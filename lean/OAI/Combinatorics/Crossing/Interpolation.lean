import OAI.Combinatorics.Crossing.PolynomialKernel
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Dimension.Constructions

namespace OAI

noncomputable section
namespace Zarankiewicz
open PolynomialModule
open scoped BigOperators
variable {W : Type*} [AddCommGroup W] [Module ℝ W]
variable {ι : Type*}

theorem bounded_sum (s : Finset ι) (p : ι → PolynomialModule ℝ W) (k : ℕ)
    (hp : ∀ i ∈ s, Bounded k (p i)) : Bounded k (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bounded_zero (W := W) k
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact bounded_add (hp a (Finset.mem_insert_self a s))
      (ih fun i hi => hp i (Finset.mem_insert_of_mem hi))

theorem eq_zero_of_node_roots (node : ι → ℝ) (hn : Function.Injective node)
    (s : Finset ι) (p : PolynomialModule ℝ W) (hp : Bounded s.card p)
    (he : ∀ i ∈ s, eval (node i) p = 0) : p = 0 := by
  classical
  induction s using Finset.induction_on generalizing p with
  | empty => exact (bounded_zero_iff p).mp hp
  | @insert a s ha ih =>
    have hp' : Bounded (s.card+1) p := by simpa [Finset.card_insert_of_notMem ha] using hp
    obtain ⟨q, hq, eq⟩ := exists_mulRoot_of_eval_zero (node a) s.card p hp'
      (he a (Finset.mem_insert_self a s))
    have hqe : ∀ i ∈ s, eval (node i) q = 0 := by
      intro i hi
      have h := he i (Finset.mem_insert_of_mem hi)
      rw [← eq, eval_mulRoot] at h
      have hia : node i - node a ≠ 0 := sub_ne_zero.mpr (fun e => ha (hn e ▸ hi))
      exact (smul_eq_zero.mp h).resolve_left hia
    have hq0 := ih q hq hqe
    rw [← eq, hq0]
    simp [mulRoot]

variable [Fintype ι]
variable (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)

def nodeEvaluation : constrained U node Z (Fintype.card ι) →ₗ[ℝ] (∀ i, ↥(U i ⊓ Z)) where
  toFun p i := ⟨Z.subtype (eval (node i) p.val), p.property.2 i,
    (eval (node i) p.val).property⟩
  map_add' p q := by ext i; simp
  map_smul' c p := by ext i; simp

theorem nodeEvaluation_injective (hn : Function.Injective node) :
    Function.Injective (nodeEvaluation U node Z) := by
  intro p q he
  apply Subtype.ext
  apply sub_eq_zero.mp
  apply eq_zero_of_node_roots node hn Finset.univ (p.val-q.val)
  · simpa using bounded_sub p.property.1 q.property.1
  · intro i hi
    rw [map_sub, sub_eq_zero]
    apply Subtype.ext
    exact congrArg (fun x : ↥(U i ⊓ Z) => x.val) (congrFun he i)

def vectorInterpolant (z : ∀ i, ↥(U i ⊓ Z)) : PolynomialModule ℝ Z :=
  by
    classical
    exact ∑ i, Lagrange.basis Finset.univ node i • single ℝ 0 ⟨(z i).val, (z i).property.2⟩

theorem eval_vectorInterpolant (hn : Function.Injective node) (z : ∀ i, ↥(U i ⊓ Z)) (i : ι) :
    eval (node i) (vectorInterpolant U node Z z) = ⟨(z i).val, (z i).property.2⟩ := by
  classical
  simp only [vectorInterpolant, map_sum, eval_smul, eval_single, pow_zero, one_smul]
  rw [Finset.sum_eq_single i]
  · rw [Lagrange.eval_basis_self hn.injOn (Finset.mem_univ i), one_smul]
  · intro j hj hji
    rw [Lagrange.eval_basis_of_ne hji (Finset.mem_univ i), zero_smul]
  · simp

theorem bounded_vectorInterpolant (hn : Function.Injective node) (z : ∀ i, ↥(U i ⊓ Z)) :
    Bounded (Fintype.card ι) (vectorInterpolant U node Z z) := by
  classical
  apply bounded_sum
  intro i hi n hge
  rw [smul_single_apply]
  simp only [Nat.zero_le, ite_true, Nat.sub_zero]
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt]
  · exact zero_smul _ _
  · have hc : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
    rw [Lagrange.natDegree_basis hn.injOn hi, Finset.card_univ]
    omega

theorem nodeEvaluation_surjective (hn : Function.Injective node) :
    Function.Surjective (nodeEvaluation U node Z) := by
  intro z
  have hu : ∀ i, Z.subtype (eval (node i) (vectorInterpolant U node Z z)) ∈ U i := by
    intro i
    rw [eval_vectorInterpolant U node Z hn z i]
    exact (z i).property.1
  refine ⟨⟨vectorInterpolant U node Z z, bounded_vectorInterpolant U node Z hn z, hu⟩, ?_⟩
  funext i
  apply Subtype.ext
  exact congrArg Z.subtype (eval_vectorInterpolant U node Z hn z i)

def nodeEvaluationEquiv (hn : Function.Injective node) :
    constrained U node Z (Fintype.card ι) ≃ₗ[ℝ] (∀ i, ↥(U i ⊓ Z)) :=
  LinearEquiv.ofBijective (nodeEvaluation U node Z)
    ⟨nodeEvaluation_injective U node Z hn, nodeEvaluation_surjective U node Z hn⟩

theorem finrank_constrained_zero
    {W : Type*} [AddCommGroup W] [Module ℝ W] {ι : Type*} [Fintype ι]
    (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    : Module.finrank ℝ (constrained U node Z 0) = 0 := by
  have hz : constrained U node Z 0 = ⊥ := by
    apply le_antisymm _ bot_le
    intro p hp
    exact (Submodule.mem_bot ℝ).mpr ((bounded_zero_iff p).mp hp.1)
  rw [hz]
  simp

theorem constrained_finrank_mono
    {W : Type*} [AddCommGroup W] [Module ℝ W] {ι : Type*} [Fintype ι]
    (U : ι → Submodule ℝ W) (node : ι → ℝ) (Z : Submodule ℝ W)
    [FiniteDimensional ℝ W] :
    Monotone (fun k => Module.finrank ℝ (constrained U node Z k)) := by
  intro k l hkl
  exact Submodule.finrank_mono (fun p hp => ⟨bounded_mono hp.1 hkl, hp.2⟩)

theorem sum_rankIncrement [FiniteDimensional ℝ W] (m : ℕ) :
    ∑ h ∈ Finset.range m, rankIncrement U node Z h =
      Module.finrank ℝ (constrained U node Z m) := by
  unfold rankIncrement
  rw [Finset.sum_range_tsub (constrained_finrank_mono U node Z), finrank_constrained_zero,
    Nat.sub_zero]

theorem interpolation_identity [FiniteDimensional ℝ W] (hn : Function.Injective node) :
    ∑ h ∈ Finset.range (Fintype.card ι), rankIncrement U node Z h =
      ∑ i, Module.finrank ℝ ↥(U i ⊓ Z) := by
  rw [sum_rankIncrement, (nodeEvaluationEquiv U node Z hn).finrank_eq,
    Module.finrank_pi_fintype]

end Zarankiewicz

end

end OAI
