import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.Push
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Alternating.DomCoprod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.TensorProduct.Basic

namespace OAI

open scoped TensorProduct
namespace Mahler
open AlternatingMap
variable {T : Type*} [AddCommGroup T] [Module ℝ T]

/-- A form annihilates a vector in every slot. -/
def Horizontal {ι : Type*} (a : T [⋀^ι]→ₗ[ℝ] ℂ) (V : T) : Prop :=
  ∀ (v : ι → T) (i : ι), v i = V → a v = 0

/-- A horizontal top-degree form vanishes when the contracting vector is nonzero. -/
theorem horizontal_top_eq_zero [FiniteDimensional ℝ T]
    {ι : Type*} [Fintype ι] {a : T [⋀^ι]→ₗ[ℝ] ℂ} {V : T}
    (hdim : Fintype.card ι = Module.finrank ℝ T) (hV : V ≠ 0)
    (ha : Horizontal a V) : a = 0 := by
  classical
  ext v
  by_cases hv : LinearIndependent ℝ v
  · let b := basisOfLinearIndependentOfCardEqFinrank' v hv hdim
    have hb (i : ι) : b i = v i :=
      congrFun (coe_basisOfLinearIndependentOfCardEqFinrank' v hv hdim) i
    obtain ⟨i, hi⟩ : ∃ i, b.repr V i ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hV
      apply b.repr.injective
      ext i
      simpa using hn i
    have hz := ha (Function.update v i V) i (Function.update_self ..)
    have he : V = ∑ j, b.repr V j • v j := by
      simpa only [← hb] using (b.sum_repr V).symm
    rw [he, a.map_update_sum] at hz
    have hs : (∑ j, a (Function.update v i (b.repr V j • v j))) =
        (b.repr V i) • a v := by
      rw [Finset.sum_eq_single i]
      · rw [a.map_update_smul, Function.update_eq_self]
      · intro j hj hji
        rw [a.map_update_smul, a.map_update_self _ hji.symm, smul_zero]
      · simp
    rw [hs] at hz
    exact (smul_eq_zero.mp hz).resolve_left hi
  · exact a.map_linearDependent v hv

/-- The exterior product uses the shuffle convention, with scalar
multiplication after the tensor-valued alternating product. -/
noncomputable def wedge {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (a : T [⋀^ι]→ₗ[ℝ] ℂ) (b : T [⋀^κ]→ₗ[ℝ] ℂ) : T [⋀^ι ⊕ κ]→ₗ[ℝ] ℂ :=
  (LinearMap.mul' ℝ ℂ).compAlternatingMap (a.domCoprod b)

/-- Exterior products of horizontal forms are horizontal. -/
theorem Horizontal.wedge {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    {a : T [⋀^ι]→ₗ[ℝ] ℂ} {b : T [⋀^κ]→ₗ[ℝ] ℂ} {V : T}
    (ha : Horizontal a V) (hb : Horizontal b V) : Horizontal (wedge a b) V := by
  intro v i hi
  suffices h : a.domCoprod b v = 0 by
    change (LinearMap.mul' ℝ ℂ) (a.domCoprod b v) = 0
    rw [h, _root_.map_zero]
  change (∑ σ : Equiv.Perm.ModSumCongr ι κ, AlternatingMap.domCoprod.summand a b σ) v = 0
  rw [sum_apply]
  apply Finset.sum_eq_zero
  intro σ hσ
  induction σ using Quotient.inductionOn' with
  | h σ =>
    rw [AlternatingMap.domCoprod.summand_mk'']
    simp only [_root_.smul_apply, MultilinearMap.domDomCongr_apply,
      MultilinearMap.domCoprod_apply, AlternatingMap.coe_multilinearMap]
    have hpre : v (σ (σ.symm i)) = V := by simpa using hi
    cases he : σ.symm i with
    | inl j =>
      have hz := ha (fun j => v (σ (Sum.inl j))) j (by simpa [he] using hpre)
      simp [hz]
    | inr j =>
      have hz := hb (fun j => v (σ (Sum.inr j))) j (by simpa [he] using hpre)
      simp [hz]

/-- Slot types retain the order of each two-form factor. -/
def WedgePowerSlots : ℕ → Type
  | 0 => Fin 0
  | n + 1 => Fin 2 ⊕ WedgePowerSlots n

instance wedgePowerSlotsFintype (n : ℕ) : Fintype (WedgePowerSlots n) := by
  induction n with
  | zero => exact inferInstanceAs (Fintype (Fin 0))
  | succ n ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin 2 ⊕ WedgePowerSlots n))

noncomputable instance wedgePowerSlotsDecidableEq (n : ℕ) : DecidableEq (WedgePowerSlots n) :=
  Classical.decEq _

lemma card_wedgePowerSlots (n : ℕ) : Fintype.card (WedgePowerSlots n) = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change Fintype.card (Fin 2 ⊕ WedgePowerSlots n) = _
    rw [Fintype.card_sum, Fintype.card_fin, ih]
    omega

/-- Iterated shuffle exterior power of an actual alternating two-form. -/
noncomputable def wedgePower (a : T [⋀^Fin 2]→ₗ[ℝ] ℂ) :
    (n : ℕ) → T [⋀^WedgePowerSlots n]→ₗ[ℝ] ℂ
  | 0 => AlternatingMap.constOfIsEmpty ℝ T (Fin 0) 1
  | n + 1 => wedge a (wedgePower a n)

lemma Horizontal.wedgePower {a : T [⋀^Fin 2]→ₗ[ℝ] ℂ} {V : T}
    (ha : Horizontal a V) (n : ℕ) : Horizontal (wedgePower a n) V := by
  induction n with
  | zero => intro v i; exact Fin.elim0 i
  | succ n ih => exact ha.wedge ih

/-- The form beta wedge (d alpha_t)^(n-1) vanishes in top degree.
Here k = n-1 and T is the sphere tangent space, of dimension 2k+1. -/
theorem beta_wedge_power_eq_zero [FiniteDimensional ℝ T]
    (k : ℕ) {b : T [⋀^Fin 1]→ₗ[ℝ] ℂ} {a : T [⋀^Fin 2]→ₗ[ℝ] ℂ} {V : T}
    (hdim : Module.finrank ℝ T = 2 * k + 1) (hV : V ≠ 0)
    (hb : Horizontal b V) (ha : Horizontal a V) : wedge b (wedgePower a k) = 0 := by
  apply horizontal_top_eq_zero (V := V) _ hV (hb.wedge (ha.wedgePower k))
  rw [Fintype.card_sum, Fintype.card_fin, card_wedgePowerSlots, hdim]
  omega

end Mahler

end OAI
