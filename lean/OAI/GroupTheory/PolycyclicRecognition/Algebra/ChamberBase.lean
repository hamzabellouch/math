import OAI.GroupTheory.PolycyclicRecognition.Geometry.WeightChamberLimits
import Mathlib.Analysis.Convex.KreinMilman

namespace OAI

/-! # A compact normalized base of a pointed weight chamber -/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W I : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [Fintype I]

def chamberFunctional (α : I → W →L[ℝ] ℝ) (σ : I → Bool) : W →L[ℝ] ℝ :=
  ∑ i, orientedWeight α σ i

def chamberBase (α : I → W →L[ℝ] ℝ) (σ : I → Bool) : Set W :=
  {w | w ∈ closedWeightChamber α σ ∧ chamberFunctional α σ w = 1}

omit [Fintype I] in
theorem oriented_weights_separate (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0) :
    ∀ x : W, (∀ i, orientedWeight α σ i x = 0) → x = 0 := by
  intro x hx
  apply hsep x
  intro i
  have hi := hx i
  cases hs : σ i <;> simpa [orientedWeight, hs] using hi

theorem chamberFunctional_pos (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    {x : W} (hx : x ∈ closedWeightChamber α σ) (hx0 : x ≠ 0) :
    0 < chamberFunctional α σ x := by
  change 0 < (∑ i, orientedWeight α σ i) x
  rw [sum_apply]
  apply lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => hx i))
  intro he
  apply hx0
  apply oriented_weights_separate α σ hsep x
  have hz := Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hx i) |>.mp he.symm
  exact fun i => hz i (Finset.mem_univ i)

theorem isClosed_chamberBase (α : I → W →L[ℝ] ℝ) (σ : I → Bool) :
    IsClosed (chamberBase α σ) :=
  (isClosed_closedWeightChamber α σ).inter
    (isClosed_eq (chamberFunctional α σ).continuous continuous_const)

theorem convex_chamberBase (α : I → W →L[ℝ] ℝ) (σ : I → Bool) :
    Convex ℝ (chamberBase α σ) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    simp only [map_add, map_smul, smul_eq_mul]
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · simp only [map_add, map_smul, hx.2, hy.2, smul_eq_mul, mul_one]
    exact hab

theorem isCompact_chamberBase [FiniteDimensional ℝ W] (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0) :
    IsCompact (chamberBase α σ) := by
  let e : W →L[ℝ] (I → ℝ) := ContinuousLinearMap.pi (orientedWeight α σ)
  have hinj : Function.Injective e := by
    intro x y hxy
    apply sub_eq_zero.mp
    apply oriented_weights_separate α σ hsep
    intro i
    have hi := congrFun hxy i
    change orientedWeight α σ i x = orientedWeight α σ i y at hi
    simp only [map_sub, hi, sub_self]
  obtain ⟨K, _hK, he⟩ := e.toLinearMap.injective_iff_antilipschitz.mp hinj
  have hcube : IsCompact (Set.pi univ (fun _ : I => Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  apply Metric.isCompact_of_isClosed_isBounded (isClosed_chamberBase α σ)
  apply (he.isBounded_preimage hcube.isBounded).subset
  intro x hx i _hi
  change 0 ≤ orientedWeight α σ i x ∧ orientedWeight α σ i x ≤ 1
  refine ⟨hx.1 i, ?_⟩
  have hle := Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
  have hsum : ∑ j, orientedWeight α σ j x = 1 := by
    simpa only [chamberFunctional, sum_apply] using hx.2
  exact hle.trans_eq hsum

theorem normalize_mem_chamberBase (α : I → W →L[ℝ] ℝ) (σ : I → Bool)
    (hsep : ∀ x : W, (∀ i, α i x = 0) → x = 0)
    {x : W} (hx : x ∈ closedWeightChamber α σ) (hx0 : x ≠ 0) :
    (chamberFunctional α σ x)⁻¹ • x ∈ chamberBase α σ := by
  have hp := chamberFunctional_pos α σ hsep hx hx0
  constructor
  · intro i
    simpa only [map_smul, smul_eq_mul] using mul_nonneg (inv_nonneg.mpr hp.le) (hx i)
  · simp only [map_smul, smul_eq_mul, inv_mul_cancel₀ hp.ne']

end PolycyclicRecognition

end

end OAI
