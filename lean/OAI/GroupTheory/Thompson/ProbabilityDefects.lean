import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic.Ring

namespace OAI

/-!
# Finite probabilities and their simultaneous translation defects

One ℓ¹ space on `S × G` carries the sum of all translation defects.  In
particular its norm is the exact finite sum, without a factor depending on
`S.card`.  This is the finite-probability input to the separation argument.
-/

noncomputable section

open scoped BigOperators Classical

universe uG uι

namespace ThompsonNonamenability

variable {G : Type uG}

/-- The total mass of a finitely supported real function. -/
def mass : (G →₀ ℝ) →ₗ[ℝ] ℝ :=
  Finsupp.linearCombination ℝ (fun _ : G => (1 : ℝ))

@[simp]
theorem mass_apply (p : G →₀ ℝ) : mass p = ∑ g ∈ p.support, p g := by
  simp [mass, Finsupp.linearCombination_apply, Finsupp.sum]

@[simp]
theorem mass_single (g : G) (a : ℝ) : mass (Finsupp.single g a) = a := by
  simp [mass]

/-- Nonnegative finite weights with total mass one. -/
def IsProbabilityWeights (p : G →₀ ℝ) : Prop :=
  (∀ g, 0 ≤ p g) ∧ mass p = 1

theorem isProbabilityWeights_single (g : G) :
    IsProbabilityWeights (Finsupp.single g (1 : ℝ)) := by
  refine ⟨?_, mass_single g 1⟩
  intro x
  simp only [Finsupp.single_apply]
  split_ifs
  · exact zero_le_one
  · exact le_rfl

theorem convex_probabilityWeights :
    Convex ℝ {p : G →₀ ℝ | IsProbabilityWeights p} := by
  intro p hp q hq a b ha hb hab
  refine ⟨?_, ?_⟩
  · intro g
    change 0 ≤ a * p g + b * q g
    exact add_nonneg (mul_nonneg ha (hp.1 g)) (mul_nonneg hb (hq.1 g))
  · rw [map_add, map_smul, map_smul, hp.2, hq.2]
    simpa using hab

/-- The simultaneous defects use the ℓ¹ norm on the product index set. -/
abbrev DefectSpace (S : Finset G) := lp (fun _ : ({h // h ∈ S} × G) => ℝ) 1

variable [Group G]

/-- Translation defect of the point probability at `g`. -/
def diracDefect (S : Finset G) (g : G) : DefectSpace S :=
  ∑ h : S, (lp.single 1 (h, h.val * g) (1 : ℝ) - lp.single 1 (h, g) (1 : ℝ))

/-- The linear extension of the point-probability defects. -/
def defectMap (S : Finset G) : (G →₀ ℝ) →ₗ[ℝ] DefectSpace S :=
  Finsupp.linearCombination ℝ (diracDefect S)

@[simp]
theorem defectMap_single (S : Finset G) (g : G) (a : ℝ) :
    defectMap S (Finsupp.single g a) = a • diracDefect S g := by
  simp [defectMap]

private theorem single_apply_real {ι : Type uι} [DecidableEq ι] (i j : ι) (a : ℝ) :
    (lp.single 1 i a : lp (fun _ : ι => ℝ) 1) j = if i = j then a else 0 := by
  by_cases hij : i = j
  · subst j
    simp
  · rw [lp.single_apply_ne (E := fun _ : ι => ℝ) 1 i a (Ne.symm hij), ite_eq_right hij]

/-- Coordinate computation for a single point probability. -/
theorem diracDefect_apply (S : Finset G) (g : G) (h : S) (x : G) :
    diracDefect S g (h, x) =
      (Finsupp.single g (1 : ℝ)) (h.val⁻¹ * x) - (Finsupp.single g (1 : ℝ)) x := by
  have hmul : h.val * g = x ↔ g = h.val⁻¹ * x := by
    constructor
    · intro heq
      simpa [mul_assoc] using congrArg (fun y => h.val⁻¹ * y) heq
    · intro heq
      simpa [mul_assoc] using congrArg (fun y => h.val * y) heq
  unfold diracDefect
  rw [lp.coeFn_sum, Finset.sum_apply, Finset.sum_eq_single h]
  · simp only [lp.coeFn_sub, Pi.sub_apply]
    rw [single_apply_real, single_apply_real]
    simp only [Prod.mk.injEq, true_and, hmul,
      Finsupp.single_apply]
  · intro k _ hkh
    simp [Prod.mk.injEq, hkh]
  · simp

/-- The product coordinate is exactly the left translation difference. -/
theorem defectMap_apply (S : Finset G) (p : G →₀ ℝ) (h : S) (x : G) :
    defectMap S p (h, x) = p (h.val⁻¹ * x) - p x := by
  induction p using Finsupp.induction_linear with
  | zero => simp
  | add p q hp hq =>
      simp only [map_add, lp.coeFn_add, Pi.add_apply, Finsupp.add_apply, hp, hq]
      ring
  | single g a =>
      rw [defectMap_single, lp.coeFn_smul, Pi.smul_apply, diracDefect_apply]
      simp only [smul_eq_mul, Finsupp.single_apply, mul_sub, mul_ite, mul_one, mul_zero]

/-- Each translation difference vanishes outside its exact finite support bound. -/
theorem translation_difference_eq_zero_of_not_mem (p : G →₀ ℝ) (h x : G)
    (hx : x ∉ p.support ∪ p.support.image (fun g => h * g)) :
    p (h⁻¹ * x) - p x = 0 := by
  have hx₀ : x ∉ p.support := fun hmem => hx (Finset.mem_union_left _ hmem)
  have hx₁ : h⁻¹ * x ∉ p.support := by
    intro hmem
    apply hx
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨h⁻¹ * x, hmem, by simp⟩
  simp [Finsupp.notMem_support_iff.mp hx₀, Finsupp.notMem_support_iff.mp hx₁]

/-- Exact ℓ¹ norm of the simultaneous defect, with no `S.card` loss. -/
theorem norm_defectMap (S : Finset G) (p : G →₀ ℝ) :
    ‖defectMap S p‖ =
      ∑ h ∈ S, ∑ x ∈ p.support ∪ p.support.image (fun g => h * g),
        |p (h⁻¹ * x) - p x| := by
  have hsum : HasSum (fun z : S × G => ‖defectMap S p z‖) ‖defectMap S p‖ := by
    simpa only [ENNReal.toReal_one, Real.rpow_one] using
      (lp.hasSum_norm (p := 1) (by simp) (defectMap S p))
  calc
    ‖defectMap S p‖ = ∑' z : S × G, ‖defectMap S p z‖ := hsum.tsum_eq.symm
    _ = ∑ h : S, ∑' x : G, ‖defectMap S p (h, x)‖ := by
      rw [hsum.summable.tsum_prod, tsum_fintype]
    _ = ∑ h : S, ∑ x ∈ p.support ∪ p.support.image (fun g => h.val * g),
        |p (h.val⁻¹ * x) - p x| := by
      apply Finset.sum_congr rfl
      intro h _
      simp only [defectMap_apply, Real.norm_eq_abs]
      apply tsum_eq_sum
      intro x hx
      rw [translation_difference_eq_zero_of_not_mem p h.val x hx, abs_zero]
    _ = ∑ h ∈ S, ∑ x ∈ p.support ∪ p.support.image (fun g => h * g),
        |p (h⁻¹ * x) - p x| :=
      Finset.sum_coe_sort S (fun h : G =>
        ∑ x ∈ p.support ∪ p.support.image (fun g => h * g),
          |p (h⁻¹ * x) - p x|)

/-- The actual image of finite nonnegative probabilities under the defect map. -/
def defectSet (S : Finset G) : Set (DefectSpace S) :=
  defectMap S '' {p : G →₀ ℝ | IsProbabilityWeights p}

theorem convex_defectSet (S : Finset G) : Convex ℝ (defectSet S) :=
  convex_probabilityWeights.linear_image (defectMap S)

theorem diracDefect_mem_defectSet (S : Finset G) (g : G) :
    diracDefect S g ∈ defectSet S := by
  refine ⟨Finsupp.single g 1, isProbabilityWeights_single g, ?_⟩
  simp

theorem defectSet_nonempty (S : Finset G) : (defectSet S).Nonempty :=
  ⟨diracDefect S 1, diracDefect_mem_defectSet S 1⟩

end ThompsonNonamenability

end

end OAI
