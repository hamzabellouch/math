import OAI.Analysis.BackwardIntertwiners.HaarBase

namespace OAI

namespace BackwardIntertwiners
open Filter
open scoped Topology
noncomputable section

open Topology MeasureTheory Set
open scoped ENNReal

def coordinateDistance (j : ℤ) : ℤ := max (j+1) (-j)
def powerCost (n : ℕ) : ℕ := (n+1)^2/4

lemma powerCost_add_two (n : ℕ) : powerCost (n+2) = powerCost n + n+2 := by
  unfold powerCost
  have he : (n+2+1)^2 = (n+1)^2 + 4*(n+2) := by ring
  rw [he]
  omega

lemma coordinateDistance_pos (j : ℤ) : 1 ≤ coordinateDistance j := by
  unfold coordinateDistance
  omega

lemma coordinateDistance_endpoints (j : ℤ) (n : ℕ) :
    (n:ℤ)+2 ≤ coordinateDistance j + coordinateDistance (j+(n:ℤ)+1) := by
  have h₁ : -j ≤ coordinateDistance j := le_max_right _ _
  have h₂ : j+(n:ℤ)+1+1 ≤ coordinateDistance (j+(n:ℤ)+1) := le_max_left _ _
  omega

lemma sum_coordinateDistance_lower (n : ℕ) (j : ℤ) :
    (powerCost n : ℤ) ≤ ∑ r ∈ Finset.range n, coordinateDistance (j+(r:ℤ)) := by
  induction n using Nat.twoStepInduction generalizing j with
  | zero => simp [powerCost]
  | one => simpa [powerCost] using coordinateDistance_pos j
  | more n ih _ =>
    have hsum : (∑ r ∈ Finset.range (n+2), coordinateDistance (j+(r:ℤ))) =
        coordinateDistance j + (∑ r ∈ Finset.range n, coordinateDistance ((j+1)+(r:ℤ))) +
        coordinateDistance (j+(n:ℤ)+1) := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ']
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
      congr 1
      · rw [add_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro r hr
        congr 1
        ring
      · congr 1
        ring
    rw [hsum, powerCost_add_two]
    have hmid := ih (j+1)
    have hend := coordinateDistance_endpoints j n
    push_cast
    omega


def fiberReindexVector (e : ℤ ≃ ℤ) (v : Fiber) : Fiber :=
  ⟨fun j => v (e j), by
    apply memℓp_gen
    exact ((lp.memℓp v).summable (by norm_num)).comp_injective e.injective⟩

lemma fiberReindex_norm (e : ℤ ≃ ℤ) (v : Fiber) : ‖fiberReindexVector e v‖ = ‖v‖ := by
  have he : ‖fiberReindexVector e v‖^2 = ‖v‖^2 := by
    have h₁ := lp.norm_rpow_eq_tsum (by norm_num : (0:ℝ) < (2:ENNReal).toReal) (fiberReindexVector e v)
    have h₂ := lp.norm_rpow_eq_tsum (by norm_num : (0:ℝ) < (2:ENNReal).toReal) v
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at h₁ h₂
    rw [h₁, h₂]
    exact e.tsum_eq (fun j => ‖v j‖^2)
  nlinarith [norm_nonneg (fiberReindexVector e v), norm_nonneg v]


def fiberReindex (e : ℤ ≃ ℤ) : Fiber ≃ₗᵢ[ℂ] Fiber where
  toFun := fiberReindexVector e
  invFun := fiberReindexVector e.symm
  left_inv v := by ext j; exact congrArg v (e.apply_symm_apply j)
  right_inv v := by ext j; exact congrArg v (e.symm_apply_apply j)
  map_add' v z := by ext j; rfl
  map_smul' c v := by ext j; rfl
  norm_map' := fiberReindex_norm e

@[simp] lemma fiberReindex_apply (e : ℤ ≃ ℤ) (v : Fiber) (j : ℤ) :
    (fiberReindex e v) j = v (e j) := rfl

lemma fiberMultiplier_mem {a : ℤ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (ha : ∀ j, ‖a j‖ ≤ C) (v : Fiber) : Memℓp (fun j => a j*v j) 2 := by
  apply ((lp.memℓp v).const_smul (C:ℂ)).mono'
  intro j
  simp only [Pi.smul_apply, norm_smul, Complex.norm_real, Real.norm_of_nonneg hC, norm_mul]
  exact mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _)

def fiberMultiplierVector (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ j, ‖a j‖ ≤ C)
    (v : Fiber) : Fiber := ⟨fun j => a j*v j, fiberMultiplier_mem hC ha v⟩

lemma fiberMultiplierVector_bound (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ j, ‖a j‖ ≤ C)
    (v : Fiber) : ‖fiberMultiplierVector a C hC ha v‖ ≤ C*‖v‖ := by
  calc
    _ ≤ ‖(C:ℂ) • v‖ := by
      apply lp.norm_mono (by norm_num : (2:ENNReal) ≠ 0)
      intro j
      change ‖a j*v j‖ ≤ ‖(C:ℂ)*v j‖
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (ha j) (norm_nonneg _)
    _ = C*‖v‖ := by rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg hC]

def fiberMultiplier (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ j, ‖a j‖ ≤ C) :
    Fiber →L[ℂ] Fiber :=
  LinearMap.mkContinuous
    { toFun := fiberMultiplierVector a C hC ha
      map_add' := by intro v z; ext j; exact mul_add _ _ _
      map_smul' := by intro c v; ext j; exact mul_left_comm _ _ _ }
    C (fiberMultiplierVector_bound a C hC ha)

@[simp] lemma fiberMultiplier_apply (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ j, ‖a j‖ ≤ C)
    (v : Fiber) (j : ℤ) : fiberMultiplier a C hC ha v j = a j*v j := rfl

lemma fiberMultiplier_norm_le (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C) (ha : ∀ j, ‖a j‖ ≤ C) :
    ‖fiberMultiplier a C hC ha‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC (fiberMultiplierVector_bound a C hC ha)


def fiberWeightedPermutation (e : ℤ ≃ ℤ) (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ j, ‖a j‖ ≤ C) : Fiber →L[ℂ] Fiber :=
  (fiberReindex e).toLinearIsometry.toContinuousLinearMap.comp (fiberMultiplier a C hC ha)

@[simp] lemma fiberWeightedPermutation_apply (e : ℤ ≃ ℤ) (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ j, ‖a j‖ ≤ C) (v : Fiber) (j : ℤ) :
    fiberWeightedPermutation e a C hC ha v j = a (e j)*v (e j) := rfl

lemma fiberWeightedPermutation_norm_le (e : ℤ ≃ ℤ) (a : ℤ → ℂ) (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ j, ‖a j‖ ≤ C) : ‖fiberWeightedPermutation e a C hC ha‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  change ‖fiberReindex e (fiberMultiplier a C hC ha v)‖ ≤ _
  rw [(fiberReindex e).norm_map]
  exact fiberMultiplierVector_bound a C hC ha v



lemma fiberCoordinates_stronglyMeasurable {X : Type*} [MeasurableSpace X]
    (f : X → Fiber) (hf : ∀ n : ℤ, Measurable (fun x => f x n)) : StronglyMeasurable f := by
  apply stronglyMeasurable_of_tendsto (atTop : Filter (Finset ℤ))
    (f := fun s x => ∑ n ∈ s, lp.single 2 n (f x n))
  · intro s
    have h (n : ℤ) : StronglyMeasurable (fun x => (lp.single 2 n (f x n) : Fiber)) :=
      (lp.singleContinuousLinearMap ℂ (fun _ : ℤ => ℂ) 2 n).continuous.comp_stronglyMeasurable
        (hf n).stronglyMeasurable
    convert Finset.stronglyMeasurable_sum s (fun n _ => h n) using 1
    funext x
    simp only [Finset.sum_apply]
  · rw [tendsto_pi_nhds]
    intro x
    exact lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ∞) (f x)

end
end BackwardIntertwiners

end OAI
