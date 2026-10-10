import OAI.Probability.InvariantIsing.Gaussian.GaussianNormMoments
import OAI.Probability.InvariantIsing.Gaussian.GaussianPatternPublishedInputs

namespace OAI

/-! The actual integer Gaussian pattern counts and their aspect-ratio limits. -/
noncomputable section
open Filter
open scoped Topology
namespace InvariantIsing

lemma gaussianPatternCount_le {α : ℝ} (hα : 0 ≤ α) (N : ℕ) :
    (gaussianPatternCount α N : ℝ) ≤ α*N := by
  unfold gaussianPatternCount
  exact Nat.floor_le (mul_nonneg hα (Nat.cast_nonneg _))

lemma gaussianPatternCount_ratio_tendsto {α : ℝ} (hα : 0 ≤ α) :
    Tendsto (fun k : ℕ => (gaussianPatternCount α (k+1) : ℝ)/(k+1)) atTop (𝓝 α) := by
  have he (k : ℕ) : 0 ≤ α-(gaussianPatternCount α (k+1) : ℝ)/(k+1) ∧
      α-(gaussianPatternCount α (k+1) : ℝ)/(k+1) ≤ 1/(k+1) := by
    have hk : (0 : ℝ) < k+1 := by positivity
    have hl := gaussianPatternCount_le hα (k+1)
    have hu : α*(k+1) < (gaussianPatternCount α (k+1) : ℝ)+1 := by
      simpa only [gaussianPatternCount,Nat.cast_add,Nat.cast_one] using
        Nat.lt_floor_add_one (α*(k+1 : ℝ))
    have hr : α-(gaussianPatternCount α (k+1) : ℝ)/(k+1) =
        (α*(k+1)-(gaussianPatternCount α (k+1) : ℝ))/(k+1) := by field_simp
    rw [hr]
    constructor
    · apply div_nonneg _ hk.le
      simpa only [Nat.cast_add,Nat.cast_one] using sub_nonneg.mpr hl
    · apply div_le_div_of_nonneg_right _ hk.le
      linarith
  have ht := squeeze_zero (fun k => (he k).1) (fun k => (he k).2)
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have h := (tendsto_const_nhds (x := α)).sub ht
  simpa only [sub_zero,sub_sub_cancel] using h

lemma gaussianPatternCount_sqrt_ratio_tendsto {α : ℝ} (hα : 0 ≤ α) :
    Tendsto (fun k : ℕ => 1+Real.sqrt ((gaussianPatternCount α (k+1) : ℝ)/(k+1)))
      atTop (𝓝 (1+Real.sqrt α)) :=
  tendsto_const_nhds.add (Real.continuous_sqrt.tendsto α |>.comp (gaussianPatternCount_ratio_tendsto hα))

lemma gaussianPattern_mean_div_sqrt_le {N m : ℕ} (hN : 0 < N) :
    (∫ z, gaussianPatternSingularMax (N := N) (m := m) z
      ∂ProbabilityTheory.stdGaussian _)/Real.sqrt N ≤ 1+Real.sqrt ((m : ℝ)/N) := by
  have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hN)
  calc
    _ ≤ (Real.sqrt N+Real.sqrt m)/Real.sqrt N :=
      div_le_div_of_nonneg_right (gaussianPatternSingularMax_mean_le N m) hs.le
    _ = _ := by rw [add_div,div_self hs.ne',Real.sqrt_div (Nat.cast_nonneg m)]

lemma gaussianPattern_mean_sq_div_le {α : ℝ} (hα : 0 ≤ α) (k : ℕ) :
    (∫ z, gaussianPatternSingularMax (N := k+1) (m := gaussianPatternCount α (k+1)) z
      ∂ProbabilityTheory.stdGaussian _)^2/(k+1) ≤ 2+2*α := by
  let M := ∫ z, gaussianPatternSingularMax (N := k+1) (m := gaussianPatternCount α (k+1)) z
    ∂ProbabilityTheory.stdGaussian _
  have hM : 0 ≤ M := gaussianPatternSingularMax_mean_nonneg _ _
  have hb : M ≤ Real.sqrt (k+1 : ℝ)+Real.sqrt (gaussianPatternCount α (k+1)) := by
    simpa only [Nat.cast_add,Nat.cast_one] using
      gaussianPatternSingularMax_mean_le (k+1) (gaussianPatternCount α (k+1))
  have hs := (sq_le_sq₀ hM (by positivity : 0 ≤ Real.sqrt (k+1)+
    Real.sqrt (gaussianPatternCount α (k+1)))).2 hb
  have hN : (Real.sqrt (k+1))^2 = (k+1 : ℝ) := Real.sq_sqrt (by positivity)
  have hm : (Real.sqrt (gaussianPatternCount α (k+1)))^2 =
      (gaussianPatternCount α (k+1) : ℝ) := Real.sq_sqrt (by positivity)
  have hc := gaussianPatternCount_le hα (k+1)
  simp only [Nat.cast_add,Nat.cast_one] at hc hb
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < k+1)).mpr
  dsimp [M] at hM hs ⊢
  nlinarith [sq_nonneg (Real.sqrt (k+1)-Real.sqrt (gaussianPatternCount α (k+1)))]

end InvariantIsing

end

end OAI
