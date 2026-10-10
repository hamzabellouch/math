import OAI.MeasureTheory.Falconer.Estimates.RegularizationProperties
import OAI.MeasureTheory.Falconer.Incidence.RadialBlockDepths
import OAI.MeasureTheory.Falconer.Recursion.ProfileTelescoping

namespace OAI

/-! # Quantitative telescoping for the constructed regularization profile -/

namespace Falconer.Regularization
open MeasureTheory
open scoped ENNReal BigOperators
variable {d : ℕ}

theorem sourceProfile_depth_upper (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d)
    {a : ℕ} (ha : a ≤ N) : sourceProfile Q μ N B p a ≤ (d:ℝ)*(a:ℝ)/(N:ℝ) := by
  have hh := regularizedProfile_increment hN
    (show regularizationLeaves Q μ N ⊆ cubePaths d N from Finset.filter_subset _ _)
    (regularizationLabel Q μ N B) hB p (u := 0) (v := (a:ℝ))
    le_rfl (Nat.cast_nonneg _) (Nat.cast_le.mpr ha)
  simpa only [sourceProfile,regularizedProfile_zero,sub_zero] using hh.2

theorem radial_profile_product_bound (Q : DyadicCube d) (μ : Measure (Space d))
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) (p : CellPath d)
    (J : ℕ) {e f β s loss ℓ : ℝ} (hβ : 0 ≤ β)
    (hfinal : s-loss ≤ sourceProfile Q μ N B p N)
    (hgap : (J:ℝ)*(e+f)-β*(s-loss-
      (d:ℝ)*(2/((J:ℝ)+2)+(J:ℝ)/(N:ℝ))) ≤ -ℓ) :
    (∏ j ∈ Finset.range J,
      (ENNReal.ofReal (((2:ℝ)^N)^(-e)))⁻¹ *
        ENNReal.ofReal (((2:ℝ)^N)^(f-β*(
          sourceProfile Q μ N B p (radialBlockDepth N J (j+1))-
            sourceProfile Q μ N B p (radialBlockDepth N J j))))) ≤
      ENNReal.ofReal (((2:ℝ)^N)^(-ℓ)) := by
  let m := fun j => sourceProfile Q μ N B p (radialBlockDepth N J j)
  apply density_profile_product_bound (one_le_pow₀ (by norm_num)) m hβ J
    (s := s-loss) (t := (d:ℝ)*(2/((J:ℝ)+2)+(J:ℝ)/(N:ℝ)))
  · simpa only [m,radialBlockDepth_final] using hfinal
  · have hh := sourceProfile_depth_upper Q μ hN hB p (radialBlockDepth_le N J (Nat.zero_le _))
    have hn := radialBlockDepth_initial_upper hN J
    exact hh.trans (by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hn (Nat.cast_nonneg _))
  · exact hgap

end Falconer.Regularization

end OAI
