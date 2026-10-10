import OAI.MeasureTheory.Falconer.Slicing.GaussianRieszKernel

namespace OAI

/-! # Homogeneous inverse-moment bound for every projected difference -/
namespace Falconer
open Set MeasureTheory
open scoped ENNReal
variable {d m : ℕ}

theorem gaussianRows_inverse_moment {u : ℝ} (hu : 0 < u) (hum : u < (m:ℝ))
    (z : Space d) :
    (∫⁻ A, (edist (0:Space m) (gaussianRowMap A z))^(-u) ∂gaussianRows d m) ≤
      rieszSmallBallBound m (gaussianBandConstant^m) u * (edist (0:Space d) z)^(-u) := by
  let B := rieszSmallBallBound m (gaussianBandConstant^m) u
  by_cases hz : z = 0
  · subst z
    have hB : B ≠ 0 := by
      have : 1 ≤ B := le_add_right le_rfl
      exact ne_of_gt (zero_lt_one.trans_le this)
    simp only [edist_self,ENNReal.zero_rpow_of_neg (neg_lt_zero.mpr hu)]
    rw [ENNReal.mul_top hB]
    exact le_top
  · have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    let w : Space d := ‖z‖⁻¹ • z
    have hw : ‖w‖ = 1 := by simp [w,norm_smul,hn.ne']
    have hzw : z = ‖z‖ • w := by simp [w,smul_smul,hn.ne']
    have hfactor (A : Fin m → Space d) :
        (edist (0:Space m) (gaussianRowMap A z))^(-u) =
        (edist (0:Space d) z)^(-u) * (edist (0:Space m) (gaussianRowMap A w))^(-u) := by
      have he : edist (0:Space m) (gaussianRowMap A z) =
          edist (0:Space d) z * edist (0:Space m) (gaussianRowMap A w) := by
        rw [hzw,ContinuousLinearMap.map_smul]
        simp only [edist_dist,dist_zero_left,norm_smul,Real.norm_eq_abs,abs_norm,hw,mul_one]
        rw [ENNReal.ofReal_mul (norm_nonneg _)]
      rw [he,ENNReal.mul_rpow_of_ne_top (edist_ne_top _ _) (edist_ne_top _ _)]
    calc
      _ = (edist (0:Space d) z)^(-u) *
          ∫⁻ A, (edist (0:Space m) (gaussianRowMap A w))^(-u) ∂gaussianRows d m := by
        simp_rw [hfactor]
        apply lintegral_const_mul' _ _
        exact ENNReal.rpow_ne_top_of_ne_zero (by simpa [edist_eq_zero] using hz) (edist_ne_top _ _)
      _ ≤ (edist (0:Space d) z)^(-u) * B :=
        mul_le_mul_right (gaussianRows_unit_inverse_moment hw hu hum) _
      _ = _ := mul_comm _ _

end Falconer

end OAI
