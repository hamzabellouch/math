import OAI.NumberTheory.CubicMoment.Estimates.MellinScaleSeries
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticCompletedSeries

namespace OAI

/-! Mellin transform in the scale of the literal completed sum. Both
the cube-product scale and the coprimality Euler factor are retained. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem metaplectic_scale_mellin {r : Eisenstein} (hr : primary r)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hc : Continuous W) {s : ℂ} (hs : 1 < s.re) :
    mellin (metaplecticCompleted r 0 W) (-s) =
      mellin W s*(metaplecticCompletionEuler r s*metaplecticGaussSeries r s) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  let A (du : PrimaryArgument × PrimaryArgument) : ℂ :=
    if IsCoprime (du.1:Eisenstein) r then (Real.sqrt (norm du.1):ℂ)*gauss (r*du.2) else 0
  let N (du : PrimaryArgument × PrimaryArgument) : ℝ := norm ((du.2:Eisenstein)*du.1^3)
  have hN (du : PrimaryArgument × PrimaryArgument) : 0 < N du :=
    norm_pos_of_ne_zero (mul_ne_zero (primary_ne_zero du.2.property)
      (pow_ne_zero _ (primary_ne_zero du.1.property)))
  have hA : Summable (fun du => ‖A du‖*(N du)^(-s.re)) := by
    convert metaplecticCompletedSeries_norm_summable hr hs using 1
    ext du
    simp only [A,N]
    split_ifs
    · have hn := hN du
      dsimp only [N] at hn
      simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hn,Complex.neg_re]
    · simp
  have he : (fun x : ℝ => metaplecticCompleted r 0 W x⁻¹) =
      (fun x => ∑' du, A du*W (N du*x)) := by
    funext x
    apply tsum_congr
    intro du
    simp only [A,N,theta_zero,mul_one,div_inv_eq_mul]
    split_ifs <;> simp
  rw [←mellin_comp_inv,he,mellin_smooth_scale_series A N hN W hW hpos hc s hA]
  congr 1
  rw [←metaplecticCompletedSeries_factor hr hs]
  unfold normDirichletSeries metaplecticCompletedSeries
  apply tsum_congr
  intro du
  simp only [A,N]
  split_ifs <;> simp

end CubicFirstMoment

end

end OAI
