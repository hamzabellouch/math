import OAI.NumberTheory.CubicMoment.Transform.MetaplecticEulerFactor
import OAI.NumberTheory.CubicMoment.Transform.MetaplecticVoronoi

namespace OAI

/-! The Dirichlet series of the literal cubic completion. Absolute
convergence justifies its factorization into the Gauss series and the
coprimality Euler factor, with the exact shift `3*s-1/2`. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

def metaplecticCompletedSeries (r : Eisenstein) (s : ℂ) : ℂ :=
  ∑' du : PrimaryArgument × PrimaryArgument,
    if IsCoprime (du.1:Eisenstein) r then
      (Real.sqrt (norm du.1):ℂ)*gauss (r*du.2)*
        (norm ((du.2:Eisenstein)*du.1^3):ℂ)^(-s)
    else 0

lemma completed_series_weight (d u : PrimaryArgument) (s : ℂ) :
    (Real.sqrt (norm d):ℂ)*(norm ((u:Eisenstein)*d^3):ℂ)^(-s) =
      (norm d:ℂ)^(-(3*s-1/2))*(norm u:ℂ)^(-s) := by
  have hd : 0 < norm (d:Eisenstein) := norm_pos_of_ne_zero (primary_ne_zero d.property)
  have hu : 0 < norm (u:Eisenstein) := norm_pos_of_ne_zero (primary_ne_zero u.property)
  have hp : ((norm d^3:ℝ):ℂ)^(-s) = (norm d:ℂ)^(3*(-s)) := by
    push_cast
    exact (Complex.cpow_ofNat_mul' (n := 3) (by simpa only [Complex.arg_ofReal_of_nonneg hd.le,mul_zero] using neg_lt_zero.mpr Real.pi_pos)
      (by simp [Complex.arg_ofReal_of_nonneg hd.le,Real.pi_pos.le]) (-s)).symm
  have hsqrt : (Real.sqrt (norm d):ℂ) = (norm d:ℂ)^(1/2:ℂ) := by
    rw [Real.sqrt_eq_rpow,Complex.ofReal_cpow hd.le]
    norm_num
  rw [norm_mul_eq,eisenstein_norm_pow,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hu.le (pow_nonneg hd.le 3),hp,hsqrt]
  calc
    _ = ((norm d:ℂ)^(1/2:ℂ)*(norm d:ℂ)^(3*(-s)))*(norm u:ℂ)^(-s) := by ring
    _ = _ := by
      rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hd.ne')]
      congr 2
      ring

lemma primaryCoprimeZeta_norm_summable (r : Eisenstein) {s : ℂ} (hs : 1 < s.re) :
    Summable (fun d : PrimaryArgument =>
      ‖if IsCoprime r (d:Eisenstein) then (norm d:ℂ)^(-s) else 0‖) := by
  apply (primary_norm_rpow_summable hs).of_nonneg_of_le
    (fun _ => _root_.norm_nonneg _)
  intro d
  split_ifs
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos
      (norm_pos_of_ne_zero (primary_ne_zero d.property)),Complex.neg_re]
  · simpa using Real.rpow_nonneg (norm_nonneg (d:Eisenstein)) (-s.re)

lemma metaplecticGaussSeries_norm_summable {r : Eisenstein} (hr : primary r)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun u : PrimaryArgument => ‖gauss (r*u)*(norm u:ℂ)^(-s)‖) := by
  have he (u : PrimaryArgument) : ‖gauss (r*u)*(norm u:ℂ)^(-s)‖ =
      ‖gauss (r*u)‖*norm u^(-s.re) := by
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos
      (norm_pos_of_ne_zero (primary_ne_zero u.property)),Complex.neg_re]
  simpa only [he] using gauss_series_absolutely_summable hr hs

lemma metaplecticCompletedSeries_factor {r : Eisenstein} (hr : primary r)
    {s : ℂ} (hs : 1 < s.re) :
    metaplecticCompletedSeries r s =
      metaplecticCompletionEuler r s*metaplecticGaussSeries r s := by
  have h3 : 1 < (3*s-(1/2:ℂ)).re := by simp; linarith
  have hg := metaplecticGaussSeries_norm_summable hr hs
  rw [metaplecticCompletionEuler,primaryCoprimeZeta,metaplecticGaussSeries,
    normDirichletSeries,tsum_mul_tsum_of_summable_norm
      (primaryCoprimeZeta_norm_summable r h3) hg,metaplecticCompletedSeries]
  apply tsum_congr
  intro du
  by_cases hc : IsCoprime (du.1:Eisenstein) r
  · simp only [hc,hc.symm,ite_true]
    calc
      _ = gauss (r*du.2)*((Real.sqrt (norm du.1):ℂ)*
          (norm ((du.2:Eisenstein)*du.1^3):ℂ)^(-s)) := by ring
      _ = _ := by rw [completed_series_weight]; ring
  · simp only [hc,show ¬IsCoprime r (du.1:Eisenstein) from fun h => hc h.symm,
      ite_false,zero_mul]

lemma metaplecticCompletedSeries_norm_summable {r : Eisenstein} (hr : primary r)
    {s : ℂ} (hs : 1 < s.re) :
    Summable (fun du : PrimaryArgument × PrimaryArgument =>
      ‖if IsCoprime (du.1:Eisenstein) r then
        (Real.sqrt (norm du.1):ℂ)*gauss (r*du.2)*
          (norm ((du.2:Eisenstein)*du.1^3):ℂ)^(-s) else 0‖) := by
  have h3 : 1 < (3*s-(1/2:ℂ)).re := by simp; linarith
  have hd := primaryCoprimeZeta_norm_summable r h3
  have hu := metaplecticGaussSeries_norm_summable hr hs
  have hp := hd.mul_of_nonneg hu (fun _ => _root_.norm_nonneg _)
    (fun _ => _root_.norm_nonneg _)
  convert hp using 1
  ext du
  by_cases hc : IsCoprime (du.1:Eisenstein) r
  · simp only [hc,hc.symm,ite_true,←norm_mul]
    congr 1
    calc
      _ = gauss (r*du.2)*((Real.sqrt (norm du.1):ℂ)*
          (norm ((du.2:Eisenstein)*du.1^3):ℂ)^(-s)) := by ring
      _ = _ := by rw [completed_series_weight]; ring
  · simp only [hc,show ¬IsCoprime r (du.1:Eisenstein) from fun h => hc h.symm,
      ite_false,norm_zero,zero_mul]

lemma metaplectic_completed_mellin {r : Eisenstein} (hr : primary r)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) {σ X : ℝ} (hσ : 1 < σ) (hX : 0 < X) :
    metaplecticCompleted r 0 W X = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫ t : ℝ, mellin W ((σ:ℂ)+(t:ℂ)*Complex.I)*
        (X:ℂ)^((σ:ℂ)+(t:ℂ)*Complex.I)*
        (metaplecticCompletionEuler r ((σ:ℂ)+(t:ℂ)*Complex.I)*
          metaplecticGaussSeries r ((σ:ℂ)+(t:ℂ)*Complex.I)) := by
  let : Countable Eisenstein := coordinatesEquiv.symm.injective.countable
  let A (du : PrimaryArgument × PrimaryArgument) : ℂ :=
    if IsCoprime (du.1:Eisenstein) r then (Real.sqrt (norm du.1):ℂ)*gauss (r*du.2) else 0
  let N (du : PrimaryArgument × PrimaryArgument) : ℝ := norm ((du.2:Eisenstein)*du.1^3)
  have hN (du : PrimaryArgument × PrimaryArgument) : 0 < N du :=
    norm_pos_of_ne_zero (mul_ne_zero (primary_ne_zero du.2.property)
      (pow_ne_zero _ (primary_ne_zero du.1.property)))
  have hA : Summable (fun du => ‖A du‖*(N du)^(-σ)) := by
    convert metaplecticCompletedSeries_norm_summable hr (s := (σ:ℂ)) (by simpa using hσ) using 1
    ext du
    simp only [A,N]
    split_ifs
    · have hn := hN du
      dsimp only [N] at hn
      simp only [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hn,Complex.neg_re,Complex.ofReal_re]
    · simp
  have hleft : (∑' du, A du*W (N du/X)) = metaplecticCompleted r 0 W X := by
    apply tsum_congr
    intro du
    simp only [A,N,theta_zero,mul_one]
    split_ifs <;> simp
  rw [←hleft,smooth_mellin_series A N hN W hW hpos hsm σ hA hX]
  congr 1
  apply integral_congr_ae
  filter_upwards with t
  congr 1
  rw [←metaplecticCompletedSeries_factor hr (by simpa using hσ)]
  unfold normDirichletSeries metaplecticCompletedSeries
  apply tsum_congr
  intro du
  simp only [A,N]
  split_ifs <;> simp

end CubicFirstMoment

end

end OAI
