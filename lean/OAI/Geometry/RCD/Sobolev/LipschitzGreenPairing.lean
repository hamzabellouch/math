import OAI.Geometry.RCD.Sobolev.LipschitzDirectionalIntegral
import OAI.Geometry.RCD.Harmonic.CompactDifferencePairing
import OAI.Geometry.RCD.Sobolev.InteriorSmoothTestBounds
import OAI.Geometry.RCD.Metric.EuclideanBallDensity

namespace OAI

/-! # Compact-test integration by parts for Lipschitz Euclidean functions -/

open Set Filter MeasureTheory Metric
open scoped Topology NNReal
noncomputable section
namespace RegularPointCoordinates

theorem lipschitz_green_directional {n : ℕ} {f ψ : Euclidean n → ℝ}
    {L : ℝ≥0} (hf : LipschitzWith L f) {S : ℝ} (hS : 0<S)
    (hψ : InteriorSmoothTest n S ψ) (v : Euclidean n) :
    (∫ x, fderiv ℝ f x v*ψ x) = -(∫ x, f x*fderiv ℝ ψ x v) := by
  obtain ⟨_,_,_,K,_,hK,_,_⟩ := hψ.metric_bounds hS
  let A := S+‖v‖+1
  let χ := euclideanBallDensity (0:Euclidean n) A (A+1) (by linarith)
  let φ := fun x => f x*χ x
  have hφ : Integrable φ volume :=
    (hf.continuous.mul χ.continuous).integrable_of_hasCompactSupport
      (nestedBallCutoff_hasCompactSupport (0:Euclidean n) (by linarith : A<A+1)).mul_left
  have hφeq (x : Euclidean n) (hx : ‖x‖≤A) : φ x=f x := by
    have hc : χ x=1 := nestedBallCutoff_eq_one 0 (by linarith : A<A+1)
      (by simpa only [dist_zero_left] using hx)
    simp only [φ,hc,mul_one]
  have hz (x : Euclidean n) (hx : S≤‖x‖) : ψ x=0 := by
    by_contra hn
    have hh := hψ.2.2 (subset_tsupport ψ hn)
    have hn' : ‖x‖<S := by simpa only [mem_ball,dist_zero_right] using hh
    exact (not_lt_of_ge hx) hn'
  let q : ℕ → ℝ := fun k => 1/((k:ℝ)+1)
  have hq (k : ℕ) : 0<q k := by dsimp only [q]; positivity
  have hq1 (k : ℕ) : q k≤1 := by
    dsimp only [q]
    apply (div_le_one (by positivity : (0:ℝ)<(k:ℝ)+1)).mpr
    exact le_add_of_nonneg_left (Nat.cast_nonneg k)
  have hqlim : Tendsto q atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have heq (k : ℕ) (x : Euclidean n) :
      f x*((ψ (x-q k • v)-ψ x)/q k)=
        ((ψ (x+q k • (-v))-ψ x)/q k)*φ x := by
    by_cases hx : ‖x‖≤A
    · rw [hφeq x hx,smul_neg,← sub_eq_add_neg]
      ring
    · have hxA : A<‖x‖ := lt_of_not_ge hx
      have hsx : S≤‖x‖ := by dsimp only [A] at hxA; linarith [norm_nonneg v]
      have hsy : S≤‖x-q k • v‖ := by
        have ht := norm_add_le (x-q k • v) (q k • v)
        rw [sub_add_cancel,norm_smul,Real.norm_eq_abs,abs_of_pos (hq k)] at ht
        have hb := mul_le_mul_of_nonneg_right (hq1 k) (norm_nonneg v)
        dsimp only [A] at hxA
        linarith
      rw [smul_neg,← sub_eq_add_neg,hz x hsx,hz _ hsy]
      simp
  have hzero (x : Euclidean n) : (fderiv ℝ ψ x (-v))*φ x= - (f x*fderiv ℝ ψ x v) := by
    by_cases hx : ‖x‖≤A
    · rw [hφeq x hx,map_neg]; ring
    · have hnot : x∉tsupport ψ := by
        intro hx'
        have hsx : ‖x‖<S := by simpa only [mem_ball,dist_zero_right] using hψ.2.2 hx'
        apply hx
        dsimp only [A]
        linarith [norm_nonneg v]
      rw [fderiv_of_notMem_tsupport ℝ hnot]
      simp
  have hleft := lipschitz_directional_integral_limit hf
    (hψ.1.continuous.integrable_of_hasCompactSupport hψ.2.1) v q hq hqlim
  have hright := lipschitz_directional_integral_limit hK hφ (-v) q hq hqlim
  have hright' : Tendsto (fun k => ∫ x, ((f (x+q k • v)-f x)/q k)*ψ x) atTop
      (𝓝 (-(∫ x, f x*fderiv ℝ ψ x v))) := by
    convert hright using 1
    · funext k
      rw [compact_difference_pairing hf.continuous hψ.1.continuous hψ.2.1]
      exact integral_congr_ae (Eventually.of_forall (heq k))
    · congr 1
      rw [← integral_neg]
      exact integral_congr_ae (Eventually.of_forall fun x => (hzero x).symm)
  exact tendsto_nhds_unique hleft hright'

end RegularPointCoordinates

end

end OAI
