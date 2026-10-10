import OAI.Probability.SLE.Mass.DiskMassMomentBound
import OAI.Probability.SLE.Stochastic.WienerCoefficientLimit

namespace OAI

/-! The exact change-of-law density is supported on the physical center
hit and bounded by its compensating exponential factor. -/

noncomputable section
open Set Filter _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace SLEExactGauge.Target

lemma levelDensity_le_centerHit
    (κ : ℝ) (hκ : 0<κ) (hκ8 : κ<8)
    (b : Driver) (U : ℝ≥0 → ℝ) (hc : Continuous U)
    (γ : ℝ≥0 → ℂ) (G F : ℝ≥0 → ℂ → ℂ)
    (hw : IsCapacityTwoWitness U γ G F)
    (hU : ∀ s : ℝ, 0 ≤ s → U s.toNNReal=driverValue b (κ*s))
    (θ : ℝ) (hθ : θ∈Ioo (0:ℝ) Real.pi) (ℓ : ℝ) (hℓ : 0≤ℓ) :
    levelDensity κ θ b ℓ ≤
      (Multipoint.diskCenterHit (fun _ : Unit => γ) (fun _ : Unit => G) θ
        (Real.exp (-(4*ℓ/κ)))).indicator
        (fun _ => Real.exp ((4*ℓ/κ)*codimension κ)/(Real.sin θ)^greenExponent κ) () := by
  let z := diskMapInv θ 0
  let u := 4*ℓ/κ
  have hz : z∈upperHalfPlane := diskMapInv_maps hθ (by simp)
  have hR : 0<2*z.im := mul_pos (by norm_num) hz
  have hs : 0<Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have hu : 0≤u := div_nonneg (mul_nonneg (by norm_num) hℓ) hκ.le
  have he1 : Real.exp (-u)≤1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu)
  have hlog : Real.log (1/Real.exp (-u))=u := by
    rw [one_div,← Real.exp_neg,neg_neg,Real.log_exp]
  rw [levelDensity_eq_stoppedGreen κ hκ b U hc γ G F hw hU θ hθ ℓ hℓ]
  change stoppedGreen κ U γ G z u/initialGreen κ z ≤ _
  by_cases hh : ()∈Multipoint.diskCenterHit (fun _ : Unit => γ) (fun _ : Unit => G) θ (Real.exp (-u))
  · rw [indicator_of_mem hh]
    have hb := Multipoint.stoppedGreen_level_bound hc hw hκ hκ8 z hz
      ((2*z.im)*Real.exp (-u)) (mul_pos hR (Real.exp_pos _))
    rw [Multipoint.common_level_log_target z hz u] at hb
    apply (div_le_div_of_nonneg_right hb (initialGreen_pos κ z hz).le).trans_eq
    have hi : initialGreen κ z=(2*z.im)^(-codimension κ)*(Real.sin θ)^greenExponent κ := by
      rw [initialGreen]
      exact congrArg (fun s : ℝ => (2*z.im)^(-codimension κ)*s^greenExponent κ)
        (disk_center_sin_arg θ)
    rw [hi,Real.mul_rpow hR.le (Real.exp_pos _).le,← Real.exp_mul,neg_mul_neg]
    field_simp [(Real.rpow_pos_of_pos hR (-codimension κ)).ne',
      (Real.rpow_pos_of_pos hs (greenExponent κ)).ne']
    congr 1
    dsimp only [u]
    ring
  · rw [indicator_of_notMem hh]
    have ht : ¬ radiusLevelTime γ G z u<∞ := by
      intro ht
      apply hh
      apply (physical_radius_hit_iff_finite_level hc hw (diskMap θ) z 1 (Real.exp (-u))
        zero_lt_one (Real.exp_pos _) he1 (initialRadius_zero hθ).symm).mpr
      rwa [hlog]
    simp only [stoppedGreen,ite_eq_right ht,zero_div,le_refl]

end SLEExactGauge.Target

end

end OAI
