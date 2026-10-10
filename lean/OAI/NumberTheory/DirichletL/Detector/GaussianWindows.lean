import OAI.NumberTheory.DirichletL.Detector.GaussianPartition

namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Filter
namespace SevenEighths.ProbePhysical
open CompletedGauss

lemma gaussianMellinProfile_real (y : ℝ) (hy : 0<y) :
    gaussianMellinProfile y=
      ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
        (Real.exp (-(Real.log y)^2/4):ℂ) := by
  unfold gaussianMellinProfile
  rw [←Complex.ofReal_log hy.le]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

def gaussianDyadicProfile (Z : ℝ) (j : ℕ) (y : ℝ) : ℂ :=
  gaussianAnnulus y*gaussianMellinProfile ((2:ℝ)^j*y/Z)/(Real.sqrt y:ℂ)

lemma gaussianDyadicProfile_small (Z : ℝ) (j : ℕ) (y : ℝ) (hy : y≤1/2) :
    gaussianDyadicProfile Z j y=0 := by
  simp only [gaussianDyadicProfile,gaussianAnnulus_small y hy,zero_mul,zero_div]
lemma gaussianDyadicProfile_large (Z : ℝ) (j : ℕ) (y : ℝ) (hy : 2≤y) :
    gaussianDyadicProfile Z j y=0 := by
  simp only [gaussianDyadicProfile,gaussianAnnulus_large y hy,zero_mul,zero_div]

lemma gaussianDyadicProfile_compact (Z : ℝ) (j : ℕ) : HasCompactSupport (gaussianDyadicProfile Z j) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianDyadicProfile Z j y≠0 at hy
  constructor
  · by_contra h
    exact hy (gaussianDyadicProfile_small Z j y (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hy (gaussianDyadicProfile_large Z j y (le_of_lt (lt_of_not_ge h)))

lemma gaussianDyadicProfile_contDiff (Z : ℝ) (hZ : 0<Z) (j : ℕ) :
    ContDiff ℝ ∞ (gaussianDyadicProfile Z j) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0<y
  · have he : gaussianDyadicProfile Z j =ᶠ[𝓝 y]
        (fun x : ℝ=>gaussianAnnulus x*
          (((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
            (Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4):ℂ))/(Real.sqrt x:ℂ)) := by
      filter_upwards [eventually_gt_nhds hy] with x hx
      rw [gaussianDyadicProfile,gaussianMellinProfile_real _ (div_pos (mul_pos (by positivity) hx) hZ)]
    apply ContDiffAt.congr_of_eventuallyEq _ he
    have hq : (2:ℝ)^j*y/Z≠0 := ne_of_gt (div_pos (mul_pos (by positivity) hy) hZ)
    have hs : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
    have ha := gaussianAnnulus_contDiff.contDiffAt (x:=y)
    have hl : ContDiffAt ℝ ∞ (fun x : ℝ=>Real.log ((2:ℝ)^j*x/Z)) y :=
      (show ContDiffAt ℝ ∞ (fun x : ℝ=>(2:ℝ)^j*x/Z) y by fun_prop).log hq
    have hg : ContDiffAt ℝ ∞ (fun x : ℝ=>Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4)) y :=
      ((hl.pow 2).neg.div_const 4).exp
    have hgC := Complex.ofRealCLM.contDiff.contDiffAt.comp y hg
    have hsR : ContDiffAt ℝ ∞ Real.sqrt y := Real.contDiffAt_sqrt hy.ne'
    have ht : ContDiffAt ℝ ∞ (fun x : ℝ=>gaussianAnnulus x*
        (((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
          (Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4):ℂ))) y :=
      ha.mul (contDiffAt_const.mul hgC)
    have hsc : ContDiffAt ℝ ∞ (fun x : ℝ=>(Real.sqrt x:ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y hsR
    simpa only [div_eq_mul_inv] using ht.mul (hsc.fun_inv hs)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show y<(1/2:ℝ) by linarith)] with x hx
    exact gaussianDyadicProfile_small Z j x hx.le

lemma gaussianDyadicProfile_Vstar (Z : ℝ) (j : ℕ) (y : ℝ) (hy : 0<y) :
    Vstar (gaussianDyadicProfile Z j) y=
      gaussianAnnulus y*gaussianMellinProfile ((2:ℝ)^j*y/Z) := by
  have h : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  simp only [Vstar,gaussianDyadicProfile]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
