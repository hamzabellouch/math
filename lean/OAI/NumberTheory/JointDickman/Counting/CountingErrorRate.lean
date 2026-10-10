import OAI.NumberTheory.JointDickman.Amplification.SignedProductGcd
import OAI.NumberTheory.JointDickman.Counting.CountingCandidateComparison
import OAI.NumberTheory.JointDickman.Amplification.AmplificationPositiveMass

namespace OAI

/-! # A vanishing error profile for the counting candidate comparison -/
namespace JointDickman
open Filter
open scoped Topology

noncomputable def countingErrorRate (R Kr Kc Kp η : ℝ)
    (er ec ep ef : ℕ → ℝ) (B : ℕ) : ℝ :=
  R*(Kr*(er B+1)*|ep B|+
    (amplificationMultiplier B : ℝ)*(((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ)))+
    Kc*ec B+|ef B|+(Kr*Kp/η)*er B)

theorem countingErrorRate_nonneg {R Kr Kc Kp η : ℝ}
    (hR : 0 ≤ R) (hKr : 0 ≤ Kr) (hKc : 0 ≤ Kc) (hKp : 0 ≤ Kp) (hη : 0 ≤ η)
    {er ec ep ef : ℕ → ℝ} (her : ∀ B, 0 ≤ er B) (hec : ∀ B, 0 ≤ ec B) (B : ℕ) :
    0 ≤ countingErrorRate R Kr Kc Kp η er ec ep ef B := by
  have hg : 0 ≤ (amplificationMultiplier B : ℝ)*
      (((B : ℝ)*coefficientScale B)/(4*(auxiliaryCutoff B : ℝ))) :=
    mul_nonneg (Nat.cast_nonneg _) (div_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (coefficientScale_nonneg _)) (by positivity))
  unfold countingErrorRate
  exact mul_nonneg hR (add_nonneg (add_nonneg (add_nonneg
    (add_nonneg (mul_nonneg (mul_nonneg hKr (by linarith [her B])) (abs_nonneg _)) hg)
    (mul_nonneg hKc (hec B))) (abs_nonneg _))
    (mul_nonneg (div_nonneg (mul_nonneg hKr hKp) hη) (her B)))

theorem countingErrorRate_tendsto (R Kr Kc Kp η : ℝ)
    {er ec ep ef : ℕ → ℝ} (her : Tendsto er atTop (𝓝 0))
    (hec : Tendsto ec atTop (𝓝 0)) (hep : Tendsto ep atTop (𝓝 0))
    (hef : Tendsto ef atTop (𝓝 0)) :
    Tendsto (countingErrorRate R Kr Kc Kp η er ec ep ef) atTop (𝓝 0) := by
  unfold countingErrorRate
  have hp := ((her.add_const 1).const_mul Kr).mul hep.abs
  have h := ((((hp.add amplification_gcd_rate_tendsto).add (hec.const_mul Kc)).add hef.abs).add
    (her.const_mul (Kr*Kp/η))).const_mul R
  simpa only [zero_add,add_zero,zero_mul,mul_zero,abs_zero] using h

theorem countingErrorProfile_bound {R Kr Kc Kp η er ec ep ef g δ q s : ℝ}
    (hR : 0 ≤ R) (hKr : 0 ≤ Kr) (her : 0 ≤ er) (hep : 0 ≤ ep)
    (hef : 0 ≤ ef) (hg : 0 ≤ g) (hq : q ≤ 1) (hs : 1 ≤ s) :
    R*(Kr*(er+q)*(ep+(Kp/η)*s)+g+Kc*s*(ec+q)+ef+(δ/η)*s) ≤
      (R*(Kr*(er+1)*ep+g+Kc*ec+ef+(Kr*Kp/η)*er)+
        R*(Kr*Kp/η+Kc)*q+R*δ/η)*s := by
  have hpos : 0 ≤ R*(Kr*ep*(er*(s-1)+(s-q))+(g+ef)*(s-1)) := by
    apply mul_nonneg hR
    exact add_nonneg
      (mul_nonneg (mul_nonneg hKr hep)
        (add_nonneg (mul_nonneg her (by linarith)) (by linarith)))
      (mul_nonneg (add_nonneg hg hef) (by linarith))
  have he : (R*(Kr*(er+1)*ep+g+Kc*ec+ef+(Kr*Kp/η)*er)+
        R*(Kr*Kp/η+Kc)*q+R*δ/η)*s-
      R*(Kr*(er+q)*(ep+(Kp/η)*s)+g+Kc*s*(ec+q)+ef+(δ/η)*s) =
      R*(Kr*ep*(er*(s-1)+(s-q))+(g+ef)*(s-1)) := by ring
  linarith only [hpos,he]

end JointDickman

end OAI
