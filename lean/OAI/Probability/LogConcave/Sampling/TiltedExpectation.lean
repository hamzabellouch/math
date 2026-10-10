import Mathlib
import OAI.Probability.LogConcave.Sampling.PolynomialGrowth

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section UpperProof
namespace LogConcaveSampling
open scoped RealInnerProductSpace

lemma growth_const {d : ℕ} {E : Type*} [NormedAddCommGroup E] (c : E) :
    HasPolynomialGrowth (fun _ : Point d => c) := by
  refine ⟨‖c‖,norm_nonneg _,0,fun z => ?_⟩
  simp only [pow_zero]
  nlinarith [norm_nonneg c]

lemma tilted_partition_pos {d : ℕ} {H : Point d → ℝ} (hH : Continuous H)
    (ht : HasGaussianLowerTail H) (θ : Point d) :
    0 < tiltedIntegral H (fun _ => (1:ℝ)) θ := by
  have hi := integrable_tilted H hH continuous_const ht (growth_const (1:ℝ)) θ
  simp only [smul_eq_mul,mul_one] at hi
  simpa only [tiltedIntegral,smul_eq_mul,mul_one] using integral_exp_pos hi

def tiltedExpectation {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (H : Point d → ℝ) (h : Point d → E) (θ : Point d) : E :=
  (tiltedIntegral H (fun _ => (1:ℝ)) θ)⁻¹ • tiltedIntegral H h θ

theorem contDiff_tiltedExpectation {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Point d → ℝ} {h : Point d → E} (hH : Continuous H) (hh : Continuous h)
    (ht : HasGaussianLowerTail H) (hg : HasPolynomialGrowth h) :
    ContDiff ℝ (⊤ : ℕ∞) (tiltedExpectation H h) := by
  apply ContDiff.smul
  · exact (contDiff_tiltedIntegral H hH continuous_const ht (growth_const (1:ℝ))).inv
      (fun θ => (tilted_partition_pos hH ht θ).ne')
  · exact contDiff_tiltedIntegral H hH hh ht hg

theorem hasFDerivAt_tiltedExpectation {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Point d → ℝ} {h : Point d → E} (hH : Continuous H) (hh : Continuous h)
    (ht : HasGaussianLowerTail H) (hg : HasPolynomialGrowth h) (θ : Point d) :
    HasFDerivAt (tiltedExpectation H h)
      ((tiltedIntegral H (fun _ => (1:ℝ)) θ)⁻¹ •
        (tiltedIntegral H (tiltDerivativeIntegrand h) θ -
          (tiltedIntegral H (tiltDerivativeIntegrand (fun _ => (1:ℝ))) θ).smulRight
            (tiltedExpectation H h θ))) θ := by
  let Z := tiltedIntegral H (fun _ => (1:ℝ)) θ
  let J := tiltedIntegral H h θ
  have hZ : Z ≠ 0 := (tilted_partition_pos hH ht θ).ne'
  have hDz := hasFDerivAt_tiltedIntegral H hH continuous_const ht (growth_const (1:ℝ)) θ
  have hDj := hasFDerivAt_tiltedIntegral H hH hh ht hg θ
  have hd := ((hasDerivAt_inv hZ).comp_hasFDerivAt θ hDz).smul hDj
  convert! hd using 1
  ext v
  simp only [smul_apply,sub_apply,
    add_apply,ContinuousLinearMap.smulRight_apply,tiltedExpectation]
  dsimp [Z,J] at hZ ⊢
  rw [smul_sub,smul_smul,smul_smul]
  module

lemma Primitive.hasGaussianLowerTail {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 < 1) : HasGaussianLowerTail (primitivePotential F x r) := by
  obtain ⟨z₀,hz,_,_⟩ := hF.exists_unique_mode x hr hl
  let a := (1-(lam:ℝ)*r^2)/2
  have ha : 0 < a := by dsimp [a]; linarith
  refine ⟨a/2,by positivity,a*‖z₀‖^2-primitivePotential F x r z₀,fun z => ?_⟩
  have hb := (primitivePotential_mode_bounds hF x hr hz (z-z₀)).1
  rw [add_sub_cancel] at hb
  have hn := norm_add_le (z-z₀) z₀
  simp only [sub_add_cancel] at hn
  have hs : ‖z‖^2 ≤ 2*‖z-z₀‖^2+2*‖z₀‖^2 := by
    have hsq := pow_le_pow_left₀ (norm_nonneg z) hn 2
    nlinarith [sq_nonneg (‖z-z₀‖-‖z₀‖)]
  have hh := mul_le_mul_of_nonneg_left hs ha.le
  dsimp [a] at *
  nlinarith

lemma growth_of_lipschitz {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {h : Point d → E} {K : ℝ≥0} (hh : LipschitzWith K h) : HasPolynomialGrowth h := by
  refine ⟨(K:ℝ)+‖h 0‖,by positivity,1,fun z => ?_⟩
  have hb := hh.dist_le_mul z 0
  rw [dist_zero_right,dist_eq_norm] at hb
  have hn := norm_add_le (h z-h 0) (h 0)
  simp only [sub_add_cancel] at hn
  simp only [pow_one]
  nlinarith [mul_nonneg (norm_nonneg (h 0)) (norm_nonneg z)]

theorem Primitive.contDiff_tilted_mean {d : ℕ} {F : Point d → ℝ} {lam : ℝ≥0}
    (hF : Primitive F lam) (x : Point d) {r : ℝ} (hr : 0 ≤ r)
    (hl : (lam:ℝ)*r^2 < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (tiltedExpectation (primitivePotential F x r)
      (fun z => gradient F (x+r • z))) := by
  have hLip : LipschitzWith (lam*⟨r,hr⟩) (fun z : Point d => gradient F (x+r • z)) := by
    apply LipschitzWith.of_dist_le_mul
    intro z w
    have hh := hF.gradient_lipschitz.dist_le_mul (x+r • z) (x+r • w)
    rw [dist_add_left,dist_smul₀,Real.norm_eq_abs,abs_of_nonneg hr] at hh
    change dist (gradient F (x+r • z)) (gradient F (x+r • w)) ≤
      (lam:ℝ)*r*dist z w
    nlinarith
  exact contDiff_tiltedExpectation (hF.continuous_potential x r) hLip.continuous
    (hF.hasGaussianLowerTail x hr hl) (growth_of_lipschitz hLip)

end LogConcaveSampling

end UpperProof
end
end
end

end OAI
