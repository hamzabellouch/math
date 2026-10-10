import OAI.NumberTheory.CubicMoment.Theta.CubicThetaHighCuspDerivativeBound
import Mathlib.Analysis.Calculus.SmoothSeries

namespace OAI

/-! Differentiate the exact high-cusp expansion of the arithmetic
remainder. The derivative bound is obtained from a summable majorant. -/
noncomputable section
open Set Filter
open scoped MatrixGroups Topology
namespace CubicFirstMoment

lemma cubicThetaHighCuspRow_sum (δ : SL(2,Eisenstein)) {p : ℂ × ℝ}
    (hp : 2≤p.2) {s : ℂ} (hs : 2<s.re) :
    cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaFullComplex δ) p) s=
      ∑' r, cubicThetaHighCuspRow δ r p s := by
  rw [cubicThetaArithmeticRemainder_eq_sum
    (cubicThetaMobius_height_pos (cubicThetaFullComplex δ) (by linarith : 0<p.2)) hs]
  exact tsum_congr (fun r => (cubicThetaHighCuspRow_eq δ r hp s).symm)

lemma cubicThetaHighCuspRow_sum_summable (δ : SL(2,Eisenstein)) {p : ℂ × ℝ}
    (hp : 2≤p.2) {s : ℂ} (hs : 2<s.re) :
    Summable (fun r => cubicThetaHighCuspRow δ r p s) :=
  (cubicThetaRemainderRow_summable
    (cubicThetaMobius_height_pos (cubicThetaFullComplex δ) (by linarith : 0<p.2)) hs).congr
    (fun r => (cubicThetaHighCuspRow_eq δ r hp s).symm)

lemma cubicThetaHighCusp_fderiv_eq (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3<s.re)
    {p : ℂ × ℝ} (hp : 2<p.2) :
    Summable (fun r => fderiv ℝ (fun q => cubicThetaHighCuspRow δ r q s) p) ∧
      fderiv ℝ (fun q => cubicThetaArithmeticRemainder
        (cubicThetaMobius (cubicThetaFullComplex δ) q) s) p=
        ∑' r, fderiv ℝ (fun q => cubicThetaHighCuspRow δ r q s) p := by
  obtain ⟨ρ,hρ,u,hu,hb⟩ := cubicThetaHighCuspRow_local_fderiv_bound δ hs hp
  have hpB : p∈Metric.ball p ρ := Metric.mem_ball_self hρ
  have hD : ∀ r q, q∈Metric.ball p ρ →
      HasFDerivAt (fun y => cubicThetaHighCuspRow δ r y s)
        (fderiv ℝ (fun y => cubicThetaHighCuspRow δ r y s) q) q := by
    intro r q hq
    exact ((cubicThetaHighCuspRow_contDiffAt δ r s
      (lt_trans (by norm_num : (0:ℝ)<2) (hb r q hq).1)).differentiableAt (by simp)).hasFDerivAt
  have hdf := hasFDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball (convex_ball p ρ).isPreconnected
    hD (fun r q hq => (hb r q hq).2) hpB
    (cubicThetaHighCuspRow_sum_summable δ hp.le (by linarith)) hpB
  have he : (fun q => cubicThetaArithmeticRemainder (cubicThetaMobius (cubicThetaFullComplex δ) q) s)=ᶠ[𝓝 p]
      (fun q => ∑' r, cubicThetaHighCuspRow δ r q s) := by
    filter_upwards [Metric.ball_mem_nhds p hρ] with q hq
    exact cubicThetaHighCuspRow_sum δ (hb cubicThetaZeroRow q hq).1.le (by linarith)
  exact ⟨hu.of_norm_bounded (fun r => (hb r p hpB).2),(hdf.congr_of_eventuallyEq he).fderiv⟩

theorem cubicThetaArithmeticCusp_fderiv_bound (δ : SL(2,Eisenstein)) {s : ℂ} (hs : 3<s.re)
    {p : ℂ × ℝ} (hp : 2<p.2) {R : ℝ} (hR : Complex.normSq p.1≤R) :
    ‖fderiv ℝ (fun q => cubicThetaArithmeticRemainder
        (cubicThetaMobius (cubicThetaFullComplex δ) q) s) p‖≤
      (6*(3+2*R)^2*cubicThetaFirstJetConstant s*p.2^(3-s.re))*cubicThetaCuspLatticeMass s := by
  obtain ⟨hds,he⟩ := cubicThetaHighCusp_fderiv_eq δ hs hp
  rw [he]
  let K := 6*(3+2*R)^2*cubicThetaFirstJetConstant s*p.2^(3-s.re)
  have hK : 0≤K := by
    apply mul_nonneg
    · exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (cubicThetaJetConstants_nonneg s).1
    · exact Real.rpow_nonneg (by linarith) _
  have hW := cubicThetaCuspLatticeWeight_summable δ hs
  calc
    _ ≤ ∑' r, ‖fderiv ℝ (fun q => cubicThetaHighCuspRow δ r q s) p‖ := norm_tsum_le_tsum_norm hds.norm
    _ ≤ ∑' r, K*cubicThetaCuspLatticeWeight δ s r :=
      Summable.tsum_le_tsum (fun r => cubicThetaHighCuspRow_fderiv_lattice_bound δ r hp.le hR (by linarith))
        hds.norm (hW.mul_left K)
    _ = K*(∑' r, cubicThetaCuspLatticeWeight δ s r) := tsum_mul_left
    _ ≤ K*cubicThetaCuspLatticeMass s :=
      mul_le_mul_of_nonneg_left (cubicThetaCuspLatticeWeight_tsum_le δ hs) hK

end CubicFirstMoment

end

end OAI
