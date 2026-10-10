import OAI.NumberTheory.CubicMoment.Theta.CubicThetaSpatialDerivativeBound
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCuspRowTransport

namespace OAI

/-! Primitive row powers in every cusp obey the same coordinate and
joint derivative bounds as the original Eisenstein rows. -/
noncomputable section
open scoped ContDiff
namespace CubicFirstMoment

def cubicThetaPrimitivePower (r : CubicThetaPrimitiveRow) (p : ℂ × ℝ) (s : ℂ) : ℂ :=
  (r.height p:ℂ)^s

lemma cubicThetaPrimitivePower_contDiffAt (r : CubicThetaPrimitiveRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ContDiffAt ℝ ∞ (fun q => cubicThetaPrimitivePower r q s) p := by
  obtain ⟨g,rfl⟩ := cubicThetaPrimitiveRow_surjective r
  have hh : ContDiffAt ℝ ∞ (fun q => (cubicThetaPrimitiveRow g).height q) p := by
    simp only [cubicThetaPrimitiveRow_height]
    exact contDiffAt_snd.comp p (cubicThetaMobius_contDiffAt _ hp)
  exact (cubicThetaHeightPower_analytic s ((cubicThetaPrimitiveRow g).height_pos hp)).contDiffAt.comp p hh

lemma cubicThetaPrimitivePower_cartesian (r : CubicThetaPrimitiveRow) (hc : r.c≠0)
    (s : ℂ) (x y : ℝ) {v : ℝ} (hv : 0<v) :
    cubicThetaPrimitivePower r (cubicThetaCartesianPoint x y v) s=
      (norm r.c:ℂ)^(-s)*cubicThetaCartesianKernel s
        (x+((r.d:ℂ)/(r.c:ℂ)).re) (y+((r.d:ℂ)/(r.c:ℂ)).im) v := by
  unfold cubicThetaPrimitivePower CubicThetaPrimitiveRow.height CubicThetaPrimitiveRow.denominator
  rw [cubicThetaRowRadius_complex_power hc (p:=cubicThetaCartesianPoint x y v) hv,
    cubicThetaRowRadius_cartesian]
  rw [show (cubicThetaCartesianPoint x y v).2=v from rfl,cubicTheta_row_power hv hc]
  unfold cubicThetaCartesianKernel
  ring

lemma cubicThetaPrimitivePower_jetBound (r : CubicThetaPrimitiveRow) (s : ℂ)
    (x y : ℝ) {v : ℝ} (hv : 0<v) :
    CubicThetaCoordinateJetBound
      (fun a b t => cubicThetaPrimitivePower r (cubicThetaCartesianPoint a b t) s) s x y v := by
  by_cases hc : r.c=0
  · have he : (fun a b t => cubicThetaPrimitivePower r (cubicThetaCartesianPoint a b t) s)=
        (fun (_ _ t : ℝ) => (t:ℂ)^s) := by
      funext a b t
      simp only [cubicThetaPrimitivePower,cubicThetaCuspRow_height_zero_c hc,cubicThetaCartesianPoint]
    rw [he]
    exact cubicThetaHeightPower_jetBound s x y hv
  · exact cubicThetaCoordinateJetBound_congr
      (fun a b t ht => cubicThetaPrimitivePower_cartesian r hc s a b ht) hv
      (cubicThetaCoordinateJetBound_translate ((norm r.c:ℂ)^(-s))
        ((r.d:ℂ)/(r.c:ℂ)).re ((r.d:ℂ)/(r.c:ℂ)).im x y v
        (cubicThetaCartesian_jetBound s _ _ hv))

lemma cubicThetaPrimitivePower_fderiv_bound (r : CubicThetaPrimitiveRow) (s : ℂ)
    {p : ℂ × ℝ} (hp : 0<p.2) :
    ‖fderiv ℝ (fun q => cubicThetaPrimitivePower r q s) p‖≤
      3*(‖cubicThetaPrimitivePower r p s‖*(cubicThetaFirstJetConstant s/p.2)) := by
  have he : cubicThetaCartesianPoint p.1.re p.1.im p.2=p := by
    apply Prod.ext
    · exact Complex.re_add_im p.1
    · rfl
  have hd := (cubicThetaPrimitivePower_contDiffAt r s hp).differentiableAt (by simp)
  have hc := cubicThetaFDeriv_coordinates p.1.re p.1.im p.2 (he ▸ hd)
  rw [he] at hc
  have hj := cubicThetaPrimitivePower_jetBound r s p.1.re p.1.im hp
  apply cubicThetaComplexProduct_opNorm_le _
    (mul_nonneg (_root_.norm_nonneg _) (div_nonneg (cubicThetaJetConstants_nonneg s).1 hp.le))
  · rw [hc.1]
    simpa only [he,cubicThetaAxisFunction,cubicThetaCoordinateCenter] using (hj .x).1
  · rw [hc.2.1]
    simpa only [he,cubicThetaAxisFunction,cubicThetaCoordinateCenter] using (hj .y).1
  · rw [hc.2.2]
    simpa only [he,cubicThetaAxisFunction,cubicThetaCoordinateCenter] using (hj .height).1

end CubicFirstMoment

end

end OAI
