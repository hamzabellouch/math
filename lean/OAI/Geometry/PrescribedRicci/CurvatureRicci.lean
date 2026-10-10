import Mathlib
import OAI.Geometry.PrescribedRicci.ChernLuAlgebra
import OAI.Geometry.PrescribedPotential.VolumePath

namespace OAI

/-! Curvature Ricci. -/

section

 

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder MatrixOrder Matrix.Norms.Elementwise
namespace MongeAmpere
variable {d : ℕ}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

lemma contDiffAt_logdetReal (H : Mat) (hH : H.PosDef) :
    ContDiffAt ℝ ∞ (fun M : Mat => Real.log M.det.re) H := by
  exact ((Complex.reCLM.contDiff.contDiffAt).comp H
    ((contDiff_det.restrict_scalars ℝ).contDiffAt)).log
      (ne_of_gt (Complex.pos_iff.mp hH.det_pos).1)

lemma fderiv_logdetReal (H K : Mat) (hH : H.PosDef) :
    fderiv ℝ (fun M : Mat => Real.log M.det.re) H K = (H⁻¹*K).trace.re := by
  have hp : HasDerivAt (fun t : ℝ => H + (t:ℂ) • K) K 0 := by
    convert! ((hasDerivAt_id (0 : ℝ)).smul_const K).const_add H using 1
    simp only [one_smul]
  have hd := ((contDiffAt_logdetReal H hH).differentiableAt (by simp)).hasFDerivAt
  have hd' : HasFDerivAt (fun M : Mat => Real.log M.det.re)
      (fderiv ℝ (fun M : Mat => Real.log M.det.re) H) (H + ((0:ℝ):ℂ) • K) := by
    convert! hd using 1
    simp only [Complex.ofReal_zero,zero_smul,add_zero]
  have hf := hd'.comp_hasDerivAt 0 hp
  exact hf.unique (hasDerivAt_logdet_add_smul H K hH)

lemma trace_mul_real {H K : Mat} (hH : H.IsHermitian) (hK : K.IsHermitian) :
    ((H*K).trace.re : ℂ) = (H*K).trace := by
  have he : star (H*K).trace = (H*K).trace := by
    rw [← trace_conjTranspose,conjTranspose_mul,hH.eq,hK.eq,trace_mul_comm]
  have hi := congrArg Complex.im he
  change -(H*K).trace.im = (H*K).trace.im at hi
  apply Complex.ext
  · rfl
  · simp only [Complex.ofReal_im]; linarith

end MongeAmpere
namespace Anticanonical.SourceSmooth.KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}
local notation "Mat" => Matrix (Fin d) (Fin d) ℂ

lemma fderiv_logVolume (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (v : Coordinates d) :
    fderiv ℝ (fun y => Real.log (g.volumeCoefficient q y)) z v =
      ((g.matrix q z)⁻¹*fderiv ℝ (g.matrix q) z v).trace.re := by
  have hg := ((g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)).differentiableAt (by simp)
  have hh := (((MongeAmpere.contDiffAt_logdetReal _ (g.positive q z hz)).differentiableAt (by simp)).hasFDerivAt.comp z hg.hasFDerivAt).fderiv
  have he := congrArg (fun L : Coordinates d →L[ℝ] ℝ => L v) hh
  exact he.trans (MongeAmpere.fderiv_logdetReal _ _ (g.positive q z hz))

lemma holRealDeriv_logVolume (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) (a : Fin d) :
    holRealDeriv (fun y => Real.log (g.volumeCoefficient q y)) z a =
      ((g.matrix q z)⁻¹*holDerivative (g.matrix q) z a).trace := by
  change (2:ℂ)⁻¹ * ((fderiv ℝ (fun y => Real.log (g.volumeCoefficient q y)) z (coordinateVector a):ℂ) -
    Complex.I * (fderiv ℝ (fun y => Real.log (g.volumeCoefficient q y)) z (Complex.I • coordinateVector a):ℂ)) = _
  rw [g.fderiv_logVolume q hz,g.fderiv_logVolume q hz,
    MongeAmpere.trace_mul_real (g.positive q z hz).inv.isHermitian (g.derivative_hermitian q hz _),
    MongeAmpere.trace_mul_real (g.positive q z hz).inv.isHermitian (g.derivative_hermitian q hz _)]
  simp only [holDerivative,Matrix.mul_smul,mul_sub,trace_smul,trace_sub,smul_eq_mul]

lemma curvatureRicci_eq (g : KaehlerMetric A) (q : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart q).target) :
    g.curvatureRicci q z = PotentialKaehler.potentialMatrix (g.ricciPotential q) z := by
  have hs := (g.smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hi := ((MongeAmpere.contDiffAt_inv _ (g.positive q z hz).det_pos.ne').restrict_scalars ℝ).comp z hs
  have hl := (g.volumeCoefficient_smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hz)
  have hl' := hl.log (g.volumeCoefficient_pos q hz).ne'
  ext b a
  have he : (fun y => holRealDeriv (g.ricciPotential q) y a) =ᶠ[nhds z]
      (fun y => -((g.matrix q y)⁻¹*holDerivative (g.matrix q) y a).trace) := by
    filter_upwards [(A.chart q).open_target.mem_nhds hz] with y hy
    have hh := (g.volumeCoefficient_smooth q).contDiffAt ((A.chart q).open_target.mem_nhds hy)
    have hh' := (hh.log (g.volumeCoefficient_pos q hy).ne').differentiableAt (by simp)
    change holRealForm a (fderiv ℝ (fun w => -Real.log (g.volumeCoefficient q w)) y) = _
    rw [fderiv_fun_neg,map_neg]
    exact congrArg Neg.neg (g.holRealDeriv_logVolume q hy a)
  change ((g.matrix q z)⁻¹*g.curvatureMatrix q z b a).trace =
    PotentialKaehler.potentialMatrix (g.ricciPotential q) z b a
  have hric : ContDiffAt ℝ ∞ (g.ricciPotential q) z := hl'.neg
  rw [← barDeriv_holRealDeriv hric]
  have hb : barDeriv (fun y => holRealDeriv (g.ricciPotential q) y a) z b =
      -barDeriv (fun y => ((g.matrix q y)⁻¹*holDerivative (g.matrix q) y a).trace) z b := by
    unfold barDeriv
    rw [he.fderiv_eq,fderiv_fun_neg]
    simp only [_root_.neg_apply]; ring
  have hid : DifferentiableAt ℝ (fun y => (g.matrix q y)⁻¹) z := hi.differentiableAt (by simp)
  have hpd := (contDiffAt_holDerivative hs a).differentiableAt (by simp)
  have hprod : DifferentiableAt ℝ (fun y => (g.matrix q y)⁻¹*holDerivative (g.matrix q) y a) z :=
    (MongeAmpere.matrixMulCLM.hasFDerivAt_of_bilinear hid.hasFDerivAt hpd.hasFDerivAt).differentiableAt
  rw [hb,barDeriv_trace hprod,
    barDerivative_mul hid hpd,
    barDerivative_inv (hs.differentiableAt (by simp)) (isUnit_iff_ne_zero.mpr (g.positive q z hz).det_pos.ne')]
  simp only [curvatureMatrix,mul_add,mul_neg,neg_mul,trace_add,trace_neg,mul_assoc]
  abel

end Anticanonical.SourceSmooth.KaehlerMetric

end
end

end OAI
