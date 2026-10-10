import Mathlib
import OAI.Analysis.Conductivity.Flux.TorusFluxDecay
import OAI.Analysis.Conductivity.Fourier.AffineFourierField
import OAI.Analysis.Conductivity.Geometry.TorusIntegralAlgebra

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology Real MeasureTheory Matrix

theorem affine_fourier_mean_axial_flux {s : Fin 3→ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    {a phase : (Fin 2→ℤ)→ℝ} {B gap t : ℝ} (ha : ∀ h,|a h|≤B) (hg : 0<gap)
    (hr : ∀ h,a h≠0 → gap≤torusRate s h) (α β : ℝ) (ht : 0<t) :
    torusCellIntegral (2*Real.pi) (fun x => fderiv ℝ (affineFourierField s a phase α β) x (flatAxis 0)) t=
      (2*Real.pi)^2*α := by
  have hf := flatFourier_smooth (phase:=phase) hs ha
  have hd := (hf.fderiv_of_isOpen (axial_halfspace_open 0) (m:=↑(⊤:ℕ∞)) (by simp)).clm_apply
    (contDiffOn_const (c:=flatAxis 0))
  have hc := (halfspace_slice_smooth hd ht).continuous
  have he : torusCellIntegral (2*Real.pi)
      (fun x => fderiv ℝ (affineFourierField s a phase α β) x (flatAxis 0)) t=
      torusCellIntegral (2*Real.pi) (fun x => α+fderiv ℝ (flatFourier s a phase) x (flatAxis 0)) t := by
    apply intervalIntegral.integral_congr
    intro y _
    apply intervalIntegral.integral_congr
    intro z _
    change fderiv ℝ (affineFourierField s a phase α β) ![t,y,z] (flatAxis 0)=_
    rw [affineFourierField_fderiv hs ha α β (x:=![t,y,z]) ht]
    simp [flatAxis]
  rw [he,torusCellIntegral_add (by positivity) continuous_const hc,
    torusCellIntegral_const,flatFourier_mean_axial_flux_zero hs ha hg hr ht,add_zero]

end ScalarConductivity

end
end

end OAI
