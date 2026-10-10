import Mathlib
import OAI.Analysis.Conductivity.Flux.VariableCollarTensor
import OAI.Analysis.Conductivity.Fourier.AttachedPeriodicDerivative
import OAI.Analysis.Conductivity.Branching.PhysicalNullTransport
import OAI.Analysis.Conductivity.Branching.FlatEndingSplice
import OAI.Analysis.Conductivity.Fourier.SpectralAffineCovector
import OAI.Analysis.Conductivity.Fourier.AttachedPeriodicFlux

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix

lemma attachedVariableTensor_flux (K : Coord3 → Mat3) {a : ℝ} (ha : a≠0)
    (i j : Fin 4) {x : Coord3} (hx : x∈sourceExtendedBox (-(1:ℝ)/100) (1/100)) (v : Coord3) :
    attachedVariableTensor K a i j x*ᵥ(attachedCartesianMatrix a i j x*ᵥv)=
      (|a| *sourceFlatDensity i j x) • ((attachedCartesianMatrix a i j x)⁻¹ᵀ*ᵥ(K x*ᵥv)) := by
  have he : (attachedCartesianMatrix a i j x)⁻¹*ᵥ
      (attachedCartesianMatrix a i j x*ᵥv)=v := by
    rw [Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _
      (isUnit_iff_ne_zero.mpr (attachedCartesianMatrix_det_ne_zero ha i j hx)),Matrix.one_mulVec]
  simp only [attachedVariableTensor,Matrix.smul_mulVec,←Matrix.mulVec_mulVec,he]

lemma correctedEndGradient_transport {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) (a b : ℝ) (m n : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) (sourceCollarPiece m n x)+
      (fun k => lineDeriv ℝ (attachedPeriodicField (branchCorrection i z j) a b)
        (sourceCollarPiece m n x) (Pi.single k 1))=
      attachedCartesianMatrix a m n x*ᵥ(fun k => fderiv ℝ (branchSplicedField i z j)
        (flatEndCoordinates a b (sourceFaceAngles m n x)) (Pi.single k 1)) := by
  let y := flatEndCoordinates a b (sourceFaceAngles m n x)
  have hy : 0<y 0 := ht
  have hd := ((torusAffineField_smooth hs (centralBasisSlopes j i)
    (torusSpectralSynthesis s (f j))).contDiffAt
      ((axial_halfspace_open 0).mem_nhds hy)).differentiableAt (by norm_num)
  have hg := (branchCorrection_C2 i z hs j).differentiable (by norm_num)
  rw [fullAttachedEndGradient_transport s hs (f j) a b (centralBasisSlopes j i) m n hx ht,
    attachedPeriodicField_covector (branchCorrection_periodic i z j) hg a b m n hx,
    ←Matrix.mulVec_add]
  congr 1
  have he := torusAffineField_spectral_covector hs (f j) (centralBasisSlopes j i) hy
  have ha : torusAngles y=torusAngles (sourceFaceAngles m n x) :=
    torusAngles_endAxialAffine a b _
  rw [ha] at he
  change fullEndFlatCovector s (f j) (centralBasisSlopes j i) (y 0)
    (torusAngles (sourceFaceAngles m n x)) + _ = _
  rw [←he]
  ext k
  change fderiv ℝ (torusAffineField s (centralBasisSlopes j i) (torusSpectralSynthesis s (f j))) y
    (Pi.single k 1)+fderiv ℝ (branchCorrection i z j) y (Pi.single k 1)=_
  change _ = fderiv ℝ ((torusAffineField s (centralBasisSlopes j i)
    (torusSpectralSynthesis s (f j)))+branchCorrection i z j) y (Pi.single k 1)
  rw [fderiv_add hd (hg y)]
  rfl

lemma fullAttachedEnd_flat_flux {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : spectralTraceGraph (torusRate s)) (κ : ℝ) {a b : ℝ} (ha : a≠0)
    (m n : Fin 4) {x : Coord3} (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b)) :
    attachedCollarTensor s a (sourceCollarPiece m n x)*ᵥ
      fullAttachedEndGradient s f a b κ (sourceCollarPiece m n x)=
      (|a| *sourceFlatDensity m n x) • ((attachedCartesianMatrix a m n x)⁻¹ᵀ*ᵥ
        flatModeFlux s (torusAffineField s κ (torusSpectralSynthesis s f))
          (flatEndCoordinates a b (sourceFaceAngles m n x))) := by
  rw [attachedCollarTensor_open s a m n hx,
    fullAttachedEndGradient_transport s hs f a b κ m n hx ht]
  change attachedVariableTensor (fun _ => flatBackgroundTensor s) a m n x*ᵥ
    (attachedCartesianMatrix a m n x*ᵥ_) = _
  rw [attachedVariableTensor_flux _ ha m n (sourceCollarOpenBox_subset hx),flatModeFlux_tensor]
  have he := torusAffineField_spectral_covector hs f κ
    (show 0<(flatEndCoordinates a b (sourceFaceAngles m n x)) 0 from ht)
  have ha' : torusAngles (flatEndCoordinates a b (sourceFaceAngles m n x))=
      torusAngles (sourceFaceAngles m n x) := torusAngles_endAxialAffine a b _
  rw [ha'] at he
  rw [he]
  rfl

lemma attachedSpliced_constitution_point {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) {a b : ℝ} (ha : a≠0) (m n : Fin 4) {x : Coord3}
    (hx : x∈sourceCollarOpenBox) (ht : 0<a*(x 0-b))
    (hE : branchSplicedTensor i z (flatEndCoordinates a b (sourceFaceAngles m n x))*ᵥ
      (fun k => fderiv ℝ (branchSplicedField i z j)
        (flatEndCoordinates a b (sourceFaceAngles m n x)) (Pi.single k 1))=
      branchSplicedFlux i z j (flatEndCoordinates a b (sourceFaceAngles m n x))) :
    variableCollarTensor (branchSplicedTensor i z) a b (sourceCollarPiece m n x)*ᵥ
      (fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) (sourceCollarPiece m n x)+
        (fun k => lineDeriv ℝ (attachedPeriodicField (branchCorrection i z j) a b)
          (sourceCollarPiece m n x) (Pi.single k 1)))=
      attachedCollarTensor s a (sourceCollarPiece m n x)*ᵥ
        fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) (sourceCollarPiece m n x)+
      attachedPeriodicFlux (branchFluxCorrection i z j) a b (sourceCollarPiece m n x) := by
  rw [correctedEndGradient_transport hs f i z j a b m n hx ht,
    variableCollarTensor_open _ a b m n hx,attachedVariableTensor_flux _ ha m n (sourceCollarOpenBox_subset hx),hE,
    branchSplicedFlux,Matrix.mulVec_add,smul_add,
    fullAttachedEnd_flat_flux hs (f j) (centralBasisSlopes j i) ha m n hx ht,
    attachedPeriodicFlux_open _ a b m n hx]

lemma attachedSpliced_constitution_ae {s : Fin 3 → ℝ}
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
    (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))
    (j : Fin 2) {a b l r : ℝ} (ha : a≠0) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Ioo l r,0<a*(t-b)) :
    ∀ᵐ y ∂volume.restrict (sourceClosedCollarBand l r),
    variableCollarTensor (branchSplicedTensor i z) a b y*ᵥ
      (fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) y+
        fun k => lineDeriv ℝ (attachedPeriodicField (branchCorrection i z j) a b) y (Pi.single k 1))=
      attachedCollarTensor s a y*ᵥfullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) y+
        attachedPeriodicFlux (branchFluxCorrection i z j) a b y := by
  apply sourceClosedCollarBand_ae_faces hl hr
  intro m n
  have he := sourceFaceAngles_ae
    (flatEndCoordinates_ae ha b (branchSpliced_constitution i z hs j)) m n
  filter_upwards [ae_restrict_of_ae he,sourceExtendedBox_open_ae hl hr,
    sourceExtendedBox_axial_strict_ae l r] with x hx hxo hxt
  exact attachedSpliced_constitution_point hs f i z j ha m n hxo (hT _ hxt) hx

end ScalarConductivity

end
end

end OAI
