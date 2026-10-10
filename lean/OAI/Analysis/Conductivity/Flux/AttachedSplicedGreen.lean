import Mathlib
import OAI.Analysis.Conductivity.Flux.PhysicalEndSmoothGreen
import OAI.Analysis.Conductivity.Scalarization.AttachedSplicedConstitution
import OAI.Analysis.Conductivity.Flux.BranchTerminalFluxIntegral
import OAI.Analysis.Conductivity.Fourier.AttachedPeriodicGreen

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix UnitAddTorus
open scoped ENNReal
local instance attachedSplicedGreenMeasureSpace : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance attachedSplicedGreenProbabilityMeasure : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

lemma symmetric_dotProduct_mulVec_swap {A : Mat3} (hA : A.IsSymm) (u v : Coord3) :
    u ⬝ᵥ(A*ᵥv)=(A*ᵥu) ⬝ᵥv := by
  rw [←hA,Matrix.dotProduct_transpose_mulVec,dotProduct_comm,hA]

variable {s : Fin 3 → ℝ} (f : Fin 2 → spectralTraceGraph (torusRate s)) (i : Fin 3)
  (z : TorusEndingData s (branchNormalize i (fun j => torusSpectralSynthesis s (f j))))

def splicedAttachedGradient (j : Fin 2) (a b : ℝ) (y : Coord3) : Coord3 :=
  fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) y+
    (fun k => lineDeriv ℝ (attachedPeriodicField (branchCorrection i z j) a b) y (Pi.single k 1))

lemma splicedAttached_energy_ae
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (φ : Coord3 → ℝ) {a b l r : ℝ} (ha : a≠0)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) (ht : ∀ t∈Ioo l r,0<a*(t-b)) :
    (fun y => splicedAttachedGradient f i z j a b y ⬝ᵥ
       (variableCollarTensor (branchSplicedTensor i z) a b y*ᵥphysicalTestCovector φ y))=ᵐ[
         volume.restrict (sourceClosedCollarBand l r)]
      fun y => fullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) y ⬝ᵥ
        (attachedCollarTensor s a y*ᵥphysicalTestCovector φ y)+
          attachedPeriodicFlux (branchFluxCorrection i z j) a b y ⬝ᵥphysicalTestCovector φ y := by
  filter_upwards [attachedSpliced_constitution_ae hs f i z j ha hl hr ht] with y hy
  rw [symmetric_dotProduct_mulVec_swap (variableCollarTensor_symm (branchSplicedTensor_symm i z) a b y),
    show variableCollarTensor (branchSplicedTensor i z) a b y*ᵥsplicedAttachedGradient f i z j a b y=
      attachedCollarTensor s a y*ᵥfullAttachedEndGradient s (f j) a b (centralBasisSlopes j i) y+
        attachedPeriodicFlux (branchFluxCorrection i z j) a b y from hy,add_dotProduct,
    symmetric_dotProduct_mulVec_swap (A:=attachedCollarTensor s a y)
      (attachedFaceTensorList_symmetric s a _ y)]

lemma splicedAttached_smooth_green_pos
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a l r R : ℝ} (ha : 0<a) (hlr : l<r) (hR : a*(r-l)=R) (hz : z.R<R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    IntegrableOn (fun y => splicedAttachedGradient f i z j a l y ⬝ᵥ
      (variableCollarTensor (branchSplicedTensor i z) a l y*ᵥphysicalTestCovector φ y))
        (sourceClosedCollarBand l r) volume ∧
    (∫ y in sourceClosedCollarBand l r,splicedAttachedGradient f i z j a l y ⬝ᵥ
      (variableCollarTensor (branchSplicedTensor i z) a l y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (f j))
        (spectralGraphWeight (torusRate s) (smoothCollarTrace s l hφ))-
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (smoothCollarTrace s l hφ)+
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (smoothCollarTrace s r hφ)) := by
  have hRp : 0<R := hR ▸ mul_pos ha (sub_pos.mpr hlr)
  have hT : ∀ t∈Icc l r,affineEndTime a l t∈Icc 0 R := by
    intro t ht
    dsimp [affineEndTime]
    constructor
    · exact mul_nonneg ha.le (sub_nonneg.mpr ht.1)
    · rw [←hR]; exact mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 l) ha.le
  have ht : ∀ t∈Ioo l r,0<a*(t-l) := fun t ht => mul_pos ha (sub_pos.mpr ht.1)
  have hO := (fullAttachedEnd_smooth_energy_pullback s hs (f j) (centralBasisSlopes j i) hφ
    ha.ne' hlr.le hRp.le hl hr hT ht).1
  obtain ⟨hC,hCI⟩ := attachedPeriodicFlux_smooth_green (branchFluxCorrection_C1 i z hs j)
    (branchFluxCorrection_periodic i z j) hφ ha.ne' hlr.le hRp.le hl hr hT
    (Or.inl ⟨ha,by ring,hR⟩) (fun x _ => branchFluxCorrection_divergence i z hs j x)
  have he := splicedAttached_energy_ae f i z hs j φ ha.ne' hl hr ht
  refine ⟨(hO.add hC).congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_add hO hC,
    fullAttachedEnd_smooth_green_pos s hs (f j) (centralBasisSlopes j i) hφ ha hlr hR hl hr,hCI,
    branchFluxCorrection_initial_integral hs i z j,
    branchFluxCorrection_terminal_integral hs f i z j hRp hz _ hφ]
  have hend : a⁻¹*R+l=r := by rw [←hR]; field_simp [ha.ne']; ring
  rw [hend]
  ring

lemma splicedAttached_smooth_green_neg
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a l r R : ℝ} (ha : a<0) (hlr : l<r) (hR : a*(l-r)=R) (hz : z.R<R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100) :
    IntegrableOn (fun y => splicedAttachedGradient f i z j a r y ⬝ᵥ
      (variableCollarTensor (branchSplicedTensor i z) a r y*ᵥphysicalTestCovector φ y))
        (sourceClosedCollarBand l r) volume ∧
    (∫ y in sourceClosedCollarBand l r,splicedAttachedGradient f i z j a r y ⬝ᵥ
      (variableCollarTensor (branchSplicedTensor i z) a r y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (f j))
        (spectralGraphWeight (torusRate s) (smoothCollarTrace s r hφ))-
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (smoothCollarTrace s r hφ)+
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (smoothCollarTrace s l hφ)) := by
  have hRp : 0<R := hR ▸ mul_pos_of_neg_of_neg ha (sub_neg.mpr hlr)
  have hT : ∀ t∈Icc l r,affineEndTime a r t∈Icc 0 R := by
    intro t ht
    dsimp [affineEndTime]
    constructor
    · exact mul_nonneg_of_nonpos_of_nonpos ha.le (sub_nonpos.mpr ht.2)
    · rw [←hR]; exact mul_le_mul_of_nonpos_left (sub_le_sub_right ht.1 r) ha.le
  have ht : ∀ t∈Ioo l r,0<a*(t-r) := fun t ht => mul_pos_of_neg_of_neg ha (sub_neg.mpr ht.2)
  have hO := (fullAttachedEnd_smooth_energy_pullback s hs (f j) (centralBasisSlopes j i) hφ
    ha.ne hlr.le hRp.le hl hr hT ht).1
  obtain ⟨hC,hCI⟩ := attachedPeriodicFlux_smooth_green (branchFluxCorrection_C1 i z hs j)
    (branchFluxCorrection_periodic i z j) hφ ha.ne hlr.le hRp.le hl hr hT
    (Or.inr ⟨ha,hR,by ring⟩) (fun x _ => branchFluxCorrection_divergence i z hs j x)
  have he := splicedAttached_energy_ae f i z hs j φ ha.ne hl hr ht
  refine ⟨(hO.add hC).congr he.symm,?_⟩
  rw [integral_congr_ae he,integral_add hO hC,
    fullAttachedEnd_smooth_green_neg s hs (f j) (centralBasisSlopes j i) hφ ha hlr hR hl hr,hCI,
    branchFluxCorrection_initial_integral hs i z j,
    branchFluxCorrection_terminal_integral hs f i z j hRp hz _ hφ]
  have hend : a⁻¹*R+r=l := by rw [←hR]; field_simp [ha.ne]; ring
  rw [hend]
  ring

end ScalarConductivity

end
end

end OAI
