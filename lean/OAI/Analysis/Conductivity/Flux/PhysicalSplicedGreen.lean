import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalFiniteEndingData
import OAI.Analysis.Conductivity.Flux.AttachedSplicedGreen
import OAI.Analysis.Conductivity.Branching.VariableBlockEnergy

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

def flatTensor (i : Fin 3) : Coord3 → Mat3 := branchSplicedTensor i (z.ending i)

lemma correctedEndJet_parent (j : Fin 2) (y : Coord3) :
    (fun k : Fin 3 => z.correctedEndJet j 0 (WithLp.toLp 2 y) k.succ)=
      splicedAttachedGradient (fun j => centralT s 0 (z.p j)) 0 (z.ending 0) j
        (z.compression 0) centralThickness y := by
  ext k
  rfl

lemma correctedEndJet_child (j : Fin 2) (n : Fin 2) (y : Coord3) :
    (fun k : Fin 3 => z.correctedEndJet j n.succ (WithLp.toLp 2 y) k.succ)=
      fun k => sourceScale⁻¹*splicedAttachedGradient (fun j => centralT s n.succ (z.p j))
        n.succ (z.ending n.succ) j (z.compression n.succ) (-centralThickness)
        ((sourceChildHomeomorph (actualChildSign n)).symm y) (childAxis k) := by
  ext k
  dsimp [correctedEndJet,attachedPhysicalJet,periodicCorrectionJet,physicalJet,splicedAttachedGradient]
  ring

lemma corrected_child_energy_pullback (j : Fin 2)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (k : Fin 2) :
    (∫ y in physicalEndRegion k.succ,
      (fun n : Fin 3 => z.correctedEndJet j k.succ (WithLp.toLp 2 y) n.succ) ⬝ᵥ
        (variableEndTensor z.flatTensor z.compression k.succ y*ᵥphysicalTestCovector φ y))=
      ∫ y in sourceClosedCollarBand (-centralThickness) 0,
        splicedAttachedGradient (fun j => centralT s k.succ (z.p j)) k.succ (z.ending k.succ) j
          (z.compression k.succ) (-centralThickness) y ⬝ᵥ
          (variableCollarTensor (z.flatTensor k.succ) (z.compression k.succ) (-centralThickness) y*ᵥ
            physicalTestCovector (φ ∘ sourceChildCoordinates (actualChildSign k)) y) := by
  have hreg : physicalEndRegion k.succ=sourceChildCoordinates (actualChildSign k) ''
      sourceClosedCollarBand (-centralThickness) 0 := by
    change (sourceChildHomeomorph (actualChildSign k)).symm ⁻¹' _=_
    ext y
    constructor
    · intro hy
      exact ⟨(sourceChildHomeomorph (actualChildSign k)).symm y,hy,
        (sourceChildHomeomorph (actualChildSign k)).apply_symm_apply y⟩
    · rintro ⟨x,hx,rfl⟩
      change (sourceChildHomeomorph (actualChildSign k)).symm
        ((sourceChildHomeomorph (actualChildSign k)) x)∈sourceClosedCollarBand (-centralThickness) 0
      simpa only [Homeomorph.symm_apply_apply] using hx
  conv_lhs => rw [hreg]
  conv_lhs => rw [sourceChild_integral (actualChildSign k) childEndBand_measurable]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [z.correctedEndJet_child]
  have hv : (sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply y
  rw [hv]
  change sourceScale^3*((fun n => sourceScale⁻¹*splicedAttachedGradient _ _ _ _ _ _ y (childAxis n)) ⬝ᵥ
    (sourceChildTensorPush k _ (sourceChildCoordinates (actualChildSign k) y)*ᵥ
      physicalTestCovector φ (sourceChildCoordinates (actualChildSign k) y)))=_
  rw [sourceChildTensorPush_mixed,physicalTestCovector_child hφ]

lemma corrected_parent_jet_green
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (∫ y in physicalEndRegion 0,(fun k : Fin 3 => z.correctedEndJet j 0 (WithLp.toLp 2 y) k.succ) ⬝ᵥ
      (variableEndTensor z.flatTensor z.compression 0 y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s 0 (z.p j)))
        (spectralGraphWeight (torusRate s) (centralT s 0 (physicalSmoothCentral s hφ)))-
      centralBasisSlopes j 0*spectralGraphMean (torusRate s) (centralT s 0 (physicalSmoothCentral s hφ))+
      centralBasisSlopes j 0*spectralGraphMean (torusRate s) (physicalSmoothOuterTrace s hφ 0)) := by
  simp_rw [z.correctedEndJet_parent]
  change (∫ y in sourceClosedCollarBand 0 centralThickness,splicedAttachedGradient _ _ _ _ _ _ _ ⬝ᵥ
    (variableCollarTensor _ _ _ _*ᵥphysicalTestCovector φ y))=_
  dsimp only [flatTensor]
  rw [(splicedAttached_smooth_green_neg (fun j => centralT s 0 (z.p j)) 0 (z.ending 0) hs j hφ
    (l:=0) (r:=centralThickness) z.compression_parent (by norm_num [centralThickness]) (R:=physicalEndLength z.compression 0)
    (by dsimp [physicalEndLength]; rw [abs_of_neg z.compression_parent]; ring)
    (by rw [z.end_length]; linarith)
    (by norm_num) (by norm_num [centralThickness])).2,physicalSmoothCentral_parent_trace s hφ]
  rfl

lemma corrected_child_jet_green
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (k : Fin 2) :
    (∫ y in physicalEndRegion k.succ,(fun n : Fin 3 => z.correctedEndJet j k.succ (WithLp.toLp 2 y) n.succ) ⬝ᵥ
      (variableEndTensor z.flatTensor z.compression k.succ y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s k.succ (z.p j)))
        (spectralGraphWeight (torusRate s) (centralT s k.succ (physicalSmoothCentral s hφ)))-
      centralBasisSlopes j k.succ*spectralGraphMean (torusRate s) (centralT s k.succ (physicalSmoothCentral s hφ))+
      centralBasisSlopes j k.succ*spectralGraphMean (torusRate s) (physicalSmoothOuterTrace s hφ k.succ)) := by
  rw [z.corrected_child_energy_pullback j hφ k]
  dsimp only [flatTensor]
  rw [(splicedAttached_smooth_green_pos (fun j => centralT s k.succ (z.p j)) k.succ (z.ending k.succ) hs j
    (hφ.comp (sourceChildCoordinates_contDiff (actualChildSign k)))
    (l:= -centralThickness) (r:=0) (z.compression_child k) (by norm_num [centralThickness]) (R:=physicalEndLength z.compression k.succ)
    (by dsimp [physicalEndLength]; rw [abs_of_pos (z.compression_child k)]; ring)
    (by rw [z.end_length]; linarith)
    (by norm_num [centralThickness]) (by norm_num)).2,physicalSmoothCentral_child_trace s hφ k]
  rfl

lemma corrected_jet_green
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (i : Fin 3) :
    (∫ y in physicalEndRegion i,(fun n : Fin 3 => z.correctedEndJet j i (WithLp.toLp 2 y) n.succ) ⬝ᵥ
      (variableEndTensor z.flatTensor z.compression i y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s i (z.p j)))
        (spectralGraphWeight (torusRate s) (centralT s i (physicalSmoothCentral s hφ)))-
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (centralT s i (physicalSmoothCentral s hφ))+
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (physicalSmoothOuterTrace s hφ i)) :=
  Fin.cases (z.corrected_parent_jet_green hs j hφ) (fun k => z.corrected_child_jet_green hs j hφ k) i

end PhysicalFiniteEndingData
end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix
local instance physicalSplicedGreenMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance physicalSplicedGreenBorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

def constantTerminalFluxCLM (κ : Fin 3 → ℝ) : H1 →L[ℝ] ℝ :=
  angularArea • ∑ i : Fin 3,κ i •
    (Complex.reCLM.comp ((lp.evalCLM ℂ (fun _ : TorusModes => ℂ) 2 0).restrictScalars ℝ)).comp
      (physicalOuterTraceCLM i)

lemma constantTerminalFlux_smooth (s κ : Fin 3 → ℝ)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    constantTerminalFluxCLM κ (piSmoothH1 hφ)=angularArea*∑ i : Fin 3,
      κ i*spectralGraphMean (torusRate s) (physicalSmoothOuterTrace s hφ i) := by
  simp only [constantTerminalFluxCLM,_root_.smul_apply,_root_.sum_apply,
    ContinuousLinearMap.comp_apply,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [physicalOuterTrace_smooth i hφ s]
  rfl

namespace PhysicalFiniteEndingData
variable {s : Fin 3 → ℝ} (z : PhysicalFiniteEndingData s)

lemma flatTensor_properties
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) (i : Fin 3) :
    Measurable (z.flatTensor i) ∧ (∀ x,(z.flatTensor i x).IsSymm) ∧
      ∃ c C : ℝ,0<c ∧ c≤C ∧ ∀ x v,c*(v ⬝ᵥ v)≤v ⬝ᵥ(z.flatTensor i x*ᵥv) ∧
        v ⬝ᵥ(z.flatTensor i x*ᵥv)≤C*(v ⬝ᵥ v) :=
  ⟨branchSplicedTensor_measurable i (z.ending i),branchSplicedTensor_symm i (z.ending i),
    branchSplicedTensor_elliptic i (z.ending i) hs⟩

lemma corrected_gradient (j : Fin 2) (i : Fin 3) {w : H1}
    (hw : H1JetOn w (physicalEndRegion i) (z.correctedEndJet j i)) :
    ∀ᵐ y : Coord3,y∈physicalEndRegion i → originalPiGradient w y=
      (fun k => z.correctedEndJet j i (WithLp.toLp 2 y) k.succ) := by
  apply originalPiGradient_eq_on_ball (fun _ => physicalEndRegion_subset_ball i) w _
  filter_upwards [hw] with x hx hy k
  exact congrArg (fun v : JetFiber => v k.succ) (hx hy)

lemma corrected_end_smooth_green
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) {w : H1} (hw : ∀ i,H1JetOn w (physicalEndRegion i) (z.correctedEndJet j i))
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (i : Fin 3) :
    (∫ y in physicalEndRegion i,originalPiGradient w y ⬝ᵥ
      (variableEndTensor z.flatTensor z.compression i y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s i (z.p j)))
        (spectralGraphWeight (torusRate s) (centralT s i (physicalSmoothCentral s hφ)))-
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (centralT s i (physicalSmoothCentral s hφ))+
      centralBasisSlopes j i*spectralGraphMean (torusRate s) (physicalSmoothOuterTrace s hφ i)) := by
  have he : (∫ y in physicalEndRegion i,originalPiGradient w y ⬝ᵥ
      (variableEndTensor z.flatTensor z.compression i y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
      ∫ y in physicalEndRegion i,(fun n => z.correctedEndJet j i (WithLp.toLp 2 y) n.succ) ⬝ᵥ
        (variableEndTensor z.flatTensor z.compression i y*ᵥphysicalTestCovector φ y) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (z.corrected_gradient j i (hw i)),
      ae_restrict_of_ae (piSmoothH1_gradient hφ (fun _ => physicalEndRegion_subset_ball i)),
      ae_restrict_mem (physicalEndRegion_compact i).measurableSet] with y hw hv hy
    rw [hw hy,hv hy]
  exact he.trans (z.corrected_jet_green hs j hφ i)

lemma corrected_block_smooth_green
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (w : H1) (hwc : H1JetOn w centralPhysical (centralFullJetCLM s (z.p j).val))
    (hwe : ∀ i,H1JetOn w (physicalEndRegion i) (z.correctedEndJet j i))
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
      (variableBlockTensor z.flatTensor z.compression y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
      constantTerminalFluxCLM (centralBasisSlopes j) (piSmoothH1 hφ) := by
  rw [(variableBlockTensor_energy_sum z.flatTensor z.compression (z.flatTensor_properties hs)
    z.compression_ne w (piSmoothH1 hφ)).2,
    central_physical_energy (z.p j) (physicalSmoothCentral s hφ) w (piSmoothH1 hφ) hwc
      (physicalSmoothCentral_jet s hφ),constantTerminalFlux_smooth s]
  simp_rw [z.corrected_end_smooth_green hs j hwe hφ]
  rw [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hv := z.variational j (physicalSmoothCentral s hφ)
  nlinarith

lemma corrected_block_green
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (j : Fin 2) (w : H1) (hwc : H1JetOn w centralPhysical (centralFullJetCLM s (z.p j).val))
    (hwe : ∀ i,H1JetOn w (physicalEndRegion i) (z.correctedEndJet j i)) (v : H1) :
    (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
      (variableBlockTensor z.flatTensor z.compression y*ᵥoriginalPiGradient v y))=
      constantTerminalFluxCLM (centralBasisSlopes j) v := by
  refine smoothPiH1L_dense.induction_on v ?_ ?_
  · exact isClosed_eq (variableBlockEnergy_continuous z.flatTensor z.compression
      (z.flatTensor_properties hs) z.compression_ne w)
      (constantTerminalFluxCLM (centralBasisSlopes j)).continuous
  intro φ
  exact z.corrected_block_smooth_green hs j w hwc hwe (smoothScalar_contDiff φ)

theorem corrected_pair_green_exists
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2)≤ s 0*x^2+2*s 1*x*y+s 2*y^2) :
    ∃ w : Fin 2 → H1,(∀ j,w j∈H10) ∧
      (∀ j,H1JetOn (w j) centralPhysical (centralFullJetCLM s (z.p j).val)) ∧
      (∀ j i,H1JetOn (w j) (physicalEndRegion i) (z.correctedEndJet j i)) ∧
      ∀ j v,(∫ y in physicalBlockRegion,originalPiGradient (w j) y ⬝ᵥ
        (variableBlockTensor z.flatTensor z.compression y*ᵥoriginalPiGradient v y))=
        constantTerminalFluxCLM (centralBasisSlopes j) v := by
  obtain ⟨u,w,h0,hc,he,_⟩ := z.corrected_pair_exists hs
  exact ⟨w,fun j => (h0 j).2,fun j => (hc j).2,fun j i => (he j i).2,
    fun j v => z.corrected_block_green hs j (w j) (hc j).2 (fun i => (he j i).2) v⟩

end PhysicalFiniteEndingData
end ScalarConductivity

end

end OAI
