import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalBlockEnergySum
import OAI.Analysis.Conductivity.Variational.CompletePhysicalAttachment
import OAI.Analysis.Conductivity.Flux.PhysicalEndSmoothGreen
import OAI.Analysis.Conductivity.Variational.PhysicalSmoothTest
import OAI.Analysis.Conductivity.Sobolev.CentralPhysicalEnergy

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

def physicalSmoothOuterTrace {φ : (Fin 3 → ℝ) → ℝ} (s : Fin 3 → ℝ)
    (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (i : Fin 3) : spectralTraceGraph (torusRate s) :=
  Fin.cases (smoothCollarTrace s 0 hφ)
    (fun k => smoothCollarTrace s 0 (hφ.comp (sourceChildCoordinates_contDiff (actualChildSign k)))) i

def physicalEndLength (a : Fin 3 → ℝ) (i : Fin 3) : ℝ := |a i| *centralThickness

lemma H1JetOn.attached_gradient {s a κ : Fin 3 → ℝ} {p : centralEnergySpace s}
    {w : H1} {i : Fin 3} (hw : H1JetOn w (physicalEndRegion i) (attachedPhysicalJet s a κ p i)) :
    ∀ᵐ y : Fin 3 → ℝ,y∈physicalEndRegion i → originalPiGradient w y=
      (fun j => attachedPhysicalJet s a κ p i (WithLp.toLp 2 y) j.succ) := by
  apply originalPiGradient_eq_on_ball (fun _ => physicalEndRegion_subset_ball i) w _
  filter_upwards [hw] with x hx hy j
  exact congrArg (fun v : JetFiber => v j.succ) (hx hy)

lemma attached_child_end_energy_pullback (s a κ : Fin 3 → ℝ) (p : centralEnergySpace s)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (k : Fin 2) :
    (∫ y in physicalEndRegion k.succ,
      (fun j => attachedPhysicalJet s a κ p k.succ (WithLp.toLp 2 y) j.succ) ⬝ᵥ
        (physicalEndTensor s a k.succ y*ᵥphysicalTestCovector φ y))=
      ∫ y in sourceClosedCollarBand (-centralThickness) 0,
        fullAttachedEndGradient s (centralT s k.succ p) (a k.succ) (-centralThickness) (κ k.succ) y ⬝ᵥ
          (attachedCollarTensor s (a k.succ) y*ᵥphysicalTestCovector (φ ∘ sourceChildCoordinates (actualChildSign k)) y) := by
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
  change sourceScale^3*((fun j => sourceScale⁻¹*fullAttachedEndGradient s (centralT s k.succ p)
    (a k.succ) (-centralThickness) (κ k.succ)
    ((sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)) (childAxis j)) ⬝ᵥ
    (sourceChildTensorPush k (attachedCollarTensor s (a k.succ))
      (sourceChildCoordinates (actualChildSign k) y)*ᵥphysicalTestCovector φ
        (sourceChildCoordinates (actualChildSign k) y)))=_
  have hv : (sourceChildHomeomorph (actualChildSign k)).symm
      (sourceChildCoordinates (actualChildSign k) y)=y :=
    (sourceChildHomeomorph (actualChildSign k)).symm_apply_apply y
  rw [hv,
    sourceChildTensorPush_mixed,physicalTestCovector_child hφ]

lemma attached_parent_jet_smooth_green (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha₀ : a 0<0) (_ : ∀ k : Fin 2,0<a k.succ) (p : centralEnergySpace s)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)  :
    (∫ y in physicalEndRegion 0,(fun j => attachedPhysicalJet s a κ p 0 (WithLp.toLp 2 y) j.succ) ⬝ᵥ
      (physicalEndTensor s a 0 y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s 0 p))
        (spectralGraphWeight (torusRate s) (centralT s 0 (physicalSmoothCentral s hφ)))-
      κ 0*spectralGraphMean (torusRate s) (centralT s 0 (physicalSmoothCentral s hφ))+
      cylinderTerminalFlux s (κ 0) (physicalEndLength a 0) (centralT s 0 p)
        (physicalSmoothOuterTrace s hφ 0)) := by
  change (∫ y in sourceClosedCollarBand 0 centralThickness,
    fullAttachedEndGradient s (centralT s 0 p) (a 0) centralThickness (κ 0) y ⬝ᵥ
      (attachedCollarTensor s (a 0) y*ᵥphysicalTestCovector φ y))=_
  rw [fullAttachedEnd_smooth_green_neg s hs (centralT s 0 p) (κ 0) hφ ha₀
    (by norm_num [centralThickness]) (R:=physicalEndLength a 0)
    (by dsimp [physicalEndLength]; rw [abs_of_neg ha₀]; ring)
    (by norm_num) (by norm_num [centralThickness]),physicalSmoothCentral_parent_trace s hφ]
  rfl

lemma attached_child_jet_smooth_green (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (_ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) (p : centralEnergySpace s)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (k : Fin 2) :
    (∫ y in physicalEndRegion k.succ,(fun j => attachedPhysicalJet s a κ p k.succ (WithLp.toLp 2 y) j.succ) ⬝ᵥ
      (physicalEndTensor s a k.succ y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s k.succ p))
        (spectralGraphWeight (torusRate s) (centralT s k.succ (physicalSmoothCentral s hφ)))-
      κ k.succ*spectralGraphMean (torusRate s) (centralT s k.succ (physicalSmoothCentral s hφ))+
      cylinderTerminalFlux s (κ k.succ) (physicalEndLength a k.succ) (centralT s k.succ p)
        (physicalSmoothOuterTrace s hφ k.succ)) := by
  conv_lhs => rw [attached_child_end_energy_pullback s a κ p hφ k]
  rw [fullAttachedEnd_smooth_green_pos s hs (centralT s k.succ p) (κ k.succ)
    (hφ.comp (sourceChildCoordinates_contDiff (actualChildSign k))) (ha k)
    (by norm_num [centralThickness]) (R:=physicalEndLength a k.succ)
    (by dsimp [physicalEndLength]; rw [abs_of_pos (ha k)]; ring)
    (by norm_num [centralThickness]) (by norm_num),physicalSmoothCentral_child_trace s hφ k]
  rfl

lemma attached_physical_jet_smooth_green (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) (p : centralEnergySpace s)
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (i : Fin 3) :
    (∫ y in physicalEndRegion i,(fun j => attachedPhysicalJet s a κ p i (WithLp.toLp 2 y) j.succ) ⬝ᵥ
      (physicalEndTensor s a i y*ᵥphysicalTestCovector φ y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s i p))
        (spectralGraphWeight (torusRate s) (centralT s i (physicalSmoothCentral s hφ)))-
      κ i*spectralGraphMean (torusRate s) (centralT s i (physicalSmoothCentral s hφ))+
      cylinderTerminalFlux s (κ i) (physicalEndLength a i) (centralT s i p)
        (physicalSmoothOuterTrace s hφ i)) := by
  refine Fin.cases ?_ (fun k => ?_) i
  · exact attached_parent_jet_smooth_green s a κ hs ha₀ ha p hφ
  · exact attached_child_jet_smooth_green s a κ hs ha₀ ha p hφ k

lemma attached_physical_end_smooth_green (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) (p : centralEnergySpace s)
    (w : H1) (hw : ∀ i : Fin 3,H1JetOn w (physicalEndRegion i) (attachedPhysicalJet s a κ p i))
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) (i : Fin 3) :
    (∫ y in physicalEndRegion i,originalPiGradient w y ⬝ᵥ
      (physicalEndTensor s a i y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
      angularArea*(inner ℝ (spectralGraphWeight (torusRate s) (centralT s i p))
        (spectralGraphWeight (torusRate s) (centralT s i (physicalSmoothCentral s hφ)))-
      κ i*spectralGraphMean (torusRate s) (centralT s i (physicalSmoothCentral s hφ))+
      cylinderTerminalFlux s (κ i) (physicalEndLength a i) (centralT s i p)
        (physicalSmoothOuterTrace s hφ i)) := by
  have he : (∫ y in physicalEndRegion i,originalPiGradient w y ⬝ᵥ
      (physicalEndTensor s a i y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
    ∫ y in physicalEndRegion i,
      (fun j => attachedPhysicalJet s a κ p i (WithLp.toLp 2 y) j.succ) ⬝ᵥ
        (physicalEndTensor s a i y*ᵥphysicalTestCovector φ y) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (hw i).attached_gradient,
      ae_restrict_of_ae (piSmoothH1_gradient hφ (fun _ => physicalEndRegion_subset_ball i)),
      ae_restrict_mem (physicalEndRegion_compact i).measurableSet] with y hw hv hy
    rw [hw hy,hv hy]
  exact he.trans (attached_physical_jet_smooth_green s a κ hs ha₀ ha p hφ i)

end ScalarConductivity



namespace ScalarConductivity
open Set MeasureTheory Filter Topology Matrix

lemma attached_block_smooth_green (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) (p : centralEnergySpace s)
    (hp : ∀ v : centralEnergySpace s,
      inner ℝ (centralD s p) (centralD s v)+angularArea*
        (∑ i : Fin 3,inner ℝ (spectralGraphWeight (torusRate s) (centralT s i p))
          (spectralGraphWeight (torusRate s) (centralT s i v)))=
      angularArea*(∑ i : Fin 3,κ i*spectralGraphMean (torusRate s) (centralT s i v)))
    (w : H1) (hwc : H1JetOn w centralPhysical (centralFullJetCLM s p.val))
    (hwe : ∀ i : Fin 3,H1JetOn w (physicalEndRegion i) (attachedPhysicalJet s a κ p i))
    {φ : (Fin 3 → ℝ) → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ) :
    (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
      (physicalBlockTensor s a y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
      angularArea*∑ i : Fin 3,cylinderTerminalFlux s (κ i) (physicalEndLength a i)
        (centralT s i p) (physicalSmoothOuterTrace s hφ i) := by
  have han (i : Fin 3) : a i≠0 := Fin.cases ha₀.ne (fun k => (ha k).ne') i
  rw [(physicalBlockTensor_energy_sum s a hs han w (piSmoothH1 hφ)).2,
    central_physical_energy p (physicalSmoothCentral s hφ) w (piSmoothH1 hφ) hwc
      (physicalSmoothCentral_jet s hφ)]
  simp_rw [attached_physical_end_smooth_green s a κ hs ha₀ ha p w hwe hφ]
  rw [←Finset.mul_sum,Finset.sum_add_distrib,Finset.sum_sub_distrib]
  have hv := hp (physicalSmoothCentral s hφ)
  nlinarith

theorem physical_attached_smooth_green_exists (s a κ : Fin 3 → ℝ)
    (hs : ∀ x y : ℝ,(1/2)*(x^2+y^2) ≤ s 0*x^2+2*s 1*x*y+s 2*y^2)
    (ha₀ : a 0<0) (ha : ∀ k : Fin 2,0<a k.succ) (hκ : ∑ i,κ i=0) :
    ∃ (p : centralEnergySpace s) (w : H1),w∈H10 ∧ centralM s p=0 ∧
      H1JetOn w centralPhysical (centralFullJetCLM s p.val) ∧
      (∀ i : Fin 3,H1JetOn w (physicalEndRegion i) (attachedPhysicalJet s a κ p i)) ∧
      ∀ (φ : (Fin 3 → ℝ) → ℝ) (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ),
        (∫ y in physicalBlockRegion,originalPiGradient w y ⬝ᵥ
          (physicalBlockTensor s a y*ᵥoriginalPiGradient (piSmoothH1 hφ) y))=
          angularArea*∑ i : Fin 3,cylinderTerminalFlux s (κ i) (physicalEndLength a i)
            (centralT s i p) (physicalSmoothOuterTrace s hφ i) := by
  obtain ⟨p,hpm,hp,_⟩ := central_unnormalized_variational_exists s κ hκ
  obtain ⟨w,hw0,hwc,hwe⟩ := complete_physical_attachment s hs a κ ha₀ ha p
  exact ⟨p,w,hw0,hpm,hwc,hwe,fun _ hφ =>
    attached_block_smooth_green s a κ hs ha₀ ha p hp w hwc hwe hφ⟩

end ScalarConductivity

end

end OAI
