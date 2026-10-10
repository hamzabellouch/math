import Mathlib
import OAI.Analysis.Conductivity.Geometry.PhysicalCollarBand
import OAI.Analysis.Conductivity.Fourier.AttachedEndPoisson
import OAI.Analysis.Conductivity.Geometry.AffineCylinder

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology UnitAddTorus
open scoped ENNReal

def attachedEndPoissonJet (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {a b l r R : ℝ}
    (ha : a≠0) (hR : 0≤R) (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (j : Fin 4) :
    Lp ℂ 2 (sourcePhysicalCollarMeasure l r) :=
  sourceCollarPullback hlr hl hr (affineEndPullback ha hT (endPoissonJet s hs R hR f j))

lemma attachedEndPoissonJet_ae (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {a b l r R : ℝ}
    (ha : a≠0) (hR : 0≤R) (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (j : Fin 4) :
    attachedEndPoissonJet s hs f ha hR hlr hl hr hT j=ᵐ[sourcePhysicalCollarMeasure l r]
      attachedEndPoissonField s f a b j := by
  have he : affineEndPullback ha hT (endPoissonJet s hs R hR f j)=ᵐ[sourceCylinderMeasure l r]
      endPoissonField s f j ∘ affineEndCoordinates a b :=
    affineEndPullback_ae_of_ae ha hT _ (endPoissonJet_ae s hs R hR f j)
  have hp := sourceCollarPullback_ae_of_ae hlr hl hr _ he
  change sourceCollarPullback hlr hl hr (affineEndPullback ha hT (endPoissonJet s hs R hR f j))=ᵐ[sourcePhysicalCollarMeasure l r] _
  exact hp

lemma attachedEndPoissonField_memLp (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {a b l r R : ℝ}
    (ha : a≠0) (hR : 0≤R) (hlr : l≤r) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (j : Fin 4) :
    MemLp (attachedEndPoissonField s f a b j) 2
      (volume.restrict (sourceClosedCollarBand l r)) :=
  sourceClosedCollarBand_memLp hl hr
    ((memLp_congr_ae (attachedEndPoissonJet_ae s hs f ha hR hlr hl hr hT j)).mp
      (Lp.memLp (attachedEndPoissonJet s hs f ha hR hlr hl hr hT j)))

lemma attachedEndPoissonField_angular_memLp (s : Fin 3 → ℝ)
    (hs : ∀ u v : ℝ,(1/2)*(u^2+v^2) ≤ s 0*u^2+2*s 1*u*v+s 2*v^2)
    (f : spectralTraceGraph (torusRate s)) {a b l r R : ℝ}
    (ha : a≠0) (hR : 0≤R) (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R) (j : Fin 4) :
    MemLp (fun z : ℝ×UnitAddTorus (Fin 2) => attachedEndPoissonField s f a b j
      (sourceAngularCollar z.1 z.2)) 2 ((volume.restrict (Ioc l r)).prod volume) := by
  rw [←sourceCylinderMeasure_eq]
  have h : MemLp (endPoissonField s f j ∘ affineEndCoordinates a b) 2 (sourceCylinderMeasure l r) :=
    (memLp_congr_ae (affineEndPullback_ae_of_ae ha hT _
    (endPoissonJet_ae s hs R hR f j))).mp (Lp.memLp (affineEndPullback ha hT
      (endPoissonJet s hs R hR f j)))
  apply (memLp_congr_ae _).mp h
  have ht : ∀ᵐ z∂sourceCylinderMeasure l r,z.1∈Ioc l r :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioc)
  filter_upwards [ht] with z hz
  exact (attachedEndPoissonField_angular s f a b j ⟨hl.trans hz.1.le,hz.2.trans hr⟩ z.2).symm

end ScalarConductivity

end

end OAI
