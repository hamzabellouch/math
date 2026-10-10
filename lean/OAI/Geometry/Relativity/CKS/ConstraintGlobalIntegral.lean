import OAI.Geometry.Relativity.CKS.ConstraintCanonical
import OAI.Geometry.Relativity.CKS.ConstraintVolumeCoordinate

namespace OAI

noncomputable section
open Bundle Manifold Set Filter CKSLorentz CKSMetricGluing CKSSpatialManifold MeasureTheory
open scoped ContDiff Topology ENNReal
namespace CKSIntrinsicConstraints
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

def endConstraintChart
    (g : SmoothMetric I (M := M)) (K : InnerField I (M := M))
    (e : OpenPartialHomeomorph M E)
    (hf : ContMDiffOn I 𝓘(ℝ,E) ∞ e e.source)
    (A B : SpatialTensor)
    (hAs : ContDiffOn ℝ ∞ A e.target) (hBs : ContDiffOn ℝ ∞ B e.target)
    (hA : ∀ y ∈ e.target, (∀ v w, A y v w = A y w v) ∧ (∀ v : E, v ≠ 0 → 0 < A y v v))
    (hB : ∀ y ∈ e.target, ∀ v w, B y v w = B y w v)
    (hrep : ∀ x ∈ e.source, g.inner x = endInner I e A x ∧ K x = endInner I e B x)
    (x : M) (hx : x ∈ e.source) : ConstraintChart g.inner K x where
  domain := e.source
  coordinate := e
  metric := A
  tensor := B
  isOpen := e.open_source
  mem := hx
  smooth := hf
  fullRank := fun y hy => endInner_fullRank g e A (hrep y hy).1
  coefficientSmooth := fun _ hy =>
    ⟨(hAs _ (e.map_source hy)).contDiffAt (e.open_target.mem_nhds (e.map_source hy)),
      (hBs _ (e.map_source hy)).contDiffAt (e.open_target.mem_nhds (e.map_source hy))⟩
  positiveSymmetric := fun _ hy =>
    ⟨(hA _ (e.map_source hy)).1,(hA _ (e.map_source hy)).2,hB _ (e.map_source hy)⟩
  represents := hrep

theorem exists_integrable_constraint_densities
    (g : SmoothMetric I (M := M)) (K : InnerField I (M := M))
    (hDEC : PhysicalDEC I g.inner K)
    (e : OpenPartialHomeomorph M E) (hcompact : IsCompact e.sourceᶜ)
    (hf : ContMDiffOn I 𝓘(ℝ,E) ∞ e e.source)
    (A B : SpatialTensor)
    (hAs : ContDiffOn ℝ ∞ A e.target) (hBs : ContDiffOn ℝ ∞ B e.target)
    (hA : ∀ y ∈ e.target, (∀ v w, A y v w = A y w v) ∧ (∀ v : E, v ≠ 0 → 0 < A y v v))
    (hB : ∀ y ∈ e.target, ∀ v w, B y v w = B y w v)
    (hrep : ∀ x ∈ e.source, g.inner x = endInner I e A x ∧ K x = endInner I e B x)
    (hCint : IntegrableOn (spatialEnergy A B) e.target (spatialVolume A))
    (hQint : IntegrableOn (coordinateMomentumNorm A B) e.target (spatialVolume A)) :
    ∃ C Q : M → ℝ, Continuous C ∧ Continuous Q ∧
      Integrable C (CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
      Integrable Q (CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric) ∧
      (∀ x, 0 ≤ Q x ∧ Q x ≤ C x) ∧
      ∀ x (c : ConstraintChart g.inner K x), C x = c.energy ∧ Q x = c.momentumNorm := by
  obtain ⟨C,Q,hC,hQ,hdec,hsame⟩ := exists_canonical_constraint_densities g K hDEC
  let ν := CKSIntrinsicVolume.riemannianVolume g.toContinuousRiemannianMetric
  have hv : ν.restrict e.source = Measure.map e.symm ((spatialVolume A).restrict e.target) :=
    riemannianVolume_end g e A hf (fun x hx => (hrep x hx).1)
  have heq : ∀ᵐ y ∂(spatialVolume A).restrict e.target,
      C (e.symm y) = spatialEnergy A B y ∧ Q (e.symm y) = coordinateMomentumNorm A B y := by
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
    have h := hsame (e.symm y) (endConstraintChart g K e hf A B hAs hBs hA hB hrep _ (e.map_target hy))
    simpa only [ConstraintChart.energy,ConstraintChart.momentumNorm,endConstraintChart,e.right_inv hy] using h
  have hm : AEMeasurable e.symm ((spatialVolume A).restrict e.target) :=
    e.continuousOn_symm.aemeasurable e.open_target.measurableSet
  have hCe : IntegrableOn C e.source ν := by
    rw [IntegrableOn,hv]
    exact (integrable_map_measure hC.aestronglyMeasurable hm).mpr
      (hCint.congr (heq.mono fun _ h => h.1.symm))
  have hQe : IntegrableOn Q e.source ν := by
    rw [IntegrableOn,hv]
    exact (integrable_map_measure hQ.aestronglyMeasurable hm).mpr
      (hQint.congr (heq.mono fun _ h => h.2.symm))
  have hCc : IntegrableOn C e.sourceᶜ ν := hC.continuousOn.integrableOn_compact hcompact
  have hQc : IntegrableOn Q e.sourceᶜ ν := hQ.continuousOn.integrableOn_compact hcompact
  have hCall : Integrable C ν := by
    simpa only [union_compl_self,integrableOn_univ] using hCe.union hCc
  have hQall : Integrable Q ν := by
    simpa only [union_compl_self,integrableOn_univ] using hQe.union hQc
  exact ⟨C,Q,hC,hQ,hCall,hQall,hdec,hsame⟩
end CKSIntrinsicConstraints

end

end OAI
