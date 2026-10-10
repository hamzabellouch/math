import OAI.Geometry.SurfaceImmersion.Atlas.CompactPhaseDiskTopology
import OAI.Geometry.SurfaceImmersion.Geometry.ProjectedFrameConstruction
import OAI.Geometry.SurfaceImmersion.Geometry.BoundaryJetCurvature
import OAI.Geometry.SurfaceImmersion.Geometry.SecondFormNormalFields

namespace OAI

/-! The old boundary inequalities extend to one compact collar. This
supplies the zero-amplitude conditions on the full analytic domain. -/
noncomputable section
open Set Filter
open scoped ContDiff Topology
namespace ClosedSurfaceR4.GeometryPreservation
open SmallModes RealModes NormalFrame VelocityFrame

lemma actual_intrinsic_crossing_continuousOn {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {U : Set Base} (hD : ∀ x ∈ U, gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    (hB : ∀ x ∈ U, realSecondForm F dy dy x ≠ 0)
    {v : Base → Base} (hv : ContinuousOn v U) :
    ContinuousOn (fun x => orderedCrossing F dy (v x) x
      (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) x)) U := by
  let J := realBoundaryProfile F 1
  have hJ : Continuous J := (realBoundaryProfile_smooth hF 1).continuous
  have hκ : ContinuousOn (fun x => boundaryJetCurvature (J x)) U := by
    intro x hx
    exact ((continuousAt_boundaryJetCurvature (hD x hx)).comp hJ.continuousAt).continuousWithinAt
  have hcross : ContinuousOn (fun x => boundaryJetCrossing (J x) dy (v x)
      (boundaryJetCurvature (J x))) U := by
    intro x hx
    have hb : boundaryJetSecond (J x) dy dy ≠ 0 := by
      rw [boundaryJetSecond_actual hF]
      exact hB x hx
    exact (continuousAt_boundaryJetCrossing (J := J x) (v := dy) (w := v x)
      (κ := boundaryJetCurvature (J x)) (hD x hx) hb).comp_continuousWithinAt
      (f := fun y => (J y,dy,v y,boundaryJetCurvature (J y)))
      (hJ.continuousAt.continuousWithinAt.prodMk
        (continuousWithinAt_const.prodMk ((hv x hx).prodMk (hκ x hx))))
  exact hcross.congr (fun x hx => by
    dsimp only [J]
    rw [boundaryJetCrossing_actual hF,boundaryJetCurvature_actual hF x (hD x hx)])

theorem primitive_boundary_collar {F : RField 4} (hF : ContDiff ℝ ∞ F)
    {Ω D : Set Base} (hΩ : IsOpen Ω) (hD : IsOpen D)
    (hDc : IsCompact (closure D)) (hDΩ : closure D ⊆ Ω)
    (hI : ∀ x ∈ Ω, gramDet (coordDeriv dx F x) (coordDeriv dy F x) ≠ 0)
    {n : Base → Vec} (hn : ContDiffOn ℝ ∞ n Ω)
    (hboundary : ∀ x ∈ frontier D, realSecondForm F dy dy x ≠ 0 ∧
      normalize (realSecondForm F dy dy x) ≠ -n x)
    {ι : Type*} [Finite ι] (C : ι → Set Base) (hC : ∀ i, IsClosed (C i))
    (v : ι → Base → Base) (hv : ∀ i, ContDiff ℝ ∞ (v i))
    (hold : ∀ i x, x ∈ C i → x ∈ frontier D →
      0 < orderedCrossing F dy (v i x) x
        (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) x)) :
    ∃ V : Set Base, IsOpen V ∧ IsCompact (closure V) ∧ closure D ⊆ V ∧ closure V ⊆ Ω ∧
      (∀ x ∈ closure V \ D, realSecondForm F dy dy x ≠ 0 ∧
        normalize (realSecondForm F dy dy x) ≠ -n x) ∧
      ∀ i x, x ∈ C i → x ∈ closure V \ D →
        0 < orderedCrossing F dy (v i x) x
          (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) x) := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  let N := {x | x ∈ Ω ∧ realSecondForm F dy dy x ≠ 0 ∧
    normalize (realSecondForm F dy dy x) ≠ -n x}
  have hN : IsOpen N := nonopposite_region_open hΩ (realSecondForm_smoothOn hF hI dy dy) hn
  have hDN : frontier D ⊆ N := fun x hx => ⟨hDΩ (frontier_subset_closure hx),hboundary x hx⟩
  let Q := fun i x => orderedCrossing F dy (v i x) x
    (coordinateGaussianCurvature (realMetric F dx dx) (realMetric F dx dy) (realMetric F dy dy) x)
  have hQ (i : ι) : ContinuousOn (Q i) N :=
    actual_intrinsic_crossing_continuousOn hF (fun x hx => hI x hx.1)
      (fun _ hx => hx.2.1) ((hv i).continuous.continuousOn)
  let G := N ∩ ⋂ i, (C i)ᶜ ∪ (N ∩ (Q i) ⁻¹' Ioi 0)
  have hG : IsOpen G := hN.inter (isOpen_iInter_of_finite (fun i =>
    (hC i).isOpen_compl.union ((hQ i).isOpen_inter_preimage hN isOpen_Ioi)))
  have hDG : frontier D ⊆ G := by
    intro x hx
    refine ⟨hDN hx,mem_iInter.mpr fun i => ?_⟩
    by_cases hi : x ∈ C i
    · exact Or.inr ⟨hDN hx,hold i x hi hx⟩
    · exact Or.inl hi
  obtain ⟨V,hV,hVc,hDV,hVΩ,hVG⟩ := compact_phase_boundary_neighborhood hD hDc hΩ hDΩ hG hDG
  refine ⟨V,hV,hVc,hDV,hVΩ,fun x hx => (hVG hx).1.2,?_⟩
  intro i x hi hx
  exact (Or.resolve_left (mem_iInter.mp (hVG hx).2 i) (not_not.mpr hi)).2

end ClosedSurfaceR4.GeometryPreservation

end

end OAI
