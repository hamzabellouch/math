import OAI.Analysis.CircleDomains.Selection.SavedAppendingContours
import OAI.Analysis.CircleDomains.Sobolev.AppendingEnergyTolerance

namespace OAI

/-! A saved finite family includes a common positive tolerance for both
exact contour values and strict Sobolev energy bounds. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold ENNReal
noncomputable section
namespace CircleDomainRigidity

structure SavedSeparatingFamily (G : Set Sphere) (a η : ℝ)
    (p q : EuclideanPlane → ℝ)
    (Wp : DeGiorgi.MemW1pWitness 2 p (physicalPlaneDomain G))
    (Wq : DeGiorgi.MemW1pWitness 2 q (physicalPlaneDomain G)) where
  count : ℕ
  jordan : Fin count → ℂ ≃ₜ ℂ
  curve : Fin count → Circle → ℂ
  neighborhood : Fin count → Set ℂ
  barrier : Fin count → EuclideanPlane → ℝ
  cover : {z : ℂ | (z : Sphere) ∉ G} ⊆ ⋃ i, jordanInterior (jordan i)
  inside : ∀ i, closure (jordanInterior (jordan i)) ⊆ ball 0 (64*a)
  regular : ∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (curve i) ∧ Topology.IsEmbedding (curve i) ∧
    frontier (jordanInterior (jordan i)) = range (curve i) ∧ ∀ z ∈ range (curve i), (z : Sphere) ∈ G
  open_neighborhood : ∀ i, IsOpen (neighborhood i)
  contains : ∀ i, closure (jordanInterior (jordan i)) ⊆ neighborhood i
  smooth : ∀ i, ContDiff ℝ ∞ (barrier i)
  compact : ∀ i, HasCompactSupport (barrier i)
  unit : ∀ i x, barrier i x ∈ Icc (0 : ℝ) 1
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  stable : ∀ (p' q' : EuclideanPlane → ℝ), Continuous p' → Continuous q' →
    ∀ (Wp' : DeGiorgi.MemW1pWitness 2 p' (physicalPlaneDomain G ∩ ball 0 (65*a)))
      (Wq' : DeGiorgi.MemW1pWitness 2 q' (physicalPlaneDomain G ∩ ball 0 (65*a))),
    (∀ x, ‖planePair (p' x) (q' x)-planePair (p x) (q x)‖ ≤ tolerance) →
    (eLpNorm (fun x => Wp'.weakGrad x-Wp.weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal ≤ tolerance →
    (eLpNorm (fun x => Wq'.weakGrad x-Wq.weakGrad x) 2
      (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal ≤ tolerance →
    ∀ i,
      (∀ z ∈ neighborhood i, barrier i (planePair (p' (complexPlaneCoordinates.symm z))
        (q' (complexPlaneCoordinates.symm z))) = 1) ∧
      (∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a →
        barrier i (planePair (p' (complexPlaneCoordinates.symm z))
          (q' (complexPlaneCoordinates.symm z))) = 0) ∧
      ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => barrier i (planePair (p' x) (q' x)))
        (physicalPlaneDomain G ∩ ball 0 (65*a)),
        (eLpNorm W.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η

 theorem AppendingPairData.exists_saved_family
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    {a δ η : ℝ} (D : AppendingPairData G u Wold a δ η)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a) :
    Nonempty (SavedSeparatingFamily G a η D.p D.q D.p_witness D.q_witness) := by
  obtain ⟨n,J,γ,b,V,hcover,hb,hJ,hγ,hV,houter,_⟩ :=
    D.exists_saved_contours hsard hsch hG hinf hTD ha hBa
  let c := fun i : Fin n => planePair (sphereFromPlaneFunction D.p (b i))
    (sphereFromPlaneFunction D.q (b i))
  obtain ⟨t,ht,henergy⟩ := D.exists_energy_tolerance hG c
  let τ := min (D.radius/8) (min (a/2) t)/2
  have hmin : 0 < min (D.radius/8) (min (a/2) t) :=
    lt_min (div_pos D.radius_pos (by norm_num)) (lt_min (half_pos ha) ht)
  have hτ : 0 < τ := half_pos hmin
  have hτr : τ < D.radius/8 := (half_lt_self hmin).trans_le
    (min_le_left _ _)
  have hτa : τ < a/2 := (half_lt_self hmin).trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hτt : τ ≤ t := ((half_lt_self hmin).trans_le
    ((min_le_right _ _).trans (min_le_right _ _))).le
  refine ⟨{
    count := n, jordan := J, curve := γ, neighborhood := V
    barrier := fun i => translatedPhysicalBarrier D.barrier (c i)
    cover := hcover, inside := hJ, regular := hγ
    open_neighborhood := fun i => (hV i).1
    contains := fun i => (hV i).2.1
    smooth := fun i => D.barrier_smooth.comp (contDiff_id.sub contDiff_const)
    compact := ?_, unit := fun i x => D.barrier_unit (x-c i)
    tolerance := τ, tolerance_pos := hτ, stable := ?_ }⟩
  · intro i
    have he : translatedPhysicalBarrier D.barrier (c i) = D.barrier ∘ Homeomorph.addRight (-c i) := by
      funext x
      change D.barrier (x-c i) = D.barrier (x+-c i)
      rw [sub_eq_add_neg]
    rw [he]
    exact D.barrier_compact.comp_homeomorph _
  · intro p q hp hq Wp Wq hclose hpE hqE i
    refine ⟨?_,?_,?_⟩
    · exact (hV i).2.2 (fun z => planePair (p (complexPlaneCoordinates.symm z)) (q (complexPlaneCoordinates.symm z)))
        (fun z _ => (hclose _).trans_lt hτr)
    · exact houter i (fun z => planePair (p (complexPlaneCoordinates.symm z)) (q (complexPlaneCoordinates.symm z)))
        (fun z _ _ _ => (hclose _).trans_lt hτa)
    · exact henergy i p q hp hq Wp Wq (fun z _ => (hclose z).trans hτt)
        (hpE.trans hτt) (hqE.trans hτt)

end CircleDomainRigidity

end

end OAI
