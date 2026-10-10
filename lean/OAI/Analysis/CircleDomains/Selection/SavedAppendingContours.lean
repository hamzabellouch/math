import OAI.Analysis.CircleDomains.Selection.AppendingPairData
import OAI.Analysis.CircleDomains.Modulus.StableBarrierContours

namespace OAI

/-! The constructed pair yields actual smooth inner contours, translated
barriers and open neighborhoods with strict inner and outer margins. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ContDiff Manifold ENNReal
noncomputable section
namespace CircleDomainRigidity
attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩

 theorem AppendingPairData.exists_saved_contours
    {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}
    {Wold : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    {a δ η : ℝ} (D : AppendingPairData G u Wold a δ η)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
    (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
    (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ ball 0 a) :
    ∃ (n : ℕ) (J : Fin n → ℂ ≃ₜ ℂ) (γ : Fin n → Circle → ℂ)
      (b : Fin n → Sphere) (V : Fin n → Set ℂ),
      ({z : ℂ | (z : Sphere) ∉ G} ⊆ ⋃ i, jordanInterior (J i)) ∧
      (∀ i, b i ∈ Gᶜ) ∧
      (∀ i, closure (jordanInterior (J i)) ⊆ ball 0 (64*a)) ∧
      (∀ i, ContMDiff (𝓡 1) (𝓘(ℝ, ℂ)) ∞ (γ i) ∧ Topology.IsEmbedding (γ i) ∧
        frontier (jordanInterior (J i)) = range (γ i) ∧ ∀ z ∈ range (γ i), (z : Sphere) ∈ G) ∧
      (∀ i, IsOpen (V i) ∧ closure (jordanInterior (J i)) ⊆ V i ∧
        ∀ A' : ℂ → EuclideanPlane,
          (∀ z ∈ V i, ‖A' z-planePair (D.p (complexPlaneCoordinates.symm z))
            (D.q (complexPlaneCoordinates.symm z))‖ < D.radius/8) →
          ∀ z ∈ V i, D.barrier (A' z-planePair (sphereFromPlaneFunction D.p (b i))
            (sphereFromPlaneFunction D.q (b i))) = 1) ∧
      (∀ i (A' : ℂ → EuclideanPlane),
        (∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a →
          ‖A' z-planePair (D.p (complexPlaneCoordinates.symm z))
            (D.q (complexPlaneCoordinates.symm z))‖ < a/2) →
        ∀ z : ℂ, (z : Sphere) ∈ G → 63*a ≤ ‖z‖ → ‖z‖ ≤ 65*a →
          D.barrier (A' z-planePair (sphereFromPlaneFunction D.p (b i))
            (sphereFromPlaneFunction D.q (b i))) = 0) ∧
      (∀ i, ∃ W : DeGiorgi.MemW1pWitness 2 (fun x => D.barrier
        (planePair (D.p x) (D.q x)-planePair (sphereFromPlaneFunction D.p (b i))
          (sphereFromPlaneFunction D.q (b i))))
        (physicalPlaneDomain G ∩ ball 0 (65*a)),
        (eLpNorm W.weakGrad 2 (volume.restrict (physicalPlaneDomain G ∩ ball 0 (65*a)))).toReal < η) := by
  have hplateau : ∀ y : EuclideanPlane, ‖y‖ ≤ D.radius/2 → D.barrier y = 1 := by
    intro y hy
    exact D.barrier_one y (mem_ball_zero_iff.mpr (hy.trans_lt (half_lt_self D.radius_pos)))
  obtain ⟨n,J,γ,b,V,hcover,hb,hJD,hγ,hV⟩ := exists_stable_barrier_contours hsard hsch
    hG hinf hTD D.p D.q D.p_continuous D.q_continuous D.p_compact D.q_compact
    D.barrier (half_pos D.radius_pos) hplateau
    (fun z hz => (ball_subset_ball (show a ≤ 64*a by linarith)) (hBa hz))
  refine ⟨n,J,γ,b,V,hcover,hb,hJD,hγ,?_,?_,fun i => D.small_energy _⟩
  · intro i
    refine ⟨(hV i).1,(hV i).2.1,?_⟩
    intro A' hA
    apply (hV i).2.2 A'
    simpa only [show D.radius/2/4 = D.radius/8 by ring] using hA
  · intro i A' hchange z hz hz63 hz65
    have hc := D.trace_bound (b i) (hb i)
    have hz63' : 63*a ≤ ‖complexPlaneCoordinates.symm z‖ := by
      simpa only [← complexPlaneCoordinates_norm (complexPlaneCoordinates.symm z),
        complexPlaneCoordinates.apply_symm_apply] using hz63
    have hz65' : ‖complexPlaneCoordinates.symm z‖ ≤ 65*a := by
      simpa only [← complexPlaneCoordinates_norm (complexPlaneCoordinates.symm z),
        complexPlaneCoordinates.apply_symm_apply] using hz65
    have hm := D.outer_margin (complexPlaneCoordinates.symm z)
      (show complexPlaneCoordinates.symm z ∈ physicalPlaneDomain G from by
        simpa only [physicalPlaneDomain, mem_preimage, planeSphere,
          complexPlaneCoordinates.apply_symm_apply] using hz)
      hz63' hz65' _ hc
    have hc' := hchange z hz hz63 hz65
    have ht : ‖planePair (D.p (complexPlaneCoordinates.symm z)) (D.q (complexPlaneCoordinates.symm z))-
        planePair (sphereFromPlaneFunction D.p (b i)) (sphereFromPlaneFunction D.q (b i))‖ ≤
      ‖A' z-planePair (D.p (complexPlaneCoordinates.symm z)) (D.q (complexPlaneCoordinates.symm z))‖+
      ‖A' z-planePair (sphereFromPlaneFunction D.p (b i)) (sphereFromPlaneFunction D.q (b i))‖ := by
      have h := norm_add_le
        (planePair (D.p (complexPlaneCoordinates.symm z)) (D.q (complexPlaneCoordinates.symm z))-A' z)
        (A' z-planePair (sphereFromPlaneFunction D.p (b i)) (sphereFromPlaneFunction D.q (b i)))
      simpa only [sub_add_sub_cancel, norm_sub_rev _ (A' z)] using h
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    have hlt := mem_ball_zero_iff.mp (D.barrier_support hs)
    linarith

end CircleDomainRigidity

end

end OAI
