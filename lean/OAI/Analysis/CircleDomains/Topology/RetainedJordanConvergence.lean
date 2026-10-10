import OAI.Analysis.CircleDomains.Selection.PrescribedMarkedEnds
import OAI.Analysis.CircleDomains.Topology.JordanCrossingStability

namespace OAI

/-!
# Anchors for the Jordan curves of actual finite models

A point of the physical domain on the inside of a retained contour gives
an interior anchor in every sufficiently late model. The proved side
correspondence identifies that side, and local uniform convergence gives
the anchor and boundary convergence needed for the crossing argument.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_domain_point_inside_jordan
    {G : Set Sphere} (hG : IsOpen G) (H : ℂ ≃ₜ ℂ)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) :
    ∃ q : ℂ, (q : Sphere) ∈ G ∧ q ∈ jordanInterior H := by
  obtain ⟨p, hp⟩ := (isConnected_frontier_jordanInterior H).nonempty
  have hpG : p ∈ ((↑) : ℂ → Sphere) ⁻¹' G := hboundary ⟨p, hp, rfl⟩
  exact mem_closure_iff_nhds.mp (frontier_subset_closure hp)
    (((↑) : ℂ → Sphere) ⁻¹' G) ((hG.preimage OnePoint.continuous_coe).mem_nhds hpG)

theorem exists_anchored_retained_jordan_models
    (hsch : PlanarSchoenflies)
    {I : ℕ → Type*} [∀ n, Finite (I n)] (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (hTd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (T n i))))
    (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hV : ∀ n, IsOpen (V n)) (hfix : ∀ n, f n OnePoint.infty = OnePoint.infty)
    {G : Set Sphere} (hG : IsOpen G) (A : SmoothJordanCore G) (j : Fin A.count)
    (hret : ∀ᶠ n in atTop, A.carrier ⊆ openCompletedRegion (T n))
    (hpoint : ∀ q ∈ G, ∀ᶠ n in atTop, q ∈ openCompletedRegion (T n))
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f n (z : Sphere)))
      F atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (H : ℂ ≃ₜ ℂ)
    (hH : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk j))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior H))
    (hside : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk j))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior H)) :
    ∃ (J : ℕ → ℂ ≃ₜ ℂ) (q : ℂ),
      (q : Sphere) ∈ G ∧ q ∈ jordanInterior (A.disk j) ∧ F q ∈ jordanInterior H ∧
      Continuous (F ∘ A.curve j) ∧
      range (F ∘ A.curve j) = frontier (jordanInterior H) ∧
      TendstoUniformly (fun n s => finiteCoord (f n ((A.curve j s : ℂ) : Sphere)))
        (F ∘ A.curve j) atTop ∧
      Tendsto (fun n => finiteCoord (f n (q : Sphere))) atTop (𝓝 (F q)) ∧
      (∀ᶠ n in atTop, finiteCoord (f n (q : Sphere)) ∈ jordanInterior (J n)) ∧
      (∀ᶠ n in atTop,
        f n '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk j))) =
          ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J n))) ∧
      (∀ᶠ n in atTop, range (fun s => finiteCoord (f n ((A.curve j s : ℂ) : Sphere))) =
        frontier (jordanInterior (J n))) := by
  classical
  have hinf (n : ℕ) : OnePoint.infty ∈ openCompletedRegion (T n) := by
    intro h
    obtain ⟨i, z, _, hz⟩ := mem_iUnion.mp h
    exact OnePoint.coe_ne_infty z hz
  have hex (n : ℕ) : ∃ J : Fin A.count → ℂ ≃ₜ ℂ,
      A.carrier ⊆ openCompletedRegion (T n) →
      (∀ i, f n '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J i))) ∧
      ∀ i, f n '' (openCompletedRegion (T n) ∩
          (((↑) : ℂ → Sphere) '' jordanInterior (A.disk i))) =
        (f n '' openCompletedRegion (T n)) ∩
          (((↑) : ℂ → Sphere) '' jordanInterior (J i)) := by
    by_cases hn : A.carrier ⊆ openCompletedRegion (T n)
    · obtain ⟨J, _, _, hb, hs⟩ := exists_matched_image_core_of_continuous_open hsch
        (isOpen_openCompletedRegion (T n)) (isConnected_openCompletedRegion (T n) (hTd n))
        (hinf n) (fun p hp => ((heq n).smooth p hp).1.continuousWithinAt)
        (fun S hS hSQ => (heq n).isOpen_image (hV n) hS hSQ)
        (heq n).bijOn.injOn (hfix n) (A.inDomain hn)
      exact ⟨J, fun _ => ⟨hb, hs⟩⟩
    · exact ⟨fun _ => H, fun h => (hn h).elim⟩
  choose J hJ using hex
  obtain ⟨q, hqG, hqA⟩ := exists_domain_point_inside_jordan hG (A.disk j)
    (A.boundary_subset_domain j)
  have hqH : F q ∈ jordanInterior H := by
    have hq : extendAtInfinity F (q : Sphere) ∈
        (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior H) := by
      rw [← hside]
      exact mem_image_of_mem _ ⟨hqG, q, hqA, rfl⟩
    simpa only [extendAtInfinity_coe, OnePoint.coe_injective.mem_set_image] using hq.2
  have hcurveG (s : Circle) : ((A.curve j s : ℂ) : Sphere) ∈ G := by
    apply A.boundary_subset_domain j
    exact ⟨A.curve j s, (A.boundary j) ▸ mem_range_self s, rfl⟩
  have hγ : Continuous (A.curve j) := (A.embedding j).continuous
  have hγF : Continuous (F ∘ A.curve j) := hF.comp_continuous hγ hcurveG
  have hfront : range (F ∘ A.curve j) = frontier (jordanInterior H) := by
    simpa only [extendAtInfinity_coe, finiteCoord_coe, Function.comp_def] using
      range_finite_image_boundary (A.boundary j) hH
        (fun s => by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
  have hγlim : TendstoUniformly
      (fun n s => finiteCoord (f n ((A.curve j s : ℂ) : Sphere))) (F ∘ A.curve j) atTop := by
    apply tendstoUniformlyOn_univ.mp
    apply (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact isCompact_univ).mp
    exact hlim.comp (A.curve j) (fun s _ => hcurveG s) hγ.continuousOn
  refine ⟨fun n => J n j, q, hqG, hqA, hqH, hγF, hfront, hγlim,
    hlim.tendsto_at hqG, ?_, ?_, ?_⟩
  · filter_upwards [hret, hpoint (q : Sphere) hqG] with n hn hqn
    have ht : f n (q : Sphere) ∈ ((↑) : ℂ → Sphere) '' jordanInterior (J n j) := by
      have hh := mem_image_of_mem (f n) (show (q : Sphere) ∈
        openCompletedRegion (T n) ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk j)) from
          ⟨hqn, q, hqA, rfl⟩)
      rw [(hJ n hn).2 j] at hh
      exact hh.2
    obtain ⟨r, hr, her⟩ := ht
    simpa only [← her, finiteCoord_coe] using hr
  · filter_upwards [hret] with n hn
    exact (hJ n hn).1 j
  · filter_upwards [hret] with n hn
    apply range_finite_image_boundary (A.boundary j) ((hJ n hn).1 j)
    intro s
    exact (heq n).finite_forward (hinf n) (hfix n)
      ((A.inDomain hn).boundary_subset_domain j
        ⟨A.curve j s, (A.boundary j) ▸ mem_range_self s, rfl⟩)

end CircleDomainRigidity

end

end OAI
