import OAI.Analysis.CircleDomains.Selection.FiniteMarkedTrapping

namespace OAI

/-!
# Inverse images approach the assigned terminal boundary

A target sequence approaching an assigned complementary component has
preimages eventually in every neighborhood of the corresponding physical
terminal boundary. Compactness and the proved component assignment replace
any assumption of a boundary extension of the uniformizing map.
-/

open Set Function Filter
open scoped Topology

namespace CircleDomainRigidity

open FiniteTransfer

instance sphereFirstCountableTopology : FirstCountableTopology Sphere :=
  (onePointEquivSphereOfFinrankEq (V := ℂ) (ι := Fin 3) (by simp)).isEmbedding.firstCountableTopology

theorem TerminalComponentAssignment.source_cluster_mem_boundary
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    {i : I} {q y : Sphere} (hy : y ∈ connectedComponentIn Vᶜ (a.point i))
    {x : ℕ → Sphere} (hx : Tendsto x atTop (𝓝 q))
    (hxQ : ∀ᶠ n in atTop, x n ∈ openCompletedRegion T)
    (hfx : Tendsto (f ∘ x) atTop (𝓝 y)) :
    q ∈ ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)) := by
  have hyout : y ∈ Vᶜ := connectedComponentIn_subset _ _ hy
  have hqout : q ∉ openCompletedRegion T := by
    intro hq
    have hflim := ((hf.smooth q hq).1.tendsto).comp hx
    have heq : y = f q := tendsto_nhds_unique hfx hflim
    exact hyout (heq.symm ▸ hf.mapsTo hq)
  have hqunion : q ∈ ⋃ j, closedTerminalCap (T j) := not_not.mp hqout
  obtain ⟨j, hqj⟩ := mem_iUnion.mp hqunion
  have hyj := a.cluster j q hqj x hx hxQ y hfx
  have hji : j = i := by
    by_contra hne
    exact Set.disjoint_left.mp (a.disjoint hne) hyj hy
  subst j
  have hQavoid : openCompletedRegion T ⊆ (closedTerminalCap (T i))ᶜ := by
    intro z hz hzi
    exact hz (mem_iUnion.mpr ⟨i, hzi⟩)
  have hqclosure : q ∈ closure (openCompletedRegion T) := mem_closure_of_tendsto hx hxQ
  have hqnot : q ∉ interior (closedTerminalCap (T i)) := by
    change q ∈ (interior (closedTerminalCap (T i)))ᶜ
    simpa only [closure_compl] using closure_mono hQavoid hqclosure
  obtain ⟨z, hz, rfl⟩ := hqj
  refine ⟨z, ?_, rfl⟩
  rw [(jordanInterior_isOpen (T i)).frontier_eq]
  refine ⟨hz, ?_⟩
  intro hzi
  apply hqnot
  rw [interior_closedTerminalCap]
  exact mem_image_of_mem _ hzi

theorem TerminalComponentAssignment.inverse_eventually_near_boundary
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    {i : I} {y : Sphere} (hy : y ∈ connectedComponentIn Vᶜ (a.point i))
    {yn : ℕ → Sphere} (hyn : Tendsto yn atTop (𝓝 y))
    (hynV : ∀ᶠ n in atTop, yn n ∈ V)
    {O : Set Sphere} (hO : IsOpen O)
    (hboundary : ((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)) ⊆ O) :
    ∀ᶠ n in atTop, fi (yn n) ∈ O := by
  by_contra hnot
  have hfreq : ∃ᶠ n in atTop, fi (yn n) ∈ Oᶜ := not_eventually.mp hnot
  obtain ⟨q, hq, s, hs, hqs⟩ := hO.isClosed_compl.isCompact.tendsto_subseq' hfreq
  have hxQ : ∀ᶠ n in atTop, fi (yn (s n)) ∈ openCompletedRegion T := by
    filter_upwards [hs.tendsto_atTop hynV] with n hn
    exact hf.mapsTo_inv hn
  have hfn : (fun n => f (fi (yn (s n)))) =ᶠ[atTop] (yn ∘ s) := by
    filter_upwards [hs.tendsto_atTop hynV] with n hn
    exact hf.right_inv _ hn
  have hfqs : Tendsto (fun n => f (fi (yn (s n)))) atTop (𝓝 y) :=
    (hyn.comp hs.tendsto_atTop).congr' hfn.symm
  exact hq (hboundary (a.source_cluster_mem_boundary hf hy hqs hxQ hfqs))

theorem TerminalComponentAssignment.inverse_tendsto_boundary
    {I : Type*} {T : I → ℂ ≃ₜ ℂ} {f fi : Sphere → Sphere} {V : Set Sphere}
    (a : TerminalComponentAssignment T f V)
    (hf : IsSmoothSphereEquivalence f fi (openCompletedRegion T) V)
    {i : I} {y : Sphere} (hy : y ∈ connectedComponentIn Vᶜ (a.point i))
    {yn : ℕ → Sphere} (hyn : Tendsto yn atTop (𝓝 y))
    (hynV : ∀ᶠ n in atTop, yn n ∈ V) :
    Tendsto (fi ∘ yn) atTop
      (𝓝ˢ (((↑) : ℂ → Sphere) '' frontier (jordanInterior (T i)))) := by
  rw [tendsto_def]
  intro s hs
  obtain ⟨O, hO, hAO, hOs⟩ := mem_nhdsSet_iff_exists.mp hs
  exact (a.inverse_eventually_near_boundary hf hy hyn hynV hO hAO).mono
    (fun _ hn => hOs hn)

end CircleDomainRigidity

end OAI
