import OAI.Analysis.CircleDomains.Transfer.GeometricCompletion
import OAI.Analysis.CircleDomains.Topology.CutoffCore
import OAI.Analysis.CircleDomains.Uniformization.FiniteCompletionUniformization

namespace OAI

/-!
# Terminal contours retaining the prescribed core and oscillation bounds

Intersect the prescribed quotient neighborhoods with the complement of the
core image before choosing terminal contours. This retains the uniform
staircase estimate, confines every terminal to its prescribed neighborhood,
and places the whole core in the open finite completion.
-/

open Set Function Filter
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

theorem PhysicalTerminalDisks.core_subset_openCompletedRegion
    {I : Type*} {G B C : Set Sphere} {π : Sphere → Sphere}
    {p : I → Sphere} {O : I → Set Sphere} (D : PhysicalTerminalDisks G π B p O)
    (havoid : ∀ i, Disjoint (closedTerminalCap (D.H i)) C) :
    C ⊆ openCompletedRegion D.H := by
  intro x hx hbad
  obtain ⟨i, hi⟩ := mem_iUnion.mp hbad
  exact Set.disjoint_left.mp (havoid i) hi hx

theorem exists_retained_physical_terminals_with_staircase_bound
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {I L : Type*} [Fintype I] [Fintype L]
    {G C : Set Sphere} (hG : IsOpen G) (hC : IsCompact C) (hCG : C ⊆ G)
    (hinfty : OnePoint.infty ∈ C)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π)
    (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ))
    (p : I → Sphere) (hp : Injective p) (hpB : ∀ i, p i ∈ π '' Gᶜ)
    (O : I → Set Sphere) (hO : ∀ i, O i ∈ 𝓝 (p i))
    (U : I → Set Sphere) (u : I → L → Sphere → ℝ) (M : I → L → ℝ)
    (hM : ∀ i l x, x ∈ U i → |u i l x| ≤ M i l)
    (hphysical : ∀ i (z : ℂ), (z : Sphere) ∈ G → π (z : Sphere) ∈ O i →
      π (z : Sphere) ∈ U i)
    (active : I → L → Prop) (c : I → L → ℝ)
    (hbudget : ∀ i l, active i l →
      limsup (u i l) (𝓝[U i] (p i)) - liminf (u i l) (𝓝[U i] (p i)) ≤ c i l)
    {h : ℝ} (hh : 0 < h) :
    ∃ D : PhysicalTerminalDisks G π (π '' Gᶜ) p O,
      (∀ i, Disjoint (closedTerminalCap (D.H i)) C) ∧
      C ⊆ openCompletedRegion D.H ∧
      ∀ i l, active i l → ∀ δ θ : ℝ,
        ∀ x ∈ frontier (jordanInterior (D.H i)),
        ∀ y ∈ frontier (jordanInterior (D.H i)),
        |shiftedStaircase h δ θ (u i l (π (x : Sphere))) -
          shiftedStaircase h δ θ (u i l (π (y : Sphere)))| ≤ c i l + 4 * h := by
  have hsafe := quotient_core_safe_open π hπ hC hCG hr
  let O' : I → Set Sphere := fun i => O i ∩ (π '' C)ᶜ
  have hO' (i : I) : O' i ∈ 𝓝 (p i) :=
    inter_mem (hO i) (hsafe.1.mem_nhds (hsafe.2.1 (hpB i)))
  have hpinfty (i : I) : p i ≠ π OnePoint.infty := by
    intro heq
    exact hsafe.2.1 (hpB i) (heq ▸ mem_image_of_mem π hinfty)
  obtain ⟨D, hosc⟩ := exists_physical_terminals_with_uniform_staircase_oscillation
    hsard hsch G π hπ hclosed hsurj hr
      (hG.isClosed_compl.isCompact.image hπ).isClosed hTD
      (fun x hx => mem_image_of_mem π hx) p hp hpB hpinfty O' hO' U u M hM
      (fun i z hz hzi => hphysical i z hz hzi.1) active c hbudget hh
  let D' : PhysicalTerminalDisks G π (π '' Gᶜ) p O :=
    { D with closure_subset := fun i z hz => (D.closure_subset i hz).1 }
  have havoid (i : I) : Disjoint (closedTerminalCap (D'.H i)) C :=
    D.closure_disjoint_core (fun _ _ hz => hz.2) i
  exact ⟨D', havoid, D'.core_subset_openCompletedRegion havoid, hosc⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
