import OAI.Analysis.CircleDomains.Topology.SphericalGridPreparation
import OAI.Analysis.CircleDomains.Uniformization.FiniteCompletion

namespace OAI

/-!
# Keeping the selected physical core away from all terminal disks

A closed planar core extends across infinity to a compact spherical
core. Its quotient image is disjoint from the quotient dust. Thus the
terminal and filling neighborhoods can be chosen away from the entire
retained core. Compact planar tail pieces suffice for the metric step.
-/

open Set Filter Function Metric
open scoped Topology ContDiff

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def sphericalCore (K : Set (ℝ × ℝ)) : Set Sphere :=
  (((↑) : ℂ → Sphere) '' (Complex.equivRealProdCLM ⁻¹' Kᶜ))ᶜ

@[simp] theorem coe_mem_sphericalCore (K : Set (ℝ × ℝ)) (z : ℂ) :
    (z : Sphere) ∈ sphericalCore K ↔ Complex.equivRealProdCLM z ∈ K := by
  simp [sphericalCore, OnePoint.coe_injective.mem_set_image]

@[simp] theorem infty_mem_sphericalCore (K : Set (ℝ × ℝ)) :
    OnePoint.infty ∈ sphericalCore K := by
  simp [sphericalCore]

theorem isCompact_sphericalCore {K : Set (ℝ × ℝ)} (hK : IsClosed K) :
    IsCompact (sphericalCore K) := by
  apply IsClosed.isCompact
  exact (OnePoint.isOpen_image_coe.mpr
    (hK.isOpen_compl.preimage Complex.equivRealProdCLM.continuous)).isClosed_compl

theorem sphericalCore_subset_domain
    {G : Set Sphere} {K : Set (ℝ × ℝ)} (hinfty : OnePoint.infty ∈ G)
    (hKG : ∀ z : ℂ, Complex.equivRealProdCLM z ∈ K → (z : Sphere) ∈ G) :
    sphericalCore K ⊆ G := by
  intro x hx
  cases x using OnePoint.rec with
  | infty => exact hinfty
  | coe z => exact hKG z ((coe_mem_sphericalCore K z).mp hx)

/-- The quotient image of any retained physical core misses every
collapsed complementary component. -/
theorem quotient_core_disjoint_dust
    {G C : Set Sphere} (π : Sphere → Sphere) (hCG : C ⊆ G)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    Disjoint (π '' C) (π '' Gᶜ) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
  rcases (hr x y).mp heq.symm with hxy | hxG
  · exact hy (hxy ▸ hCG hx)
  · exact hxG.1 (hCG hx)

/-- The complement of the compact quotient image is an open neighborhood
of all dust points, whose full physical preimage avoids the core. -/
theorem quotient_core_safe_open
    {G C : Set Sphere} (π : Sphere → Sphere) (hπ : Continuous π)
    (hC : IsCompact C) (hCG : C ⊆ G)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    IsOpen (π '' C)ᶜ ∧ π '' Gᶜ ⊆ (π '' C)ᶜ ∧
      Disjoint (π ⁻¹' (π '' C)ᶜ) C := by
  refine ⟨(hC.image hπ).isClosed.isOpen_compl, ?_, ?_⟩
  · exact Set.disjoint_left.mp (quotient_core_disjoint_dust π hCG hr).symm
  · exact Set.disjoint_left.mpr (fun x hx hc => hx ⟨x, hc, rfl⟩)

/-- Actual terminal disks in the prescribed quotient neighborhoods avoid
the retained core, including their boundaries. -/
theorem PhysicalTerminalDisks.closure_disjoint_core
    {I : Type*} {G B C : Set Sphere} {π : Sphere → Sphere}
    {p : I → Sphere} {O : I → Set Sphere} (D : PhysicalTerminalDisks G π B p O)
    (hO : ∀ i, O i ⊆ (π '' C)ᶜ) (i : I) :
    Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (D.H i))) C := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨z, hz, rfl⟩ hc
  exact hO i (D.closure_subset i hz) ⟨(z : Sphere), hc, rfl⟩

theorem PhysicalTerminalDisks.core_subset_completedRegion
    {I : Type*} {G B C : Set Sphere} {π : Sphere → Sphere}
    {p : I → Sphere} {O : I → Set Sphere} (D : PhysicalTerminalDisks G π B p O)
    (hO : ∀ i, O i ⊆ (π '' C)ᶜ) : C ⊆ completedRegion D.H := by
  intro x hx hterminal
  obtain ⟨i, hi⟩ := mem_iUnion.mp hterminal
  obtain ⟨z, hz, rfl⟩ := hi
  exact Set.disjoint_left.mp (D.closure_disjoint_core hO i) ⟨z, subset_closure hz, rfl⟩ hx

/-- The two standard descriptions of quotient dust agree for the
actual component-collapse map. -/
theorem quotient_dust_eq_compl_image
    {G : Set Sphere} (π : Sphere → Sphere) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x)) :
    π '' Gᶜ = (π '' G)ᶜ := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩ ⟨z, hz, heq⟩
    rcases (hr z x).mp heq with hzx | hzG
    · exact hx (hzx ▸ hz)
    · exact hzG.1 hz
  · intro hy
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨x, fun hx => hy ⟨x, hx, rfl⟩, rfl⟩

/-- Construct the actual terminal disks in arbitrary prescribed
neighborhoods and automatically keep their closed caps off the retained
core. Including infinity in the core also excludes the infinity fiber
without an additional assumption on the selected indices. -/
theorem exists_physical_terminals_avoiding_core
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : Type*} [Fintype I] {G C : Set Sphere} (hG : IsOpen G)
    (π : Sphere → Sphere) (hπ : Continuous π) (hclosed : IsClosedMap π) (hsurj : Surjective π)
    (hr : ∀ x y, π x = π y ↔
      x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (hTD : IsTotallyDisconnected (π '' Gᶜ)) (hC : IsCompact C) (hCG : C ⊆ G)
    (hinfty : OnePoint.infty ∈ C) (p : I → Sphere) (hp : Injective p)
    (hpB : ∀ i, p i ∈ π '' Gᶜ) (O : I → Set Sphere) (hO : ∀ i, O i ∈ 𝓝 (p i)) :
    ∃ D : PhysicalTerminalDisks G π (π '' Gᶜ) p O,
      ∀ i, Disjoint (((↑) : ℂ → Sphere) '' closure (jordanInterior (D.H i))) C := by
  have hs := quotient_core_safe_open π hπ hC hCG hr
  let O' : I → Set Sphere := fun i => O i ∩ (π '' C)ᶜ
  have hO' (i : I) : O' i ∈ 𝓝 (p i) :=
    inter_mem (hO i) (hs.1.mem_nhds (hs.2.1 (hpB i)))
  have hpinfty (i : I) : p i ≠ π OnePoint.infty := by
    intro heq
    exact hs.2.1 (hpB i) (heq ▸ (show π OnePoint.infty ∈ π '' C from
      ⟨OnePoint.infty, hinfty, rfl⟩))
  obtain ⟨D⟩ := exists_disjoint_physical_terminal_disks hsard hschoenflies
    G π hπ hclosed hsurj hr (hG.isClosed_compl.isCompact.image hπ).isClosed hTD
    (fun x hx => ⟨x, hx, rfl⟩) p hp hpB hpinfty O' hO'
  let E : PhysicalTerminalDisks G π (π '' Gᶜ) p O :=
    { D with closure_subset := fun i z hz => (D.closure_subset i hz).1 }
  exact ⟨E, fun i => D.closure_disjoint_core (fun _ _ hz => hz.2) i⟩

/-- For a core containing a neighborhood of infinity the entire tail
integral can be computed on one compact part of the finite chart. -/
theorem exists_compact_tail_piece
    {Q K : Set (ℝ × ℝ)} (hQ : IsClosed Q) (hK : IsCompact (closure Kᶜ)) :
    ∃ R : ℝ, 0 < R ∧ IsCompact (Q ∩ closedBall 0 R) ∧
      Q \ K = (Q ∩ closedBall 0 R) \ K := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  refine ⟨R, hR, (isCompact_closedBall (0 : ℝ × ℝ) R).of_isClosed_subset
    (hQ.inter isClosed_closedBall) inter_subset_right, ?_⟩
  ext z
  constructor
  · intro hz
    refine ⟨⟨hz.1, ?_⟩, hz.2⟩
    apply ball_subset_closedBall
    simpa only [mem_ball, dist_zero_right] using hbound z (subset_closure hz.2)
  · exact fun hz => ⟨hz.1.1, hz.2⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
