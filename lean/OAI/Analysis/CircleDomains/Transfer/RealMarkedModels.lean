import OAI.Analysis.CircleDomains.Topology.RealModelExhaustion
import OAI.Analysis.CircleDomains.Modulus.NormalizedAssignedEnds

namespace OAI

/-! Assign the actual countable real-model terminals to their original source ends. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer

def CountableRealCoordinates.sourceMark {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} (d : CountableRealCoordinates G π σ) (s : S) : Sphere :=
  Classical.choose (d.labels_dust s)

theorem CountableRealCoordinates.sourceMark_outside
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (d : CountableRealCoordinates G π σ) (s : S) : d.sourceMark s ∈ Gᶜ :=
  (Classical.choose_spec (d.labels_dust s)).1

theorem CountableRealCoordinates.sourceMark_image
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (d : CountableRealCoordinates G π σ) (s : S) : π (d.sourceMark s) = σ s :=
  (Classical.choose_spec (d.labels_dust s)).2

theorem CountableRealCoordinates.sourceMark_component
    {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    (d : CountableRealCoordinates G π σ)
    (hr : ∀ x y, π x = π y ↔ x = y ∨ (x ∈ Gᶜ ∧ y ∈ connectedComponentIn Gᶜ x))
    (s : S) : connectedComponentIn Gᶜ (d.sourceMark s) = π ⁻¹' {σ s} := by
  ext x
  constructor
  · intro hx
    have he := (hr (d.sourceMark s) x).mpr (Or.inr ⟨d.sourceMark_outside s, hx⟩)
    exact he.symm.trans (d.sourceMark_image s)
  · intro hx
    have he : π (d.sourceMark s) = π x := (d.sourceMark_image s).trans hx.symm
    rcases (hr (d.sourceMark s) x).mp he with h | h
    · exact h ▸ mem_connectedComponentIn (d.sourceMark_outside s)
    · exact h.2

namespace RealModelExhaustion

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  (M : RealModelExhaustion d O ε)

def markIndex (n : ℕ) (s : S) : (M.stages n).indices := by
  classical
  exact if h : s ∈ (M.stages n).indices then ⟨s, h⟩
  else ⟨Classical.choose (M.indices_nonempty n ⟨s⟩),
    Classical.choose_spec (M.indices_nonempty n ⟨s⟩)⟩

theorem eventually_markIndex (s : S) :
    ∀ᶠ n in atTop, (M.markIndex n s : S) = s := by
  classical
  filter_upwards [M.marks s] with n hn
  simp [markIndex, hn]

theorem eventually_sourceMark_captured (s : S) :
    ∀ᶠ n in atTop, d.sourceMark s ∈
      closedTerminalCap ((M.stages n).terminals.H (M.markIndex n s)) := by
  have hinf : OnePoint.infty ∈ G :=
    M.core_source 0 (M.plane_core 0 (Or.inr rfl))
  have hq : d.sourceMark s ≠ OnePoint.infty := by
    intro he
    exact d.sourceMark_outside s (he ▸ hinf)
  obtain ⟨z, hz⟩ := OnePoint.ne_infty_iff_exists.mp hq
  filter_upwards [M.eventually_markIndex s] with n hn
  refine ⟨z, subset_closure ((M.stages n).terminals.fiber_subset (M.markIndex n s) ?_), hz⟩
  change π (z : Sphere) = σ (M.markIndex n s)
  rw [hn, hz]
  exact d.sourceMark_image s

theorem eventually_marked_cap_subset (s : S) {W : Set Sphere}
    (hO : ∀ᶠ n in atTop, O n s ⊆ W) :
    ∀ᶠ n in atTop, closedTerminalCap ((M.stages n).terminals.H (M.markIndex n s)) ⊆
      π ⁻¹' W := by
  filter_upwards [M.eventually_markIndex s, hO] with n hn hOn
  rintro p ⟨z, hz, rfl⟩
  have h := (M.stages n).terminals.closure_subset (M.markIndex n s) hz
  change π (z : Sphere) ∈ O n (M.markIndex n s) at h
  rw [hn] at h
  exact hOn h

end RealModelExhaustion

structure AssignedRealModelLimit {S : Type*} {G : Set Sphere} {π : Sphere → Sphere}
    {σ : S → Sphere} {d : CountableRealCoordinates G π σ}
    {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ} (M : RealModelExhaustion d O ε) where
  assignment : ∀ n, TerminalComponentAssignment (M.stages n).terminals.H
    (M.stages n).forward (M.stages n).domain
  subsequence : ℕ → ℕ
  function : ℂ → ℂ
  center : S → ℂ
  radius : S → ℝ
  cores : ℕ → SmoothJordanCore G
  contours : ∀ j, Fin (cores j).count → ℂ ≃ₜ ℂ
  strict : StrictMono subsequence
  converges : TendstoLocallyUniformlyOn (fun n (z : ℂ) =>
    finiteCoord ((M.stages (subsequence n)).forward (z : Sphere))) function
    atTop (((↑) : ℂ → Sphere) ⁻¹' G)
  normalized : IsPrincipalNormalized (extendAtInfinity function)
  conformal : IsConformalEquivalence (extendAtInfinity function) G (extendAtInfinity function '' G)
  bounds : ∀ s, ‖center s‖ ≤ 3 * M.radius ∧ radius s ∈ Icc 0 (3 * M.radius)
  nested : ∀ j, (cores j).carrier ⊆ interior (cores (j + 1)).carrier
  exhausts : (⋃ j, interior (cores j).carrier) = G
  boundary : ∀ j i, extendAtInfinity function ''
    (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((cores j).disk i))) =
    ((↑) : ℂ → Sphere) '' frontier (jordanInterior (contours j i))
  disjoint : ∀ j, Pairwise (Disjoint on fun i => closure (jordanInterior (contours j i)))
  image_core : ∀ j, (extendAtInfinity function '' (cores j).carrier)ᶜ =
    ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (contours j i)
  side : ∀ j i, extendAtInfinity function ''
    (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior ((cores j).disk i))) =
    (extendAtInfinity function '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior (contours j i))
  marked : ∀ s, ∃ (index : ∀ j, Fin (cores j).count) (p : Sphere),
    p ∈ (extendAtInfinity function '' G)ᶜ ∧
    connectedComponentIn Gᶜ (d.sourceMark s) = ⋂ j, closedTerminalCap ((cores j).disk (index j)) ∧
    connectedComponentIn (extendAtInfinity function '' G)ᶜ p =
      ⋂ j, closedTerminalCap (contours j (index j)) ∧
    ((↑) : ℂ → Sphere) '' closedBall (center s) (radius s) ⊆
      connectedComponentIn (extendAtInfinity function '' G)ᶜ p ∧
    Tendsto (fun n => hausdorffDist
      (finiteCoord '' connectedComponentIn (M.stages (subsequence n)).domainᶜ
        ((assignment (subsequence n)).point (M.markIndex (subsequence n) s)))
      (closedBall (center s) (radius s))) atTop (𝓝 0)

theorem RealModelExhaustion.exists_assigned_limit
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies)
    {S : Type*} [Countable S] {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
    (M : RealModelExhaustion d O ε) (hG : IsOpen G) (hconn : IsConnected G) :
    Nonempty (AssignedRealModelLimit M) := by
  let _ : ∀ n, Fintype (M.stages n).indices := fun n => (M.stages n).finite_indices.fintype
  obtain ⟨a, s, F, c, r, C, J, hs, hl, hn, he, hb, hnest, hcover, hboundary,
      hdisj, himage, hside, hmark⟩ :=
    exists_normalized_limit_with_assigned_ends harea hmontel hhurwitz hzero hsard hsch
      (fun n => (M.stages n).terminals.H) (fun n => (M.stages n).terminals.disjoint_closures)
      (fun n => (M.stages n).forward) (fun n => (M.stages n).inverse)
      (fun n => (M.stages n).domain) (fun n => (M.stages n).equivalence)
      (fun n => (M.stages n).circle_domain) M.plane_open M.plane_connected M.plane_monotone
      (fun n z hz => M.core_model n (M.plane_core n (Or.inl ⟨z, hz, rfl⟩)))
      (fun n => (M.core_conformal n).mono (fun _ hp => M.plane_core n (Or.inl hp)))
      M.radius_pos (fun n => (M.exterior_core n).trans (M.core_model n))
      (fun n => (M.core_conformal n).mono
        ((compl_subset_compl.mpr (image_mono ball_subset_closedBall)).trans (M.exterior_core n)))
      (fun n => (M.stages n).principal) M.exterior_plane hG hconn M.exhausts
      d.sourceMark d.sourceMark_outside M.markIndex M.eventually_sourceMark_captured
  exact ⟨⟨a, s, F, c, r, C, J, hs, hl, hn, he, hb, hnest, hcover, hboundary,
    hdisj, himage, hside, hmark⟩⟩

end CircleDomainRigidity.FiniteTransfer

end

end OAI
