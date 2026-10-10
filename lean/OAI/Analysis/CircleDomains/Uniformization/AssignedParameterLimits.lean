import OAI.Analysis.CircleDomains.Selection.PrescribedMarkedEnds
import OAI.Analysis.CircleDomains.Topology.CompactCoreRetention

namespace OAI

/-!
# Normalized finite models retaining marked disk parameters

This assembles the published normal-family inputs, the constructed finite
terminal assignment, the actual smooth Jordan exhaustion, and marked-disk
trapping. Every marked limit is attached to its source component.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem exists_normalized_limit_with_assigned_parameters
    (harea : ExteriorCoefficientAreaTheorem)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit)
    (hzero : HurwitzZeroFreeLimit)
    (hsard : SmoothPlanarSard) (hschoenflies : PlanarSchoenflies)
    {I : ℕ → Type*} [∀ n, Finite (I n)] (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (hTd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (T n i))))
    (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hV : ∀ n, IsCircleDomain (V n))
    {D : ℕ → Set ℂ} (hD : ∀ n, IsOpen (D n))
    (hconn : ∀ n, IsConnected (D n)) (hmono : Monotone D)
    (hDQ : ∀ n z, z ∈ D n → (z : Sphere) ∈ openCompletedRegion (T n))
    (hcore : ∀ n, IsConformalOn (f n) (((↑) : ℂ → Sphere) '' D n))
    {R : ℝ} (hR : 0 < R)
    (hsource : ∀ n, ((((↑) : ℂ → Sphere) '' ball 0 R)ᶜ) ⊆ openCompletedRegion (T n))
    (hconf : ∀ n, IsConformalOn (f n)
      ((((↑) : ℂ → Sphere) '' closedBall 0 R)ᶜ))
    (hnorm : ∀ n, IsPrincipalNormalized (f n))
    (hext : {z : ℂ | 2 * R ≤ ‖z‖} ⊆ D 0)
    {G : Set Sphere} (hG : IsOpen G) (hGc : IsConnected G)
    (hGdef : ((↑) : ℂ → Sphere) '' (⋃ n, D n) ∪ {OnePoint.infty} = G)
    {B : Type*} [Countable B] (q : B → Sphere) (hq : ∀ b, q b ∈ Gᶜ)
    (t : (n : ℕ) → B → I n)
    (hmark : ∀ b, ∀ᶠ n in atTop, q b ∈ closedTerminalCap (T n (t n b))) :
    ∃ (a : ∀ n, TerminalComponentAssignment (T n) (f n) (V n))
      (s : ℕ → ℕ) (F : ℂ → ℂ) (c : B → ℂ) (r : B → ℝ)
      (C : ℕ → SmoothJordanCore G) (J : (j : ℕ) → Fin (C j).count → ℂ ≃ₜ ℂ),
      StrictMono s ∧
      TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f (s n) (z : Sphere))) F
        atTop (((↑) : ℂ → Sphere) ⁻¹' G) ∧
      IsPrincipalNormalized (extendAtInfinity F) ∧
      IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G) ∧
      (∀ b, ‖c b‖ ≤ 3 * R ∧ r b ∈ Icc 0 (3 * R)) ∧
      (∀ j, (C j).carrier ⊆ interior (C (j + 1)).carrier) ∧
      (⋃ j, interior (C j).carrier) = G ∧
      (∀ j i, extendAtInfinity F ''
        (((↑) : ℂ → Sphere) '' frontier (jordanInterior ((C j).disk i))) =
        ((↑) : ℂ → Sphere) '' frontier (jordanInterior (J j i))) ∧
      (∀ j, Pairwise (Disjoint on fun i => closure (jordanInterior (J j i)))) ∧
      (∀ j, (extendAtInfinity F '' (C j).carrier)ᶜ =
        ⋃ i, ((↑) : ℂ → Sphere) '' jordanInterior (J j i)) ∧
      (∀ j i, extendAtInfinity F '' (G ∩
        (((↑) : ℂ → Sphere) '' jordanInterior ((C j).disk i))) =
        (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior (J j i))) ∧
      (∀ b, ∃ (d : (j : ℕ) → Fin (C j).count) (p : Sphere), p ∈ (extendAtInfinity F '' G)ᶜ ∧
        connectedComponentIn Gᶜ (q b) = ⋂ j, closedTerminalCap ((C j).disk (d j)) ∧
        connectedComponentIn (extendAtInfinity F '' G)ᶜ p = ⋂ j, closedTerminalCap (J j (d j)) ∧
        ((↑) : ℂ → Sphere) '' closedBall (c b) (r b) ⊆
          connectedComponentIn (extendAtInfinity F '' G)ᶜ p ∧
        Tendsto (fun n => hausdorffDist
          (finiteCoord '' connectedComponentIn (V (s n))ᶜ ((a (s n)).point (t (s n) b)))
          (closedBall (c b) (r b))) atTop (𝓝 0)) ∧
      ∃ (cn : ℕ → B → ℂ) (rn : ℕ → B → ℝ),
        (∀ n b, ‖cn n b‖ ≤ 3 * R ∧ rn n b ∈ Icc 0 (3 * R)) ∧
        (∀ b, ∀ᶠ n in atTop, connectedComponentIn (V (s n))ᶜ ((a (s n)).point (t (s n) b)) =
          ((↑) : ℂ → Sphere) '' closedBall (cn n b) (rn n b)) ∧
        (∀ b, Tendsto (fun n => cn n b) atTop (𝓝 (c b))) ∧
        (∀ b, Tendsto (fun n => rn n b) atTop (𝓝 (r b))) := by
  classical
  have hex (n : ℕ) : Nonempty (TerminalComponentAssignment (T n) (f n) (V n)) :=
    exists_terminal_component_assignment hsard hschoenflies (T n) (hTd n)
      (heq n) (hV n).1 (hnorm n).1
  let a (n : ℕ) := Classical.choice (hex n)
  obtain ⟨s, F, c, r, hs, hl, hn, he, hb, hh, _, cn, rn, hbn, hdisks, hc, hr⟩ :=
    exists_normalized_marked_sphere_limit_with_parameters harea hmontel hhurwitz hzero
      f fi (fun n => openCompletedRegion (T n)) V heq hV hD hconn hmono hDQ hcore
      hR hsource hconf hnorm hext (fun n b => (a n).point (t n b))
      (fun b => Eventually.of_forall fun n => (a n).outside (t n b))
  rw [hGdef] at he
  have hchart : ((↑) : ℂ → Sphere) ⁻¹' G = ⋃ n, D n := by
    rw [← hGdef]
    ext z
    simp
  rw [← hchart] at hl
  have hinf : OnePoint.infty ∈ G := hGdef ▸ Or.inr rfl
  have hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G) := by
    intro z hz
    have hh' := continuousAt_finite_part_of_conformalAt (he.1 _ hz)
      (by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
    simpa only [extendAtInfinity_coe, finiteCoord_coe] using hh'.continuousWithinAt
  obtain ⟨C, J, hstrict, hcover, hJd, hJe, hboundary, hside⟩ :=
    exists_matched_jordan_exhaustion hsard hschoenflies hG hGc hinf
      he.1 he.bijOn.injOn hn.1
  refine ⟨a, s, F, c, r, C, J, hs, hl, hn, he, hb, hstrict, hcover, hboundary,
    hJd, hJe, hside, ?_, cn, rn, hbn, hdisks, hc, hr⟩
  intro b
  obtain ⟨d, p, hp, hsrc, htgt, _⟩ := corresponding_target_end_of_source
    hG he.1 he.bijOn.injOn C J hstrict hcover hJd hJe hboundary hside (hq b)
  have hqd (j : ℕ) : q b ∈ ((↑) : ℂ → Sphere) '' jordanInterior ((C j).disk (d j)) := by
    apply (C j).omitted_point_mem_side (hq b)
    exact mem_iInter.mp (hsrc ▸ mem_connectedComponentIn (hq b)) j
  have hretain (j : ℕ) : ∀ᶠ n in atTop, (C j).carrier ⊆ openCompletedRegion (T (s n)) := by
    have hret := eventually_compact_subset_model hD hmono hDQ hsource (C j).isCompact
      ((C j).subset.trans (by rw [hGdef]))
    exact hs.tendsto_atTop hret
  refine ⟨d, p, hp, hsrc, htgt, ?_, hh b⟩
  exact marked_limit_subset_corresponding_component
    (fun n => T (s n)) (fun n => f (s n)) (fun n => fi (s n)) (fun n => V (s n))
    (fun n => a (s n)) (fun n => heq (s n)) (fun n => (hnorm (s n)).1)
    C d (fun j => J j (d j)) hretain (fun n => t (s n) b) hqd
    (hs.tendsto_atTop (hmark b)) F hF hl (fun j => hboundary j (d j)) htgt
    (fun n => (hbn n b).2.1) (hb b).2.1 (hc b) (hr b) (hdisks b)

end CircleDomainRigidity

end

end OAI
