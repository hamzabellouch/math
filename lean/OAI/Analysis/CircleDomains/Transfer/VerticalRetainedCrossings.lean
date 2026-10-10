import OAI.Analysis.CircleDomains.Transfer.RetainedTestCrossings
import OAI.Analysis.CircleDomains.Topology.VerticalFrontierCrossings

namespace OAI

/-! Retained target contours give crossing segments in the vertical direction. -/

open Set Function Filter Metric
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

theorem eventually_vertical_crossings_of_anchored_jordan_limits
    (H K : ℂ ≃ₜ ℂ) (Hn Kn : ℕ → ℂ ≃ₜ ℂ)
    (γ δ : Circle → ℂ) (γn δn : ℕ → Circle → ℂ)
    (hγ : Continuous γ) (hδ : Continuous δ)
    (hγfront : range γ = frontier (jordanInterior H))
    (hδfront : range δ = frontier (jordanInterior K))
    (hγn : ∀ᶠ n in atTop, range (γn n) = frontier (jordanInterior (Hn n)))
    (hδn : ∀ᶠ n in atTop, range (δn n) = frontier (jordanInterior (Kn n)))
    (hγlim : TendstoUniformly γn γ atTop) (hδlim : TendstoUniformly δn δ atTop)
    (hHK : closure (jordanInterior H) ⊆ jordanInterior K)
    {z w : ℂ} {zn wn : ℕ → ℂ}
    (hz : z ∈ jordanInterior H) (hw : w ∈ jordanInterior K)
    (hzn : Tendsto zn atTop (𝓝 z)) (hwn : Tendsto wn atTop (𝓝 w))
    (hzanchor : ∀ᶠ n in atTop, zn n ∈ jordanInterior (Hn n))
    (hwanchor : ∀ᶠ n in atTop, wn n ∈ jordanInterior (Kn n))
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ jordanInterior H)
    (D : ℕ → Set ℂ) (v : ℕ → ℂ → ℝ) {L : ℝ}
    (hbound : ∀ᶠ n in atTop, closure (jordanInterior (Kn n)) ⊆ closedBall 0 L)
    (hboundary : ∀ᶠ n in atTop, frontier (jordanInterior (Hn n)) ⊆ D n ∧
      frontier (jordanInterior (Kn n)) ⊆ D n)
    (hvalues : ∀ᶠ n in atTop,
      (∀ p ∈ frontier (jordanInterior (Kn n)), v n p = 0) ∧
      (∀ p ∈ frontier (jordanInterior (Hn n)), v n p = 1))
    {J : Set ℝ} (hJ : J ⊆ Complex.re '' C) :
    ∀ᶠ n in atTop, ∀ y ∈ J, ∃ a b : ℝ, a < b ∧ verticalLine y a ∈ D n ∧
      verticalLine y b ∈ D n ∧ verticalLine y a ∈ closedBall 0 L ∧
      verticalLine y b ∈ closedBall 0 L ∧ v n (verticalLine y a) = 0 ∧
      v n (verticalLine y b) = 1 := by
  have hretain := eventually_compact_subset_jordanInterior_of_anchor H Hn γ γn
    hγ hγfront hγn hγlim hz hzn hzanchor hC hCH
  have hnested := eventually_nested_jordanInteriors_of_anchor H K Hn Kn γ δ γn δn
    hγ hδ hγfront hδfront hγn hδn hγlim hδlim hHK hw hwn hwanchor
  filter_upwards [hretain, hnested, hbound, hboundary, hvalues] with n hnC hnested hnB hnD hnv
  apply vertical_frontier_crossings_give_values
    (jordanInterior_isOpen (Hn n)) (jordanInterior_isOpen (Kn n))
    (isCompact_closure_jordanInterior (Hn n)) (isCompact_closure_jordanInterior (Kn n))
    hnested hnB hnD.2 hnD.1 hnv.1 hnv.2
  exact hJ.trans (image_mono (hnC.trans subset_closure))

theorem eventually_vertical_crossings_of_retained_test
    (hsch : PlanarSchoenflies)
    {I : ℕ → Type*} [∀ n, Finite (I n)] (T : (n : ℕ) → I n → ℂ ≃ₜ ℂ)
    (hTd : ∀ n, Pairwise (Disjoint on fun i => closure (jordanInterior (T n i))))
    (f fi : ℕ → Sphere → Sphere) (V : ℕ → Set Sphere)
    (heq : ∀ n, IsSmoothSphereEquivalence (f n) (fi n) (openCompletedRegion (T n)) (V n))
    (hV : ∀ n, IsOpen (V n)) (hfix : ∀ n, f n OnePoint.infty = OnePoint.infty)
    {G : Set Sphere} (hG : IsOpen G)
    (A B : SmoothJordanCore G) (i : Fin A.count) (j : Fin B.count)
    (hretA : ∀ᶠ n in atTop, A.carrier ⊆ openCompletedRegion (T n))
    (hretB : ∀ᶠ n in atTop, B.carrier ⊆ openCompletedRegion (T n))
    (hpoint : ∀ q ∈ G, ∀ᶠ n in atTop, q ∈ openCompletedRegion (T n))
    (F : ℂ → ℂ) (hF : ContinuousOn F (((↑) : ℂ → Sphere) ⁻¹' G))
    (hlim : TendstoLocallyUniformlyOn (fun n (z : ℂ) => finiteCoord (f n (z : Sphere)))
      F atTop (((↑) : ℂ → Sphere) ⁻¹' G))
    (H K : ℂ ≃ₜ ℂ)
    (hH : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (A.disk i))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior H))
    (hK : extendAtInfinity F '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior (B.disk j))) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior K))
    (hsideH : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (A.disk i))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior H))
    (hsideK : extendAtInfinity F '' (G ∩ (((↑) : ℂ → Sphere) '' jordanInterior (B.disk j))) =
      (extendAtInfinity F '' G) ∩ (((↑) : ℂ → Sphere) '' jordanInterior K))
    (hHK : closure (jordanInterior H) ⊆ jordanInterior K)
    {C : Set ℂ} (hC : IsCompact C) (hCH : C ⊆ jordanInterior H)
    {L : ℝ} (hKL : closure (jordanInterior K) ⊆ ball 0 L)
    (w : ℕ → Sphere → ℝ)
    (hvalues : ∀ᶠ n in atTop,
      (∀ z ∈ frontier (jordanInterior (A.disk i)), w n z = 1) ∧
      (∀ z ∈ frontier (jordanInterior (B.disk j)), w n z = 0)) :
    ∀ᶠ n in atTop, ∀ y ∈ Complex.re '' C, ∃ a b : ℝ, a < b ∧
      (verticalLine y a : Sphere) ∈ V n ∧ (verticalLine y b : Sphere) ∈ V n ∧
      verticalLine y a ∈ closedBall 0 L ∧ verticalLine y b ∈ closedBall 0 L ∧
      w n (fi n (verticalLine y a)) = 0 ∧ w n (fi n (verticalLine y b)) = 1 := by
  obtain ⟨Hn, q, _, _, hq, hγ, hfront, hγlim, hqlim, hqa, hHb, hHnf⟩ :=
    exists_anchored_retained_jordan_models hsch T hTd f fi V heq hV hfix hG A i
      hretA hpoint F hF hlim H hH hsideH
  obtain ⟨Kn, p, _, _, hp, hδ, hfrontK, hδlim, hplim, hpa, hKb, hKnf⟩ :=
    exists_anchored_retained_jordan_models hsch T hTd f fi V heq hV hfix hG B j
      hretB hpoint F hF hlim K hK hsideK
  have hbound : ∀ᶠ n in atTop, closure (jordanInterior (Kn n)) ⊆ closedBall 0 L :=
    (eventually_jordan_fill_subset_open K Kn _ _ hδ hfrontK hKnf hδlim isOpen_ball hKL).mono
      (fun _ hn => hn.trans ball_subset_closedBall)
  have hdata : ∀ᶠ n in atTop,
      (frontier (jordanInterior (Hn n)) ⊆ ((↑) : ℂ → Sphere) ⁻¹' V n ∧
       frontier (jordanInterior (Kn n)) ⊆ ((↑) : ℂ → Sphere) ⁻¹' V n) ∧
      ((∀ z ∈ frontier (jordanInterior (Kn n)), w n (fi n z) = 0) ∧
       (∀ z ∈ frontier (jordanInterior (Hn n)), w n (fi n z) = 1)) := by
    filter_upwards [hretA, hretB, hHb, hKb, hvalues] with n hnA hnB hnH hnK hnv
    have ha := values_on_image_jordan_boundary (heq n)
      ((A.inDomain hnA).boundary_subset_domain i) hnH (w n) hnv.1
    have hb := values_on_image_jordan_boundary (heq n)
      ((B.inDomain hnB).boundary_subset_domain j) hnK (w n) hnv.2
    exact ⟨⟨ha.1, hb.1⟩, hb.2, ha.2⟩
  exact eventually_vertical_crossings_of_anchored_jordan_limits H K Hn Kn
    _ _ _ _ hγ hδ hfront hfrontK hHnf hKnf hγlim hδlim hHK hq hp hqlim hplim hqa hpa
    hC hCH (fun n => ((↑) : ℂ → Sphere) ⁻¹' V n)
    (fun n z => w n (fi n z)) hbound (hdata.mono fun _ h => h.1)
    (hdata.mono fun _ h => h.2) (Subset.refl _)

end CircleDomainRigidity

end

end OAI
