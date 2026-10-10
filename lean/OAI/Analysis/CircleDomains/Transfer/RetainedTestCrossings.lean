import OAI.Analysis.CircleDomains.Topology.RetainedJordanConvergence

namespace OAI

/-!
# Crossing segments for an actual retained test

The source test has value one on an inner retained contour and zero on
an outer one. Their actual finite-model images produce the common
crossings used in line payment, with anchors derived from source points.
-/

open Set Function Filter Metric
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

open FiniteTransfer

theorem values_on_image_jordan_boundary
    {f fi : Sphere → Sphere} {U V : Set Sphere}
    (heq : IsSmoothSphereEquivalence f fi U V)
    {H K : ℂ ≃ₜ ℂ}
    (hsource : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ U)
    (himage : f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) =
      ((↑) : ℂ → Sphere) '' frontier (jordanInterior K))
    (w : Sphere → ℝ) {c : ℝ} (hvalue : ∀ z ∈ frontier (jordanInterior H), w z = c) :
    frontier (jordanInterior K) ⊆ ((↑) : ℂ → Sphere) ⁻¹' V ∧
      ∀ z ∈ frontier (jordanInterior K), w (fi z) = c := by
  have hpre (z : ℂ) (hz : z ∈ frontier (jordanInterior K)) :
      ∃ p ∈ (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)), f p = z := by
    have hh : (z : Sphere) ∈ f '' (((↑) : ℂ → Sphere) '' frontier (jordanInterior H)) := by
      rw [himage]
      exact ⟨z, hz, rfl⟩
    exact hh
  constructor
  · intro z hz
    obtain ⟨p, hp, he⟩ := hpre z hz
    change (z : Sphere) ∈ V
    rw [← he]
    exact heq.mapsTo (hsource hp)
  · intro z hz
    obtain ⟨p, hp, he⟩ := hpre z hz
    have hpinv := heq.left_inv p (hsource hp)
    rw [he] at hpinv
    rw [hpinv]
    obtain ⟨q, hq, rfl⟩ := hp
    exact hvalue q hq

theorem eventually_crossings_of_retained_test
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
    ∀ᶠ n in atTop, ∀ y ∈ Complex.im '' C, ∃ a b : ℝ, a < b ∧
      (horizontalLine y a : Sphere) ∈ V n ∧ (horizontalLine y b : Sphere) ∈ V n ∧
      horizontalLine y a ∈ closedBall 0 L ∧ horizontalLine y b ∈ closedBall 0 L ∧
      w n (fi n (horizontalLine y a)) = 0 ∧ w n (fi n (horizontalLine y b)) = 1 := by
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
  exact eventually_crossings_of_anchored_jordan_limits H K Hn Kn
    _ _ _ _ hγ hδ hfront hfrontK hHnf hKnf hγlim hδlim hHK hq hp hqlim hplim hqa hpa
    hC hCH (fun n => ((↑) : ℂ → Sphere) ⁻¹' V n)
    (fun n z => w n (fi n z)) hbound (hdata.mono fun _ h => h.1)
    (hdata.mono fun _ h => h.2) (Subset.refl _)

end CircleDomainRigidity

end

end OAI
