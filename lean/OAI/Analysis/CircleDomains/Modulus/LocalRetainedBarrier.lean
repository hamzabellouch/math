import OAI.Analysis.CircleDomains.Selection.RealAnchorRetention
import OAI.Analysis.CircleDomains.Transfer.RealTargetEnds
import OAI.Analysis.CircleDomains.Modulus.RotatedRealPayment
import OAI.Analysis.CircleDomains.Selection.LocalCrossingGeometry

namespace OAI

/-! The local barrier inequality for an actual retained end contour and a retained source anchor.
All target crossing and zero/one value hypotheses are derived from these source data. -/

open Set Function Filter Metric MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity.FiniteTransfer.RealTargetEnd

variable {S : Type*} {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
  {d : CountableRealCoordinates G π σ} {O : ℕ → S → Set Sphere} {ε : ℕ → ℝ}
  {M : RealModelExhaustion d O ε} {A : AssignedRealModelLimit M} {q : Sphere}
  (E : RealTargetEnd A q)

theorem local_barrier_payment
    (hsch : PlanarSchoenflies) (harea : ExteriorCoefficientAreaTheorem)
    (hG : IsOpen G) (hε : Tendsto ε atTop (𝓝 0))
    (k l : ℕ)
    (hone : ∀ z ∈ frontier (jordanInterior ((A.cores k).disk (E.address k))),
      d.physical l (Complex.equivRealProdCLM z) = 1)
    (H : ℂ ≃ₜ ℂ) (hHG : closure (jordanInterior H) ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hzero : ∀ z ∈ closure (jordanInterior H), d.physical l (Complex.equivRealProdCLM z) = 0)
    (c : ℂ) (δ : ℝ) (hanchor : closedBall c δ ⊆ A.function '' jordanInterior H)
    (hd : Disjoint (closedBall c δ) (closure (jordanInterior (A.contours k (E.address k)))))
    {Q : Set ℂ} (hQ : IsCompact Q) (hQinner : Q ⊆ jordanInterior (A.contours k (E.address k)))
    {W : Set ℂ} (hW : IsClosed W) (hWconvex : Convex ℝ W)
    (hQW : Q ⊆ W) (hBW : closedBall c δ ⊆ W)
    {P : Set ℂ} (hP : IsCompact P) (hPG : P ⊆ ((↑) : ℂ → Sphere) ⁻¹' G)
    (hPW : Disjoint (A.function '' P) W)
    (rot : Circle) {J : Set ℝ} (hJ : MeasurableSet J)
    (hprojection : J ⊆ (fun z => ((rotation rot).symm z).im) '' Q ∩
      Ioo (((rotation rot).symm c).im - δ) (((rotation rot).symm c).im + δ))
    {R : ℝ} (hR : 3 * M.radius ≤ R) (hWR : W ⊆ closedBall 0 R) :
    (volume J).toReal ≤ Real.sqrt Real.pi * R * Real.sqrt
      (∫ x in realChartDomain G \ (Complex.equivRealProdCLM '' P),
        gradientEnergy (d.physical l) (fun z => sphericalMetricFactor z • 1) x) +
      2 * R * Real.sqrt (∑' s, (d.upper l s - d.lower l s) ^ 2) := by
  let _ : ∀ n, Fintype (M.stages (A.subsequence n)).indices :=
    fun n => (M.stages (A.subsequence n)).finite_indices.fintype
  have hF : ContinuousOn A.function (((↑) : ℂ → Sphere) ⁻¹' G) := by
    intro z hz
    have h := continuousAt_finite_part_of_conformalAt (A.conformal.1 _ hz)
      (by simp only [extendAtInfinity_coe]; exact OnePoint.coe_ne_infty _)
    simpa only [extendAtInfinity_coe, finiteCoord_coe] using h.continuousWithinAt
  have hret := A.strict.tendsto_atTop
    (M.eventually_model_contains (A.cores k).isCompact (A.cores k).subset)
  obtain ⟨B, p, _, _, hp, hγ, hfront, hγlim, hplim, hpa, hboundary, hBfront⟩ :=
    exists_anchored_retained_jordan_models hsch
      (fun n => (M.stages (A.subsequence n)).terminals.H)
      (fun n => (M.stages (A.subsequence n)).terminals.disjoint_closures)
      (fun n => (M.stages (A.subsequence n)).forward)
      (fun n => (M.stages (A.subsequence n)).inverse)
      (fun n => (M.stages (A.subsequence n)).domain)
      (fun n => (M.stages (A.subsequence n)).equivalence)
      (fun n => (M.stages (A.subsequence n)).circle_domain.1)
      (fun n => (M.stages (A.subsequence n)).principal.1)
      hG (A.cores k) (E.address k) hret
      (fun z hz => A.strict.tendsto_atTop
        ((M.eventually_model_contains isCompact_singleton (singleton_subset_iff.mpr hz)).mono
          (fun _ hn => hn (mem_singleton z))))
      A.function hF A.converges (A.contours k (E.address k))
      (A.boundary k (E.address k)) (A.side k (E.address k))
  have hQin := eventually_compact_subset_jordanInterior_of_anchor
    (A.contours k (E.address k)) B _ _ hγ hfront hBfront hγlim hp hplim hpa
    hQ hQinner
  have hBin := eventually_jordan_fill_subset_open (A.contours k (E.address k)) B _ _
    hγ hfront hBfront hγlim isClosed_closedBall.isOpen_compl
    (fun z hz hzb => Set.disjoint_left.mp hd hzb hz)
  have hzeron := A.eventually_zero_on_anchor_image hsch hG H hHG l hzero (isCompact_closedBall c δ) hanchor
  have honen : ∀ᶠ n in atTop,
      frontier (jordanInterior (B n)) ⊆ ((↑) : ℂ → Sphere) ⁻¹' (M.stages (A.subsequence n)).domain ∧
      ∀ z ∈ frontier (jordanInterior (B n)),
        sphereRealFunction ((M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n)))
          ((M.stages (A.subsequence n)).inverse z) = 1 := by
    filter_upwards [hret, hboundary, A.strict.tendsto_atTop
      (M.eventually_test_eq (A.cores k).isCompact (A.cores k).subset l)] with n hn hb hv
    apply values_on_image_jordan_boundary (M.stages (A.subsequence n)).equivalence
      (((A.cores k).inDomain hn).boundary_subset_domain (E.address k)) hb
    intro z hz
    change (M.stages (A.subsequence n)).functions (prefixIndex l (A.subsequence n))
      (Complex.equivRealProdCLM z) = 1
    exact (hv z (((A.cores k).inDomain (Subset.refl _)).boundary_subset_domain (E.address k) ⟨z, hz, rfl⟩)).trans (hone z hz)
  apply A.rotated_line_payment_away_from_compact harea hε rot l hR hP hPG hW hWR hPW hJ
  filter_upwards [hQin, hBin, hzeron, honen] with n hnQ hnB hnZ hnOne
  have hc := localized_frontier_crossings rot (jordanInterior_isOpen (B n)) hnQ hQW hWconvex
    (fun z hz => ⟨fun hzcl => hnB hzcl (ball_subset_closedBall hz),
      hBW (ball_subset_closedBall hz)⟩) hprojection
  intro y hy
  obtain ⟨s, t, hst, hs, ht, hsegment⟩ := hc y hy
  have hsZ := hnZ _ (ball_subset_closedBall hs)
  exact ⟨s, t, hst, hsZ.1, hnOne.1 ht,
    hWR (hsegment _ left_mem_uIcc), hWR (hsegment _ right_mem_uIcc),
    hsZ.2, hnOne.2 _ ht, fun x hx _ => hsegment x hx⟩

end CircleDomainRigidity.FiniteTransfer.RealTargetEnd

end

end OAI
