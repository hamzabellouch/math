import OAI.Probability.SLE.Gauge.RecenteredRibbonPassage
import OAI.Probability.SLE.Geometry.BoundaryScaleLaw

namespace OAI

/-! Uniform passage constants for actual recentered ribbon configurations.
The finite chart realization and normalization law are constructed, and
subsequence compactness supplies the diagonal estimate. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates BoundaryScaleLaw

local instance uniformRecenteredPathMeasurable : MeasurableSpace C(ℝ≥0, ℂ) := borel _
local instance uniformRecenteredPathBorel : BorelSpace C(ℝ≥0, ℂ) := ⟨rfl⟩

theorem uniform_recentered_passage_from_geometry
    {A Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (B₀ : ℝ≥0 → Ω → ℝ) (hB₀ : IsBrownianReal B₀ P)
    (hm : ∀ t, Measurable (B₀ t)) (hc : ∀ ω, Continuous (fun t => B₀ t ω))
    (γ : Ω → ℝ≥0 → ℂ) (Gbase Fbase : Ω → ℝ≥0 → ℂ → ℂ)
    (hwbase : ∀ ω, IsCapacityTwoWitness (fun t => Real.sqrt κ * B₀ t ω)
      (γ ω) (Gbase ω) (Fbase ω))
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (hsupport : PublishedGeometricTubeSupport P γ)
    (hplanar : PublishedPlanarDiskOpenness)
    (U : A → ℝ≥0 → ℝ) (γₙ : A → ℝ≥0 → ℂ)
    (G F₀ : A → ℝ≥0 → ℂ → ℂ)
    (hU : ∀ n, Continuous (U n))
    (hw : ∀ n, IsCapacityTwoWitness (U n) (γₙ n) (G n) (F₀ n))
    (T : A → ℝ≥0) (hT : ∀ n, 0 < T n)
    (hfresh : ∀ n s, s < T n → γₙ n (T n) ∈ survivingDomain (γₙ n) s)
    (αₙ : A → ℝ → ℂ) (Cg : ℝ≥0) (s c : ℝ)
    (hCg : 0 < (Cg : ℝ)) (hs : 0 < s) (hcpos : 0 < c)
    (hαL : ∀ n, LipschitzOnWith Cg (αₙ n) (Icc 0 2))
    (hα0 : ∀ n, αₙ n 0 = γₙ n (T n))
    (hchord : ∀ n u, u ∈ Icc (0 : ℝ) 2 → ∀ v, v ∈ Icc (0 : ℝ) 2 →
      c * |u - v| ≤ dist (αₙ n u) (αₙ n v))
    (hαD : ∀ n, MapsTo (αₙ n) (Ioc 0 2) (survivingDomain (γₙ n) (T n)))
    (hclear : ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ r : ℝ, 0 < r ∧
      ∀ n t, t ∈ Icc δ 2 → ball (αₙ n t) r ⊆ survivingDomain (γₙ n) (T n))
    (Qₙ : A → ℂ → ℂ) (K : Set ℂ) (hK : IsCompact K)
    (x₀ : ℂ) (hx₀ : x₀ ∈ K) (C Lq : ℝ≥0) (Rq : ℝ)
    (hC : 0 < C) (hLq : 0 < Lq)
    (hQupper : ∀ n, LipschitzOnWith C (Qₙ n) K)
    (hQlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ Lq * dist (Qₙ n x) (Qₙ n y))
    (hQtip : ∀ n, ‖Qₙ n x₀‖ ≤ Rq)
    (xₙ : A → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hxₙ : ∀ n, |xₙ n| ≤ ε / 4)
    (hcore : {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ ε / 4} ⊆ interior K)
    (hshape : ∀ n, EqOn (fun t => αₙ n t - γₙ n (T n))
      (fun t => Qₙ n (guideCoordinate 0 (xₙ n) t)) (Icc 0 2))
    (hangle : ∀ n, s ≤ (G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)).im /
      ‖G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)‖)
    (hregion : K ∩ passageCoordinateRegion C ε (ε / Lq) ⊆ interior K) :
    ∃ Fb : A → C(closedHalfPlane, ℂ),
      (∀ d (z : closedHalfPlane), z.1 ∈ upperHalfPlane → Fb d z =
        F₀ d (T d) ((U d (T d) : ℂ) + z) - γₙ d (T d)) ∧
      ∃ q c v₀ : ℝ, 0 < q ∧ 0 < c ∧ 0 < v₀ ∧
        ∀ d : A, ∀ v : ℝ, 0 < v → v < v₀ →
          ENNReal.ofReal q ≤ P {ω |
            finiteBoundaryPath (Fb d) (sourceTracePath γ (fun ω => (hwbase ω).1) ω) ∈
              BoundaryScaleLaw.frontMassEvent (longitudinalCoordinate (Qₙ d) K 0)
                (physicalPassageRegion (Qₙ d) K C ε (ε / Lq)) (Qₙ d 1)
                (ε / Lq) κ v c (physicalMiddleRegion (Qₙ d) K 0 ε)} := by
  choose Fb₀ hFb₀ _ using fun d => normalized_finite_capacity_inverse_boundary_extension
    hboundary (hU d) (hw d) (T d) 1 zero_lt_one
  let Fb : A → C(closedHalfPlane, ℂ) := fun d => Fb₀ d - ContinuousMap.const _ (γₙ d (T d))
  have hext d (z : closedHalfPlane) (hz : z.1 ∈ upperHalfPlane) : Fb d z =
      F₀ d (T d) ((U d (T d) : ℂ) + z) - γₙ d (T d) := by
    change Fb₀ d z - γₙ d (T d) = _
    rw [hFb₀ d z hz]
    simp only [Complex.ofReal_one, one_mul]
  let gp := sourceTracePath γ (fun ω => (hwbase ω).1)
  let prob := fun d v c => P {ω | finiteBoundaryPath (Fb d) (gp ω) ∈
    frontMassEvent (longitudinalCoordinate (Qₙ d) K 0)
      (physicalPassageRegion (Qₙ d) K C ε (ε / Lq)) (Qₙ d 1)
      (ε / Lq) κ v c (physicalMiddleRegion (Qₙ d) K 0 ε)}
  have hmono : ∀ d v, Antitone (prob d v) := by
    intro d v c₁ c₂ hc'
    apply measure_mono
    intro ω hω
    exact ⟨hω.1, (ENNReal.ofReal_le_ofReal hc').trans hω.2⟩
  have hgp : Measurable gp := by
    apply source_path_measurable
    intro t
    exact (brownian_capacity_trace_adapted B₀ hm hc κ γ Gbase Fbase hwbase t).mono
      ((Filtration.natural B₀ (fun t => (hm t).stronglyMeasurable)).le t) le_rfl
  have hclosed : ∀ᵐ ω ∂P, ClosedPathProperty (gp ω) :=
    Eventually.of_forall (fun ω t => (hwbase ω).2.2.1 t)
  have hVopen d : IsOpen (physicalPassageRegion (Qₙ d) K C ε (ε / Lq)) := by
    have hi := lower_lipschitz_injOn (Qₙ d) K Lq (hQlower d)
    have he : K ∩ passageCoordinateRegion C ε (ε / Lq) =
        interior K ∩ passageCoordinateRegion C ε (ε / Lq) :=
      Subset.antisymm (fun _ hz => ⟨hregion hz, hz.2⟩)
        (fun _ hz => ⟨interior_subset hz.1, hz.2⟩)
    unfold physicalPassageRegion
    rw [he]
    exact isOpen_image_coordinate_subset hplanar (Qₙ d) K _ (hQupper d).continuousOn hi
      (isOpen_interior.inter (passageCoordinateRegion_isOpen _ _ _))
      (inter_subset_left.trans interior_subset)
  have hVK d : physicalPassageRegion (Qₙ d) K C ε (ε / Lq) ⊆ Qₙ d '' K :=
    image_mono inter_subset_left
  have hpc d : ContinuousOn (longitudinalCoordinate (Qₙ d) K 0) (Qₙ d '' K) :=
    longitudinalCoordinate_continuousOn (Qₙ d) K Lq 0 (hQlower d)
  have hpK d : IsClosed (Qₙ d '' K) := (hK.image_of_continuousOn (hQupper d).continuousOn).isClosed
  obtain ⟨q, c₁, v₀, hq, hc₁, hv₀, hprob⟩ :=
      uniform_passage_threshold_of_subsequences prob hmono (by
        intro d v hv hlim
        obtain ⟨φ, b, Fbn, hφ, hb, hFbn, c, q, hcpos', hqpos, hseq⟩ :=
          recentered_ribbon_subsequence_passage P κ hκ hκ8 B₀ hB₀ hm hc γ Gbase Fbase hwbase
            hcompact hboundary hsupport hplanar
            (fun n => U (d n)) (fun n => γₙ (d n)) (fun n => G (d n)) (fun n => F₀ (d n))
            (fun n => hU (d n)) (fun n => hw (d n)) (fun n => T (d n)) (fun n => hT (d n))
            (fun n => hfresh (d n)) (fun n => αₙ (d n)) Cg s c hCg hs hcpos
            (fun n => hαL (d n)) (fun n => hα0 (d n)) (fun n => hchord (d n))
            (fun n => hαD (d n))
            (fun δ hδ hδ2 => by
              obtain ⟨r, hr, hh⟩ := hclear δ hδ hδ2
              exact ⟨r, hr, fun n => hh (d n)⟩)
            (fun n => Qₙ (d n)) K hK x₀ hx₀ C Lq Rq hC hLq
            (fun n => hQupper (d n)) (fun n => hQlower (d n)) (fun n => hQtip (d n))
            (fun n => xₙ (d n)) ε hε (fun n => hxₙ (d n)) hcore
            (fun n => hshape (d n)) (fun n => hangle (d n)) v hv hlim
        refine ⟨φ, hφ, c, hcpos', ENNReal.ofReal q, ENNReal.ofReal_pos.mpr hqpos, ?_⟩
        filter_upwards [hseq] with n hn
        let ell : ℝ≥0 := ⟨b n, (hb n).le⟩
        have hell : 0 < ell := by exact_mod_cast hb n
        have hFbeq : Fbn n = (Fb (d (φ n))).comp (scaleClosed ell) := by
          apply normalized_boundary_eq
            (fun z => F₀ (d (φ n)) (T (d (φ n))) z - γₙ (d (φ n)) (T (d (φ n))))
            (U (d (φ n)) (T (d (φ n)))) ell hell _ _ (hext (d (φ n)))
          intro z hz
          exact hFbn n z hz
        have hscale := ScaleTraceLaw.scaled_trace_path_law κ hκ hκ8 B₀ hB₀ hm hc
          γ Gbase Fbase hwbase ell hell
        have he := frontMassEvent_boundary_scale_probability P gp hgp hclosed ell hell
          (Fb (d (φ n))) hscale (longitudinalCoordinate (Qₙ (d (φ n))) K 0)
          (physicalPassageRegion (Qₙ (d (φ n))) K C ε (ε / Lq)) (Qₙ (d (φ n)) 1)
          (ε / Lq) κ (v (φ n)) c (physicalMiddleRegion (Qₙ (d (φ n))) K 0 ε)
          (Qₙ (d (φ n)) '' K) (hpK _) (hpc _) (hVopen _) (hVK _)
        rw [← hFbeq] at he
        dsimp only [prob]
        rw [← he]
        exact hn)
  exact ⟨Fb, hext, q, c₁, v₀, hq, hc₁, hv₀, hprob⟩

end SLEExactGauge

end

end OAI
