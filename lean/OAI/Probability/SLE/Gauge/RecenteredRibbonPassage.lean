import OAI.Probability.SLE.Geometry.RecenteredGuideCompactness
import OAI.Probability.SLE.Stochastic.PlanarCoordinatePassage
import OAI.Probability.SLE.Gauge.RibbonSequenceCompactness

namespace OAI

/-! Actual passage along a recentered conformal subsequence, with its
finite physical realization constructed from the boundary chart. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge
open RibbonCoordinates SequencePassage PassageSuccess FirstFrontPassage

theorem recentered_ribbon_subsequence_passage
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
    (U : ℕ → ℝ≥0 → ℝ) (γₙ : ℕ → ℝ≥0 → ℂ)
    (G F₀ : ℕ → ℝ≥0 → ℂ → ℂ)
    (hU : ∀ n, Continuous (U n))
    (hw : ∀ n, IsCapacityTwoWitness (U n) (γₙ n) (G n) (F₀ n))
    (T : ℕ → ℝ≥0) (hT : ∀ n, 0 < T n)
    (hfresh : ∀ n s, s < T n → γₙ n (T n) ∈ survivingDomain (γₙ n) s)
    (αₙ : ℕ → ℝ → ℂ) (Cg : ℝ≥0) (s c : ℝ)
    (hCg : 0 < (Cg : ℝ)) (hs : 0 < s) (hcpos : 0 < c)
    (hαL : ∀ n, LipschitzOnWith Cg (αₙ n) (Icc 0 2))
    (hα0 : ∀ n, αₙ n 0 = γₙ n (T n))
    (hchord : ∀ n u, u ∈ Icc (0 : ℝ) 2 → ∀ v, v ∈ Icc (0 : ℝ) 2 →
      c * |u - v| ≤ dist (αₙ n u) (αₙ n v))
    (hαD : ∀ n, MapsTo (αₙ n) (Ioc 0 2) (survivingDomain (γₙ n) (T n)))
    (hclear : ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ r : ℝ, 0 < r ∧
      ∀ n t, t ∈ Icc δ 2 → ball (αₙ n t) r ⊆ survivingDomain (γₙ n) (T n))
    (Qₙ : ℕ → ℂ → ℂ) (K : Set ℂ) (hK : IsCompact K)
    (x₀ : ℂ) (hx₀ : x₀ ∈ K) (C Lq : ℝ≥0) (Rq : ℝ)
    (hC : 0 < C) (hLq : 0 < Lq)
    (hQupper : ∀ n, LipschitzOnWith C (Qₙ n) K)
    (hQlower : ∀ n x, x ∈ K → ∀ y, y ∈ K → dist x y ≤ Lq * dist (Qₙ n x) (Qₙ n y))
    (hQtip : ∀ n, ‖Qₙ n x₀‖ ≤ Rq)
    (xₙ : ℕ → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hxₙ : ∀ n, |xₙ n| ≤ ε / 4)
    (hcore : {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 2 ∧ |z.im| ≤ ε / 4} ⊆ interior K)
    (hshape : ∀ n, EqOn (fun t => αₙ n t - γₙ n (T n))
      (fun t => Qₙ n (guideCoordinate 0 (xₙ n) t)) (Icc 0 2))
    (hangle : ∀ n, s ≤ (G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)).im /
      ‖G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)‖)
    (v : ℕ → ℝ) (hv : ∀ n, 0 < v n) (hlim : Tendsto v atTop (𝓝 0)) :
    ∃ (φ : ℕ → ℕ) (b : ℕ → ℝ) (Fb : ℕ → C(closedHalfPlane, ℂ)),
      StrictMono φ ∧ (∀ n, 0 < b n) ∧
      (∀ n (z : closedHalfPlane), z.1 ∈ upperHalfPlane → Fb n z =
        normalizedInverse (F₀ (φ n) (T (φ n))) (U (φ n) (T (φ n))) (b n) z -
          γₙ (φ n) (T (φ n))) ∧
      let η := fun n ω => (finiteBoundaryPath (Fb n)
        (sourceTracePath γ (fun ω => (hwbase ω).1) ω) : ℝ≥0 → ℂ)
      ∃ c₁ q : ℝ, 0 < c₁ ∧ 0 < q ∧ ∀ᶠ n in atTop,
        ENNReal.ofReal q ≤ P {ω |
          ω ∈ FrontSuccess η (fun n => longitudinalCoordinate (Qₙ (φ n)) K 0)
            (fun _ => 0) (fun n => physicalPassageRegion (Qₙ (φ n)) K C ε (ε / Lq))
            (fun n => Qₙ (φ n) 1) (ε / Lq) n ∧
          ENNReal.ofReal c₁ ≤ segmentSausageCharge κ (η n ω) 0
            (frontTime (fun t => longitudinalCoordinate (Qₙ (φ n)) K 0 (η n ω t)) 1)
            (v (φ n)) (physicalMiddleRegion (Qₙ (φ n)) K 0 ε)} := by
  let ℱ := Filtration.natural B₀ (fun t => (hm t).stronglyMeasurable)
  have hadapt := brownian_capacity_trace_adapted B₀ hm hc κ γ Gbase Fbase hwbase
  have hγm (t : ℝ≥0) : Measurable (fun ω => γ ω t) :=
    (hadapt t).mono (ℱ.le t) le_rfl
  have hSLE : IsOrdinaryChordalSLE κ γ P :=
    ⟨hγm, B₀, hB₀, Eventually.of_forall (fun ω => ⟨Gbase ω, Fbase ω, hwbase ω⟩)⟩
  have hxin : ∀ n, xₙ n ∈ Icc (-ε / 4) (ε / 4) := by
    intro n
    have hh := abs_le.mp (hxₙ n)
    constructor <;> linarith [hh.1, hh.2]
  obtain ⟨x, hx, ψ, hψ, hxlim⟩ := isCompact_Icc.tendsto_subseq hxin
  have hxabs : |x| ≤ ε / 4 := abs_le.mpr ⟨by linarith [hx.1], hx.2⟩
  obtain ⟨Q, χ, hχ, hQconv, hQu, hQl, _⟩ := exists_bilip_uniform_subsequence
    (fun n => Qₙ (ψ n)) K hK x₀ hx₀ C Lq Rq (fun n => hQupper (ψ n))
    (fun n => hQlower (ψ n)) (fun n => hQtip (ψ n))
  let ρ := ψ ∘ χ
  obtain ⟨b, Fb, βₙ, θ, F, α, β, hb, hext, hβc, hβ0, hβHn, hbarα,
      hθ, hF, hiF, hFne, homit, hFconv, hαconv, hβconv, _, _, hαclim, _,
      hβlim0, hβlimc, hβlimi, hβlimH, hrel⟩ :=
    recentered_actual_guide_compactness P κ hκ hκ8 γ hSLE hcompact hboundary
      (fun n => U (ρ n)) (fun n => γₙ (ρ n)) (fun n => G (ρ n)) (fun n => F₀ (ρ n))
      (fun n => hU (ρ n)) (fun n => hw (ρ n)) (fun n => T (ρ n)) (fun n => hT (ρ n))
      (fun n => hfresh (ρ n)) (fun n => αₙ (ρ n)) Cg s c hCg hs hcpos
      (fun n => hαL (ρ n)) (fun n => hα0 (ρ n))
      (fun n => hchord (ρ n)) (fun n => hαD (ρ n))
      (fun δ hδ hδ2 => by
        obtain ⟨r, hr, hh⟩ := hclear δ hδ hδ2
        exact ⟨r, hr, fun n => hh (ρ n)⟩)
      (fun n => hangle (ρ n))
  let φ := ρ ∘ θ
  let b' := fun n => b (θ n)
  let Fb' := fun n => Fb (θ n)
  let Fn := fun n z => normalizedInverse (F₀ (φ n) (T (φ n)))
    (U (φ n) (T (φ n))) (b' n) z - γₙ (φ n) (T (φ n))
  let α' := fun n t => αₙ (φ n) t - γₙ (φ n) (T (φ n))
  have hφ : StrictMono φ := (hψ.comp hχ).comp hθ
  have hQconv' : TendstoUniformlyOn (fun n => Qₙ (φ n)) Q atTop K := by
    intro u hu
    exact hθ.tendsto_atTop.eventually (hQconv u hu)
  have hguideK n t (ht : t ∈ Icc (0 : ℝ) 2) : guideCoordinate 0 (xₙ (φ n)) t ∈ K := by
    apply interior_subset
    apply hcore
    exact ⟨by simpa using ht.1, by simpa using ht.2,
      (guideCoordinate_im_bound ht.1).trans (hxₙ (φ n))⟩
  have hshapeLim : EqOn α (fun t => Q (guideCoordinate 0 x t)) (Icc 0 2) :=
    coordinate_guide_limit_identity (fun n => Qₙ (φ n)) Q K hK.isClosed hQu.continuousOn
      hQconv' (fun n => xₙ (φ n)) x
      (hxlim.comp (hχ.comp hθ).tendsto_atTop) α' α hαconv hguideK
      (fun n => hshape (φ n))
  have hmem t (ht : t ∈ Icc (0 : ℝ) (3 / 2)) : guideCoordinate 0 x t ∈ interior K := by
    apply hcore
    exact ⟨by simpa using ht.1, by simpa using ht.2.trans (by norm_num : (3 / 2 : ℝ) ≤ 2),
      (guideCoordinate_im_bound ht.1).trans hxabs⟩
  have hbase : (1 : ℂ) ∈ K := by
    apply interior_subset
    apply hcore
    refine ⟨by norm_num, by norm_num, ?_⟩
    simpa only [Complex.one_im, abs_zero] using (show 0 ≤ ε / 4 by positivity)
  let Fbar := fun n z => if hz : z ∈ closedHalfPlane then (Fb' n ⟨z, hz⟩ : OnePoint ℂ)
    else OnePoint.infty
  have hbar n : ContinuousOn (Fbar n) closedHalfPlane := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert OnePoint.continuous_coe.comp (Fb' n).continuous using 1
    funext z
    change (if hz : (z : ℂ) ∈ closedHalfPlane then (Fb' n ⟨z, hz⟩ : OnePoint ℂ)
      else OnePoint.infty) = (Fb' n z : OnePoint ℂ)
    rw [dite_eq_left z.2]
  have hbarext n z (hz : z ∈ upperHalfPlane) : Fbar n z = (Fn n z : OnePoint ℂ) := by
    have hz' : z ∈ closedHalfPlane := (show 0 < z.im from hz).le
    dsimp only [Fbar]
    rw [dite_eq_left hz']
    exact congrArg (fun z : ℂ => (z : OnePoint ℂ)) (hext (θ n) ⟨z, hz'⟩ hz)
  have hbarα' n t (ht : t ∈ Icc (0 : ℝ) 2) : Fbar n (βₙ (θ n) t) = (α' n t : OnePoint ℂ) := by
    dsimp only [Fbar]
    rw [dite_eq_left (show βₙ (θ n) t ∈ closedHalfPlane from hβHn (θ n) t ht)]
    exact congrArg (fun z : ℂ => (z : OnePoint ℂ)) (hbarα (θ n) t ht _)
  let gp := sourceTracePath γ (fun ω => (hwbase ω).1)
  let η := fun n ω => (finiteBoundaryPath (Fb' n) (gp ω) : ℝ≥0 → ℂ)
  have hηc n : ∀ᵐ ω ∂P, Continuous (η n ω) :=
    Eventually.of_forall (fun ω => (finiteBoundaryPath (Fb' n) (gp ω)).continuous)
  have hηbar n : ∀ᵐ ω ∂P, ∀ t, Fbar n (γ ω t) = (η n ω t : OnePoint ℂ) := by
    apply Eventually.of_forall
    intro ω t
    have hh : ClosedPathProperty (gp ω) := fun t => (hwbase ω).2.2.1 t
    dsimp only [η]
    rw [finiteBoundaryPath_apply _ _ hh]
    dsimp only [Fbar]
    rw [dite_eq_left (show γ ω t ∈ closedHalfPlane from (hwbase ω).2.2.1 t)]
    rfl
  have hαL' n : LipschitzOnWith Cg (α' n) (Icc 0 2) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro u hu w hw'
    simpa only [α', dist_sub_right] using (hαL (φ n)).dist_le_mul u hu w hw'
  have hnorm n := normalized_capacity_charts (hw (φ n)) (T (φ n)) (b' n) (hb (θ n))
  have hFn n : DifferentiableOn ℂ (Fn n) upperHalfPlane := (hnorm n).1.sub_const _
  have hiFn n : InjOn (Fn n) upperHalfPlane := by
    intro z hz w hw' he
    exact (hnorm n).2.1 hz hw' (sub_left_inj.mp he)
  obtain ⟨B, _, Tc, _, c₁, q, hc₁, hq, hprob⟩ := planar_coordinate_limit_passage
    κ hκ hκ8 B₀ hB₀ hm hc γ Gbase Fbase hwbase hboundary.to_onePoint hsupport hplanar
    (fun n => Qₙ (φ n)) Q K C Lq hC hLq (fun n => hQupper (φ n))
    (fun n => hQlower (φ n)) hQconv' hQu.continuousOn hbase
    Fn Fbar F hFn hiFn hbar hbarext hF hiF hFne hFconv
    α' (fun n => βₙ (θ n)) α β Cg hαL' hαconv hαclim
    (fun n => hβc (θ n)) (fun n => hβ0 (θ n)) (fun n => hβHn (θ n))
    hbarα' hβconv hβlimc hβlim0 hβlimi hβlimH hrel homit x ε (ε / Lq)
    (by linarith) (div_pos hε hLq) hshapeLim hmem
    (fun n => v (φ n)) (fun n => hv (φ n)) (hlim.comp hφ.tendsto_atTop) η hηc hηbar
  refine ⟨φ, b', Fb', hφ, (fun n => hb (θ n)), (fun n => hext (θ n)),
    c₁, q, hc₁, hq, ?_⟩
  filter_upwards [hprob] with n hn
  apply hn.trans (measure_mono ?_)
  rintro ω ⟨⟨hfinite, hhit, hbefore, hpath, hterminal⟩, hmass⟩
  exact ⟨⟨hfinite, hhit, bot_le.trans_lt hbefore, hpath, hterminal⟩,
    hmass.trans (segmentSausageCharge_mono κ (η n ω) bot_le le_rfl (v (φ n)) Subset.rfl)⟩

end SLEExactGauge

end

end OAI
