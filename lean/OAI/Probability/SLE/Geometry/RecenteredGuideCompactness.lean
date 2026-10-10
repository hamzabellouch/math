import OAI.Probability.SLE.Geometry.ActualGuideCompactness
import OAI.Probability.SLE.Geometry.PublishedFiniteBoundaryExtension

namespace OAI

/-! Actual stopped charts recentered at their physical tips. The tip may
escape to infinity as the ribbon front varies; subtracting it before the
normal-family argument removes any artificial bound on its location. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace SLEExactGauge

theorem recentered_actual_guide_compactness
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedFiniteLoewnerBoundaryExtension)
    (U : ℕ → ℝ≥0 → ℝ) (γₙ : ℕ → ℝ≥0 → ℂ)
    (G F₀ : ℕ → ℝ≥0 → ℂ → ℂ)
    (hU : ∀ n, Continuous (U n))
    (hw : ∀ n, IsCapacityTwoWitness (U n) (γₙ n) (G n) (F₀ n))
    (T : ℕ → ℝ≥0) (hT : ∀ n, 0 < T n)
    (hfresh : ∀ n s, s < T n → γₙ n (T n) ∈ survivingDomain (γₙ n) s)
    (αₙ : ℕ → ℝ → ℂ) (C : ℝ≥0) (s c : ℝ)
    (hC : 0 < (C : ℝ)) (hs : 0 < s) (hc : 0 < c)
    (hαL : ∀ n, LipschitzOnWith C (αₙ n) (Icc 0 2))
    (hα0 : ∀ n, αₙ n 0 = γₙ n (T n))
    (hchord : ∀ n u, u ∈ Icc (0 : ℝ) 2 → ∀ v, v ∈ Icc (0 : ℝ) 2 →
      c * |u - v| ≤ dist (αₙ n u) (αₙ n v))
    (hαD : ∀ n, MapsTo (αₙ n) (Ioc 0 2) (survivingDomain (γₙ n) (T n)))
    (hclear : ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ r : ℝ, 0 < r ∧
      ∀ n t, t ∈ Icc δ 2 → ball (αₙ n t) r ⊆ survivingDomain (γₙ n) (T n))
    (hangle : ∀ n, s ≤ (G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)).im /
      ‖G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)‖) :
    ∃ (b : ℕ → ℝ) (Fb : ℕ → C(closedHalfPlane, ℂ)) (βₙ : ℕ → ℝ → ℂ)
      (φ : ℕ → ℕ) (F : ℂ → ℂ) (α β : ℝ → ℂ),
      (∀ n, 0 < b n) ∧
      (∀ n (z : closedHalfPlane), z.1 ∈ upperHalfPlane → Fb n z =
        normalizedInverse (F₀ n (T n)) (U n (T n)) (b n) z - γₙ n (T n)) ∧
      (∀ n, ContinuousOn (βₙ n) (Icc 0 2)) ∧ (∀ n, βₙ n 0 = 0) ∧
      (∀ n t, t ∈ Icc (0 : ℝ) 2 → 0 ≤ (βₙ n t).im) ∧
      (∀ n t, t ∈ Icc (0 : ℝ) 2 → ∀ ht : 0 ≤ (βₙ n t).im,
        Fb n ⟨βₙ n t, ht⟩ = αₙ n t - γₙ n (T n)) ∧
      StrictMono φ ∧ DifferentiableOn ℂ F upperHalfPlane ∧ InjOn F upperHalfPlane ∧
      (∀ z ∈ upperHalfPlane, deriv F z ≠ 0) ∧ α 0 ∉ F '' upperHalfPlane ∧
      TendstoLocallyUniformlyOn
        (fun n z => normalizedInverse (F₀ (φ n) (T (φ n))) (U (φ n) (T (φ n)))
          (b (φ n)) z - γₙ (φ n) (T (φ n))) F atTop upperHalfPlane ∧
      TendstoUniformlyOn (fun n t => αₙ (φ n) t - γₙ (φ n) (T (φ n))) α atTop (Icc 0 2) ∧
      TendstoUniformlyOn (fun n => βₙ (φ n)) β atTop (Icc 0 2) ∧
      α 0 = 0 ∧ LipschitzOnWith C α (Icc 0 2) ∧
      ContinuousOn α (Icc 0 2) ∧ InjOn α (Icc 0 2) ∧
      β 0 = 0 ∧ ContinuousOn β (Icc 0 2) ∧ InjOn β (Icc 0 2) ∧
      MapsTo β (Ioc 0 2) upperHalfPlane ∧ EqOn (F ∘ β) α (Ioc 0 2) := by
  have hguide n := normalized_actual_access_guide hboundary.to_onePoint (hw n) (hU n)
    (T n) (hT n) (hfresh n) (αₙ n) (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (1 / 2 : ℝ) ∈ Ioc 0 2) (hαL n).continuousOn
    (PhysicalGuideCompactness.injective_of_lower_chord_bound hc (hchord n)) (hα0 n) (hαD n)
  choose b hb oldFb βₙ oldBar oldExt hβc hβi hβ0 hβH oldRelation hβnorm hβeq using hguide
  choose Fb₀ hFb₀ hFb₀zero using fun n =>
    normalized_finite_capacity_inverse_boundary_extension hboundary (hU n) (hw n) (T n) (b n) (hb n)
  let a := fun n => γₙ n (T n)
  let α' := fun n t => αₙ n t - a n
  let Fb : ℕ → C(closedHalfPlane, ℂ) := fun n => Fb₀ n - ContinuousMap.const _ (a n)
  let Fn := fun n z => normalizedInverse (F₀ n (T n)) (U n (T n)) (b n) z - a n
  let g₀ := fun n => normalizedForward (G n (T n)) (U n (T n)) (b n)
  let g := fun n z => g₀ n (z + a n)
  let D := fun n => {z : ℂ | z + a n ∈ survivingDomain (γₙ n) (T n)}
  have hcharts n := normalized_capacity_charts (hw n) (T n) (b n) (hb n)
  have hD n : IsOpen (D n) :=
    (isOpen_survivingDomain (hw n).1 _).preimage (continuous_id.add continuous_const)
  have hFn n : DifferentiableOn ℂ (Fn n) upperHalfPlane := (hcharts n).1.sub_const _
  have hiFn n : InjOn (Fn n) upperHalfPlane := by
    intro z hz w hw' he
    exact (hcharts n).2.1 hz hw' (sub_left_inj.mp he)
  have hg n : DifferentiableOn ℂ (g n) (D n) :=
    (hcharts n).2.2.1.comp (differentiable_id.add_const _).differentiableOn (fun _ hz => hz)
  have hig n : InjOn (g n) (D n) := by
    intro z hz w hw' he
    exact add_right_cancel ((hcharts n).2.2.2.1 hz hw' he)
  have hFD n : MapsTo (Fn n) upperHalfPlane (D n) := by
    intro z hz
    simpa only [D, mem_ofPred_eq, Fn, sub_add_cancel] using (hcharts n).2.2.2.2.1 hz
  have hgH n : MapsTo (g n) (D n) upperHalfPlane := fun _ hz => (hcharts n).2.2.2.2.2.1 hz
  have hgf n z (hz : z ∈ upperHalfPlane) : g n (Fn n z) = z := by
    simpa only [g, Fn, sub_add_cancel] using (hcharts n).2.2.2.2.2.2.1 z hz
  have hβHclosed n t (ht : t ∈ Icc (0 : ℝ) 2) : 0 ≤ (βₙ n t).im := by
    by_cases ht0 : t = 0
    · simp only [ht0, hβ0, Complex.zero_im, le_refl]
    · exact (show 0 < (βₙ n t).im from hβH n ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩).le
  have hext n (z : closedHalfPlane) (hz : z.1 ∈ upperHalfPlane) : Fb n z = Fn n z := by
    change Fb₀ n z - a n = F₀ n (T n) ((U n (T n) : ℂ) + (b n : ℂ) * z) - a n
    rw [hFb₀ n z hz]
  have hrelation n t (ht : t ∈ Ioc (0 : ℝ) 2) : Fn n (βₙ n t) = α' n t := by
    dsimp only [Fn, α']
    congr 1
    apply OnePoint.coe_injective
    exact (oldExt n _ (hβH n ht)).symm.trans (oldRelation n t ⟨ht.1.le, ht.2⟩)
  have hbarRelation n t (ht : t ∈ Icc (0 : ℝ) 2) :
      Fb n ⟨βₙ n t, hβHclosed n t ht⟩ = α' n t := by
    by_cases ht0 : t = 0
    · subst t
      change Fb₀ n ⟨βₙ n 0, _⟩ - a n = αₙ n 0 - a n
      rw [hα0 n]
      congr 1
      simpa only [hβ0] using hFb₀zero n
    · have ht' : t ∈ Ioc (0 : ℝ) 2 := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩
      rw [hext n _ (hβH n ht')]
      exact hrelation n t ht'
  let Fbar := fun n z => if hz : z ∈ closedHalfPlane then (Fb n ⟨z, hz⟩ : OnePoint ℂ)
    else OnePoint.infty
  have hbar n : ContinuousOn (Fbar n) closedHalfPlane := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert OnePoint.continuous_coe.comp (Fb n).continuous using 1
    funext z
    change (if hz : (z : ℂ) ∈ closedHalfPlane then (Fb n ⟨z, hz⟩ : OnePoint ℂ)
      else OnePoint.infty) = (Fb n z : OnePoint ℂ)
    rw [dite_eq_left z.2]
  have hbarext n z (hz : z ∈ upperHalfPlane) : Fbar n z = (Fn n z : OnePoint ℂ) := by
    have hz' : z ∈ closedHalfPlane := (show 0 < z.im from hz).le
    dsimp only [Fbar]
    rw [dite_eq_left hz']
    exact congrArg (fun z : ℂ => (z : OnePoint ℂ)) (hext n ⟨z, hz'⟩ hz)
  have hαL' n : LipschitzOnWith C (α' n) (Icc 0 2) := by
    apply lipschitzOnWith_iff_dist_le_mul.mpr
    intro u hu v hv
    simpa only [α', dist_sub_right] using (hαL n).dist_le_mul u hu v hv
  have hα0' n : α' n 0 = 0 := by simp only [α', a, hα0, sub_self]
  have hchord' (n : ℕ) (u : ℝ) (hu : u ∈ Icc (0 : ℝ) 2)
      (v : ℝ) (hv : v ∈ Icc (0 : ℝ) 2) : c * |u - v| ≤ dist (α' n u) (α' n v) := by
    simpa only [α', dist_sub_right] using hchord n u hu v hv
  have hβeq' n t (ht : t ∈ Ioc (0 : ℝ) 2) : βₙ n t = g n (α' n t) := by
    simpa only [g, α', sub_add_cancel, g₀, normalizedForward] using hβeq n t ht
  have hway n : ‖βₙ n (1 / 2)‖ = 1 ∧ s ≤ (βₙ n (1 / 2)).im := by
    refine ⟨hβnorm n, ?_⟩
    have hn := hβnorm n
    rw [hβeq n _ (by norm_num : (1 / 2 : ℝ) ∈ Ioc 0 2), norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hb n)] at hn
    have he : b n = ‖G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)‖ :=
      ((div_eq_one_iff_eq (hb n).ne').mp hn).symm
    rw [hβeq n _ (by norm_num : (1 / 2 : ℝ) ∈ Ioc 0 2), Complex.div_ofReal_im, he]
    exact hangle n
  have homit n : (0 : ℂ) ∉ Fn n '' upperHalfPlane := by
    rintro ⟨z, hz, he⟩
    have hh := (hcharts n).2.2.2.2.1 hz
    have he' : normalizedInverse (F₀ n (T n)) (U n (T n)) (b n) z = a n := sub_eq_zero.mp he
    rw [he'] at hh
    exact hh.1.2 ⟨T n, ⟨bot_le, le_rfl⟩, rfl⟩
  have hclear' : ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ r : ℝ, 0 < r ∧
      ∀ n t, t ∈ Icc δ 2 → ball (α' n t) r ⊆ D n := by
    intro δ hδ hδ2
    obtain ⟨r, hr, hball⟩ := hclear δ hδ hδ2
    refine ⟨r, hr, ?_⟩
    intro n t ht z hz
    apply hball n t ht
    rw [mem_ball, dist_eq_norm]
    change ‖z + a n - αₙ n t‖ < r
    have hz' : ‖z - (αₙ n t - a n)‖ < r := by
      simpa only [mem_ball, dist_eq_norm, α'] using hz
    convert hz' using 1
    congr 1
    ring
  obtain ⟨ρ, hρ, hballs⟩ := hclear' (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨φ, F, α, β, hφ, hF, hiF, hFne, homitlim, hFconv, hαconv, hβconv, hatip,
      hαLlim, hαclim, hαilim, hβlim0, hβlimc, hβlimi, hβlimH, hlimrel⟩ :=
    GuideCompactness.exists_joint_guide_limit_of_clearance P κ hκ hκ8 γ hSLE hcompact
      Fn g D Fbar α' βₙ (fun _ => 0) C (by norm_num) (by norm_num) (by norm_num)
      hs hρ hc hC hD hFn hiFn hg hig hFD hgH hgf hbar hbarext hαL' hα0'
      (fun _ => le_rfl) hchord' hβc hβ0 hβHclosed hway
      (fun n => hballs n _ (by norm_num)) homit hrelation
      (fun n t ht => by
        dsimp only [Fbar]
        rw [dite_eq_left (show βₙ n t ∈ closedHalfPlane from hβHclosed n t ht)]
        exact congrArg (fun z : ℂ => (z : OnePoint ℂ)) (hbarRelation n t ht))
      hβeq' hclear'
  have hzero : α 0 = 0 := by
    exact tendsto_nhds_unique hatip (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0))
  exact ⟨b, Fb, βₙ, φ, F, α, β, hb, hext, hβc, hβ0, hβHclosed,
    (fun n t ht _ => hbarRelation n t ht),
    hφ, hF, hiF, hFne, homitlim, hFconv, hαconv, hβconv, hzero, hαLlim,
    hαclim, hαilim, hβlim0, hβlimc, hβlimi, hβlimH, hlimrel⟩

end SLEExactGauge

end

end OAI
