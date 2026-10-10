import OAI.Probability.SLE.Geometry.NormalizedAccessGuide
import OAI.Probability.SLE.Geometry.NormalizedLoewnerCharts
import OAI.Probability.SLE.Geometry.GuideCompactness

namespace OAI

/-! Joint compactness for stopped capacity charts. Freshness, physical
clearance and a waypoint angle bound give parameter-guide compactness
and nondegenerate limits of the normalized analytic charts. -/

noncomputable section
open Set Filter MeasureTheory Metric
open scoped Topology NNReal

namespace SLEExactGauge

theorem actual_guide_joint_compactness
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedLoewnerBoundaryExtension)
    (U : ℕ → ℝ≥0 → ℝ) (γₙ : ℕ → ℝ≥0 → ℂ)
    (G F₀ : ℕ → ℝ≥0 → ℂ → ℂ)
    (hU : ∀ n, Continuous (U n))
    (hw : ∀ n, IsCapacityTwoWitness (U n) (γₙ n) (G n) (F₀ n))
    (T : ℕ → ℝ≥0) (hT : ∀ n, 0 < T n)
    (hfresh : ∀ n s, s < T n → γₙ n (T n) ∈ survivingDomain (γₙ n) s)
    (αₙ : ℕ → ℝ → ℂ) (C : ℝ≥0) (s c A : ℝ)
    (hC : 0 < (C : ℝ)) (hs : 0 < s) (hc : 0 < c)
    (hαL : ∀ n, LipschitzOnWith C (αₙ n) (Icc 0 2))
    (hα0 : ∀ n, αₙ n 0 = γₙ n (T n)) (haBound : ∀ n, ‖γₙ n (T n)‖ ≤ A)
    (hchord : ∀ n u, u ∈ Icc (0 : ℝ) 2 → ∀ v, v ∈ Icc (0 : ℝ) 2 →
      c * |u - v| ≤ dist (αₙ n u) (αₙ n v))
    (hαD : ∀ n, MapsTo (αₙ n) (Ioc 0 2) (survivingDomain (γₙ n) (T n)))
    (hclear : ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ r : ℝ, 0 < r ∧
      ∀ n t, t ∈ Icc δ 2 → ball (αₙ n t) r ⊆ survivingDomain (γₙ n) (T n))
    (hangle : ∀ n, s ≤ (G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)).im /
      ‖G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)‖) :
    ∃ (b : ℕ → ℝ) (φ : ℕ → ℕ) (F : ℂ → ℂ) (α β : ℝ → ℂ),
      (∀ n, 0 < b n) ∧ StrictMono φ ∧
      DifferentiableOn ℂ F upperHalfPlane ∧ InjOn F upperHalfPlane ∧
      (∀ z ∈ upperHalfPlane, deriv F z ≠ 0) ∧ α 0 ∉ F '' upperHalfPlane ∧
      TendstoLocallyUniformlyOn
        (fun n => normalizedInverse (F₀ (φ n) (T (φ n))) (U (φ n) (T (φ n))) (b (φ n)))
        F atTop upperHalfPlane ∧
      TendstoUniformlyOn (fun n => αₙ (φ n)) α atTop (Icc 0 2) ∧
      β 0 = 0 ∧ ContinuousOn β (Icc 0 2) ∧ InjOn β (Icc 0 2) ∧
      MapsTo β (Ioc 0 2) upperHalfPlane ∧ EqOn (F ∘ β) α (Ioc 0 2) := by
  have hguide n := normalized_actual_access_guide hboundary (hw n) (hU n) (T n) (hT n)
    (hfresh n) (αₙ n) (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (1 / 2 : ℝ) ∈ Ioc 0 2) (hαL n).continuousOn
    (PhysicalGuideCompactness.injective_of_lower_chord_bound hc (hchord n)) (hα0 n) (hαD n)
  choose b hb Fb βₙ hbar hext hβc hβi hβ0 hβH hbarα hβnorm hβeq using hguide
  let Fn := fun n => normalizedInverse (F₀ n (T n)) (U n (T n)) (b n)
  let g := fun n => normalizedForward (G n (T n)) (U n (T n)) (b n)
  let D := fun n => survivingDomain (γₙ n) (T n)
  have hcharts n := normalized_capacity_charts (hw n) (T n) (b n) (hb n)
  have hFn n : DifferentiableOn ℂ (Fn n) upperHalfPlane := (hcharts n).1
  have hiFn n : InjOn (Fn n) upperHalfPlane := (hcharts n).2.1
  have hg n : DifferentiableOn ℂ (g n) (D n) := (hcharts n).2.2.1
  have hig n : InjOn (g n) (D n) := (hcharts n).2.2.2.1
  have hFD n : MapsTo (Fn n) upperHalfPlane (D n) := (hcharts n).2.2.2.2.1
  have hgH n : MapsTo (g n) (D n) upperHalfPlane := (hcharts n).2.2.2.2.2.1
  have hgf n : ∀ z ∈ upperHalfPlane, g n (Fn n z) = z := (hcharts n).2.2.2.2.2.2.1
  have hrelation n t (ht : t ∈ Ioc (0 : ℝ) 2) : Fn n (βₙ n t) = αₙ n t := by
    apply OnePoint.coe_injective
    exact (hext n _ (hβH n ht)).symm.trans (hbarα n t ⟨ht.1.le, ht.2⟩)
  have hβHclosed n t (ht : t ∈ Icc (0 : ℝ) 2) : 0 ≤ (βₙ n t).im := by
    by_cases ht0 : t = 0
    · simp only [ht0, hβ0, Complex.zero_im, le_refl]
    · exact (show 0 < (βₙ n t).im from hβH n ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩).le
  have hway n : ‖βₙ n (1 / 2)‖ = 1 ∧ s ≤ (βₙ n (1 / 2)).im := by
    refine ⟨hβnorm n, ?_⟩
    have hnorm := hβnorm n
    rw [hβeq n _ (by norm_num : (1 / 2 : ℝ) ∈ Ioc 0 2), norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hb n)] at hnorm
    have he : b n = ‖G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)‖ :=
      ((div_eq_one_iff_eq (hb n).ne').mp hnorm).symm
    rw [hβeq n _ (by norm_num : (1 / 2 : ℝ) ∈ Ioc 0 2), Complex.div_ofReal_im, he]
    exact hangle n
  have homit n : γₙ n (T n) ∉ Fn n '' upperHalfPlane := by
    rintro ⟨z, hz, he⟩
    have hh := hFD n hz
    rw [he] at hh
    exact hh.1.2 ⟨T n, ⟨bot_le, le_rfl⟩, rfl⟩
  obtain ⟨ρ, hρ, hballs⟩ := hclear (1 / 2) (by norm_num) (by norm_num)
  have hwayclear n : ball (αₙ n (1 / 2)) ρ ⊆ D n :=
    hballs n _ (by norm_num)
  obtain ⟨φ, F, α, β, hφ, hF, hiF, hFne, homitlim, hFconv, hαconv, _, _,
      _, _, _, hβlim0, hβlimc, hβlimi, hβlimH, hlimrel⟩ :=
    GuideCompactness.exists_joint_guide_limit_of_clearance P κ hκ hκ8 γ hSLE hcompact
      Fn g D Fb αₙ βₙ (fun n => γₙ n (T n)) C
      (by norm_num) (by norm_num) (by norm_num) hs hρ hc hC
      (fun n => isOpen_survivingDomain (hw n).1 _) hFn hiFn hg hig hFD hgH hgf
      hbar hext hαL hα0 haBound hchord hβc hβ0 hβHclosed hway hwayclear homit
      hrelation hbarα (fun n t ht => hβeq n t ht) hclear
  exact ⟨b, φ, F, α, β, hb, hφ, hF, hiF, hFne, homitlim, hFconv, hαconv,
    hβlim0, hβlimc, hβlimi, hβlimH, hlimrel⟩

/-- The same actual compactness extraction, retaining the chosen normalized
boundary charts and parameter-guide family. Uniform convergence of that
family supplies the fixed positive guide-time convergence needed by early
trace localization. -/
theorem actual_guide_joint_compactness_with_family
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8)
    (γ : Ω → ℝ≥0 → ℂ) (hSLE : IsOrdinaryChordalSLE κ γ P)
    (hcompact : PublishedHalfPlaneUnivalentCompactness)
    (hboundary : PublishedLoewnerBoundaryExtension)
    (U : ℕ → ℝ≥0 → ℝ) (γₙ : ℕ → ℝ≥0 → ℂ)
    (G F₀ : ℕ → ℝ≥0 → ℂ → ℂ)
    (hU : ∀ n, Continuous (U n))
    (hw : ∀ n, IsCapacityTwoWitness (U n) (γₙ n) (G n) (F₀ n))
    (T : ℕ → ℝ≥0) (hT : ∀ n, 0 < T n)
    (hfresh : ∀ n s, s < T n → γₙ n (T n) ∈ survivingDomain (γₙ n) s)
    (αₙ : ℕ → ℝ → ℂ) (C : ℝ≥0) (s c A : ℝ)
    (hC : 0 < (C : ℝ)) (hs : 0 < s) (hc : 0 < c)
    (hαL : ∀ n, LipschitzOnWith C (αₙ n) (Icc 0 2))
    (hα0 : ∀ n, αₙ n 0 = γₙ n (T n)) (haBound : ∀ n, ‖γₙ n (T n)‖ ≤ A)
    (hchord : ∀ n u, u ∈ Icc (0 : ℝ) 2 → ∀ v, v ∈ Icc (0 : ℝ) 2 →
      c * |u - v| ≤ dist (αₙ n u) (αₙ n v))
    (hαD : ∀ n, MapsTo (αₙ n) (Ioc 0 2) (survivingDomain (γₙ n) (T n)))
    (hclear : ∀ δ : ℝ, 0 < δ → δ ≤ 2 → ∃ r : ℝ, 0 < r ∧
      ∀ n t, t ∈ Icc δ 2 → ball (αₙ n t) r ⊆ survivingDomain (γₙ n) (T n))
    (hangle : ∀ n, s ≤ (G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)).im /
      ‖G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)‖) :
    ∃ (b : ℕ → ℝ) (Fb : ℕ → ℂ → OnePoint ℂ) (βₙ : ℕ → ℝ → ℂ)
      (φ : ℕ → ℕ) (F : ℂ → ℂ) (α β : ℝ → ℂ),
      (∀ n, 0 < b n) ∧
      (∀ n, ContinuousOn (Fb n) {z : ℂ | 0 ≤ z.im}) ∧
      (∀ n z, z ∈ upperHalfPlane → Fb n z =
        (normalizedInverse (F₀ n (T n)) (U n (T n)) (b n) z : OnePoint ℂ)) ∧
      (∀ n, ContinuousOn (βₙ n) (Icc 0 2)) ∧
      (∀ n, βₙ n 0 = 0) ∧
      (∀ n t, t ∈ Icc (0 : ℝ) 2 → 0 ≤ (βₙ n t).im) ∧
      (∀ n t, t ∈ Ioc (0 : ℝ) 2 → βₙ n t =
        normalizedForward (G n (T n)) (U n (T n)) (b n) (αₙ n t)) ∧
      (∀ n t, t ∈ Icc (0 : ℝ) 2 → Fb n (βₙ n t) = (αₙ n t : OnePoint ℂ)) ∧
      StrictMono φ ∧ DifferentiableOn ℂ F upperHalfPlane ∧ InjOn F upperHalfPlane ∧
      (∀ z ∈ upperHalfPlane, deriv F z ≠ 0) ∧ α 0 ∉ F '' upperHalfPlane ∧
      TendstoLocallyUniformlyOn
        (fun n => normalizedInverse (F₀ (φ n) (T (φ n))) (U (φ n) (T (φ n))) (b (φ n)))
        F atTop upperHalfPlane ∧
      TendstoUniformlyOn (fun n => αₙ (φ n)) α atTop (Icc 0 2) ∧
      TendstoUniformlyOn (fun n => βₙ (φ n)) β atTop (Icc 0 2) ∧
      Tendsto (fun n => γₙ (φ n) (T (φ n))) atTop (𝓝 (α 0)) ∧
      LipschitzOnWith C α (Icc 0 2) ∧ ContinuousOn α (Icc 0 2) ∧ InjOn α (Icc 0 2) ∧
      β 0 = 0 ∧ ContinuousOn β (Icc 0 2) ∧ InjOn β (Icc 0 2) ∧
      MapsTo β (Ioc 0 2) upperHalfPlane ∧ EqOn (F ∘ β) α (Ioc 0 2) := by
  have hguide n := normalized_actual_access_guide hboundary (hw n) (hU n) (T n) (hT n)
    (hfresh n) (αₙ n) (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (1 / 2 : ℝ) ∈ Ioc 0 2) (hαL n).continuousOn
    (PhysicalGuideCompactness.injective_of_lower_chord_bound hc (hchord n)) (hα0 n) (hαD n)
  choose b hb Fb βₙ hbar hext hβc hβi hβ0 hβH hbarα hβnorm hβeq using hguide
  let Fn := fun n => normalizedInverse (F₀ n (T n)) (U n (T n)) (b n)
  let g := fun n => normalizedForward (G n (T n)) (U n (T n)) (b n)
  let D := fun n => survivingDomain (γₙ n) (T n)
  have hcharts n := normalized_capacity_charts (hw n) (T n) (b n) (hb n)
  have hFn n : DifferentiableOn ℂ (Fn n) upperHalfPlane := (hcharts n).1
  have hiFn n : InjOn (Fn n) upperHalfPlane := (hcharts n).2.1
  have hg n : DifferentiableOn ℂ (g n) (D n) := (hcharts n).2.2.1
  have hig n : InjOn (g n) (D n) := (hcharts n).2.2.2.1
  have hFD n : MapsTo (Fn n) upperHalfPlane (D n) := (hcharts n).2.2.2.2.1
  have hgH n : MapsTo (g n) (D n) upperHalfPlane := (hcharts n).2.2.2.2.2.1
  have hgf n : ∀ z ∈ upperHalfPlane, g n (Fn n z) = z := (hcharts n).2.2.2.2.2.2.1
  have hrelation n t (ht : t ∈ Ioc (0 : ℝ) 2) : Fn n (βₙ n t) = αₙ n t := by
    apply OnePoint.coe_injective
    exact (hext n _ (hβH n ht)).symm.trans (hbarα n t ⟨ht.1.le, ht.2⟩)
  have hβHclosed n t (ht : t ∈ Icc (0 : ℝ) 2) : 0 ≤ (βₙ n t).im := by
    by_cases ht0 : t = 0
    · simp only [ht0, hβ0, Complex.zero_im, le_refl]
    · exact (show 0 < (βₙ n t).im from hβH n ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩).le
  have hway n : ‖βₙ n (1 / 2)‖ = 1 ∧ s ≤ (βₙ n (1 / 2)).im := by
    refine ⟨hβnorm n, ?_⟩
    have hnorm := hβnorm n
    rw [hβeq n _ (by norm_num : (1 / 2 : ℝ) ∈ Ioc 0 2), norm_div,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hb n)] at hnorm
    have he : b n = ‖G n (T n) (αₙ n (1 / 2)) - (U n (T n) : ℂ)‖ :=
      ((div_eq_one_iff_eq (hb n).ne').mp hnorm).symm
    rw [hβeq n _ (by norm_num : (1 / 2 : ℝ) ∈ Ioc 0 2), Complex.div_ofReal_im, he]
    exact hangle n
  have homit n : γₙ n (T n) ∉ Fn n '' upperHalfPlane := by
    rintro ⟨z, hz, he⟩
    have hh := hFD n hz
    rw [he] at hh
    exact hh.1.2 ⟨T n, ⟨bot_le, le_rfl⟩, rfl⟩
  obtain ⟨ρ, hρ, hballs⟩ := hclear (1 / 2) (by norm_num) (by norm_num)
  have hwayclear n : ball (αₙ n (1 / 2)) ρ ⊆ D n :=
    hballs n _ (by norm_num)
  obtain ⟨φ, F, α, β, hφ, hF, hiF, hFne, homitlim, hFconv, hαconv, hβconv, hatip,
      hαLlim, hαclim, hαilim, hβlim0, hβlimc, hβlimi, hβlimH, hlimrel⟩ :=
    GuideCompactness.exists_joint_guide_limit_of_clearance P κ hκ hκ8 γ hSLE hcompact
      Fn g D Fb αₙ βₙ (fun n => γₙ n (T n)) C
      (by norm_num) (by norm_num) (by norm_num) hs hρ hc hC
      (fun n => isOpen_survivingDomain (hw n).1 _) hFn hiFn hg hig hFD hgH hgf
      hbar hext hαL hα0 haBound hchord hβc hβ0 hβHclosed hway hwayclear homit
      hrelation hbarα (fun n t ht => hβeq n t ht) hclear
  exact ⟨b, Fb, βₙ, φ, F, α, β, hb, hbar, hext, hβc, hβ0, hβHclosed, hβeq,
    hbarα, hφ, hF, hiF, hFne, homitlim, hFconv, hαconv, hβconv, hatip,
    hαLlim, hαclim, hαilim, hβlim0, hβlimc, hβlimi, hβlimH, hlimrel⟩

end SLEExactGauge

end

end OAI
