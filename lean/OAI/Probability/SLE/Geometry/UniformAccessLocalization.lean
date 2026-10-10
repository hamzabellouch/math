import OAI.Probability.SLE.Gauge.EarlyPassageLocalization

namespace OAI

/-! A common access radius from the converging inverse guides. A fixed
positive guide time has a nonzero limiting parameter value; all sufficiently
late guides therefore cross one common radius while their physical images
stay in the prescribed small ball. This supplies the actual uniform
localization hypotheses used before the first-height restart. -/

noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Metric
open scoped Topology NNReal ENNReal

namespace SLEExactGauge

theorem common_access_guide_radius
    (δ : ℝ) (hδ : 0 < δ)
    (β : ℕ → ℝ → ℂ) (hβc : ∀ n, ContinuousOn (β n) (Icc 0 δ))
    (hβ0 : ∀ n, β n 0 = 0) (hβH : ∀ n t, t ∈ Icc 0 δ → 0 ≤ (β n t).im)
    (z : ℂ) (hz : z ≠ 0) (hconv : Tendsto (fun n => β n δ) atTop (𝓝 z))
    (Fbar : ℕ → ℂ → OnePoint ℂ) (α : ℕ → ℝ → ℂ) (a : ℕ → ℂ)
    (C : ℝ≥0) (hα : ∀ n, LipschitzOnWith C (α n) (Icc 0 δ))
    (hα0 : ∀ n, α n 0 = a n)
    (hmap : ∀ n t, t ∈ Icc 0 δ → Fbar n (β n t) = (α n t : OnePoint ℂ)) :
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ᶠ n in atTop, ∃ S : ℝ, 0 < S ∧ S ≤ δ ∧
      ContinuousOn (β n) (Icc 0 S) ∧ β n 0 = 0 ∧ ‖β n S‖ = b₀ ∧
      (∀ t ∈ Icc 0 S, 0 ≤ (β n t).im) ∧
      ∀ t ∈ Icc 0 S, ∃ w : ℂ, Fbar n (β n t) = (w : OnePoint ℂ) ∧
        ‖w - a n‖ ≤ (C : ℝ) * δ := by
  let b₀ : ℝ := ‖z‖ / 2
  have hb₀ : 0 < b₀ := by dsimp [b₀]; exact half_pos (norm_pos_iff.mpr hz)
  have hzgt : b₀ < ‖z‖ := by dsimp [b₀]; exact half_lt_self (norm_pos_iff.mpr hz)
  have hlarge : ∀ᶠ n in atTop, b₀ < ‖β n δ‖ := hconv.norm.eventually (lt_mem_nhds hzgt)
  refine ⟨b₀, hb₀, ?_⟩
  filter_upwards [hlarge] with n hn
  obtain ⟨S, hS, hnorm⟩ := intermediate_value_Icc hδ.le (hβc n).norm
    (show b₀ ∈ Icc ‖β n 0‖ ‖β n δ‖ by rw [hβ0 n, norm_zero]; exact ⟨hb₀.le, hn.le⟩)
  change ‖β n S‖ = b₀ at hnorm
  have hSpos : 0 < S := by
    by_contra h
    have hS0 : S = 0 := le_antisymm (le_of_not_gt h) hS.1
    rw [hS0, hβ0 n, norm_zero] at hnorm
    exact hb₀.ne' hnorm.symm
  have hsub : Icc 0 S ⊆ Icc 0 δ := Icc_subset_Icc_right hS.2
  refine ⟨S, hSpos, hS.2, (hβc n).mono hsub, hβ0 n, hnorm,
    fun t ht => hβH n t (hsub ht), ?_⟩
  intro t ht
  refine ⟨α n t, hmap n t (hsub ht), ?_⟩
  have hb := (hα n).dist_le_mul t (hsub ht) 0 ⟨le_rfl, hδ.le⟩
  rw [hα0 n, dist_eq_norm] at hb
  have hdist : dist t 0 = t := by rw [Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
  rw [hdist] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (hsub ht).2 C.coe_nonneg)

/-- The common guide radius feeds the already proved actual localization
estimate for every late member of the conformal family. -/
theorem common_access_gives_firstHeight_localization
    (κ : ℝ) (hκ : 0 < κ) (hκ8 : κ < 8) :
    ∃ b C c L₀ : ℝ, 0 < b ∧ 0 < C ∧ 0 < c ∧ 1 < L₀ ∧
    ∀ (Ω : Type*) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (γ : Ω → ℝ≥0 → ℂ), IsOrdinaryChordalSLE κ γ P →
      (∀ ω, Continuous (γ ω)) → (∀ ω, γ ω 0 = 0) → (∀ ω t, 0 ≤ (γ ω t).im) →
    ∀ (F : ℕ → ℂ → ℂ) (Fbar : ℕ → ℂ → OnePoint ℂ),
      (∀ n, DifferentiableOn ℂ (F n) upperHalfPlane) →
      (∀ n, InjOn (F n) upperHalfPlane) →
      (∀ n, ContinuousOn (Fbar n) closedHalfPlane) →
      (∀ n z, z ∈ upperHalfPlane → Fbar n z = (F n z : OnePoint ℂ)) →
    ∀ (δ : ℝ), 0 < δ →
    ∀ (β : ℕ → ℝ → ℂ), (∀ n, ContinuousOn (β n) (Icc 0 δ)) →
      (∀ n, β n 0 = 0) → (∀ n t, t ∈ Icc 0 δ → 0 ≤ (β n t).im) →
    ∀ (z : ℂ), z ≠ 0 → Tendsto (fun n => β n δ) atTop (𝓝 z) →
    ∀ (α : ℕ → ℝ → ℂ) (a : ℕ → ℂ) (Cg : ℝ≥0),
      (∀ n, LipschitzOnWith Cg (α n) (Icc 0 δ)) → (∀ n, α n 0 = a n) →
      (∀ n t, t ∈ Icc 0 δ → Fbar n (β n t) = (α n t : OnePoint ℂ)) →
    ∀ (r : ℝ), 0 < r → (Cg : ℝ) * δ ≤ r →
    ∃ b₀ : ℝ, 0 < b₀ ∧ ∀ᶠ n in atTop,
      ∀ L : ℝ, L₀ ≤ L → ∀ B : ℝ, 0 < B → B / 2 ≤ b₀ * L ^ b → ∀ T : ℝ≥0,
        let σ := fun ω => FirstHeightSupport.boundedFirstHeightTime (γ ω) B T
        P (FirstHeightSupport.stoppedNarrowCertificate γ σ B T \
          EarlyPassageLocalization.stoppedImageEvent γ σ (Fbar n) (a n) (L * r)) ≤
            ENNReal.ofReal (C * L ^ (-c)) := by
  obtain ⟨b, C, c, L₀, hb, hC, hc, hL₀, hloc⟩ :=
    EarlyPassageLocalization.bounded_firstHeight_localization κ hκ hκ8
  refine ⟨b, C, c, L₀, hb, hC, hc, hL₀, ?_⟩
  intro Ω m P hP γ hSLE hγc hγ0 hγH F Fbar hF hinj hbar hext δ hδ β hβc hβ0 hβH
    z hz hconv α a Cg hα hα0 hmap r hr hbound
  obtain ⟨b₀, hb₀, haccess⟩ := common_access_guide_radius δ hδ β hβc hβ0 hβH
    z hz hconv Fbar α a Cg hα hα0 hmap
  refine ⟨b₀, hb₀, ?_⟩
  filter_upwards [haccess] with n hn
  obtain ⟨S, hS, _, hβS, hβzero, hβnorm, hH, himage⟩ := hn
  intro L hL B hB hBL T
  apply hloc Ω P γ hSLE hγc hγ0 hγH (F n) (Fbar n) (hF n) (hinj n) (hbar n)
    (hext n) (a n) r hr (β n) S b₀ hS hb₀ hβS hβzero hβnorm hH _ L hL B hB hBL T
  intro t ht
  obtain ⟨w, he, hw⟩ := himage t ht
  exact ⟨w, he, hw.trans hbound⟩

end SLEExactGauge

end

end OAI
