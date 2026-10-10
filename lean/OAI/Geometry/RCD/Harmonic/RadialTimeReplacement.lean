import OAI.Geometry.RCD.Harmonic.RadialTimeSupport

namespace OAI

/-! # Replacing a radial-time region while retaining its source capacity

The replacement preserves both endpoint marginals. The one-sided CD
support estimate holds at the chosen time and survives endpoint concentration.
-/

open Set Filter Metric MeasureTheory
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem FullCD.replace_time_region (μ : Measure X) [SigmaFinite μ]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C₁ : ℝ≥0∞} (hC₀ : C₀ ≠ ∞)
    (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₁ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (s₀ s₁ : Set X) (hs0 : ∀ᵐ x ∂ν₀, x ∈ s₀) (hs1 : ∀ᵐ x ∂ν₁, x ∈ s₁)
    (hn : 2 ≤ n) (t : Time) (β : ℝ≥0∞)
    (hβ : ∀ x ∈ s₀, ∀ y ∈ s₁, β ≤ tau K n (1 - (t : ℝ)) (dist x y))
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (B : Set X) (hB : MeasurableSet B)
    (hm : (π.map (fun γ => γ t)) B ≠ 0)
    {a : ℝ≥0∞} (ha0 : 0 < a) (ha1 : a ≤ 1) :
    ∃ π' : Measure C(Time, X), ∃ η : Measure X,
      IsProbabilityMeasure π' ∧ IsFiniteMeasure η ∧
      (∀ᵐ γ ∂π', IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) ∧
      π'.map (fun γ => γ t) =
        π.map (fun γ => γ t) - a • (π.map (fun γ => γ t)).restrict B + η ∧
      η univ = a * (π.map (fun γ => γ t)) B ∧
      timeSupportFactor n β C₀ * (π.map (fun γ => γ t)) B ≤
        μ {x | η.rnDeriv μ x ≠ 0} := by
  let κ := π.restrict ((fun γ => γ t) ⁻¹' B)
  have hκ : κ ≤ π := Measure.restrict_le_self
  have hmass : κ univ = (π.map (fun γ => γ t)) B := by
    rw [Measure.map_apply (measurable_path_eval t) hB]
    exact Measure.restrict_apply_univ _
  have hκ0 : κ univ ≠ 0 := hmass ▸ hm
  have hκtop : κ univ ≠ ∞ := measure_ne_top κ univ
  let : NeZero κ := ⟨by intro he; exact hκ0 (by rw [he]; rfl)⟩
  let η₀ := (κ univ)⁻¹ • κ.map (fun γ => γ 0)
  let η₁ := (κ univ)⁻¹ • κ.map (fun γ => γ 1)
  have htprob : IsProbabilityMeasure ((κ univ)⁻¹ • κ) := inferInstance
  have he0 : (((κ univ)⁻¹ • κ).map (fun γ => γ 0)) = η₀ := Measure.map_smul _ (measurable_path_eval 0).aemeasurable
  have he1 : (((κ univ)⁻¹ • κ).map (fun γ => γ 1)) = η₁ := Measure.map_smul _ (measurable_path_eval 1).aemeasurable
  have hprob0 : IsProbabilityMeasure η₀ := he0 ▸
    inferInstance
  have hprob1 : IsProbabilityMeasure η₁ := he1 ▸
    inferInstance
  have hend := optimalPlan_endpoints ν₀ ν₁ π hp
  have hle0 : κ.map (fun γ => γ 0) ≤ ν₀ := by
    rw [← hend.1]
    exact Measure.map_mono hκ (measurable_path_eval 0)
  have hle1 : κ.map (fun γ => γ 1) ≤ ν₁ := by
    rw [← hend.2]
    exact Measure.map_mono hκ (measurable_path_eval 1)
  have hden0 : η₀ ≤ (C₀ * (κ univ)⁻¹) • μ := fun S => by
    simpa only [η₀, Measure.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_right ((hle0.trans h0) S) (κ univ)⁻¹
  have hden1 : η₁ ≤ (C₁ * (κ univ)⁻¹) • μ := fun S => by
    simpa only [η₁, Measure.smul_apply, smul_eq_mul, mul_assoc, mul_comm, mul_left_comm] using
      mul_le_mul_right ((hle1.trans h1) S) (κ univ)⁻¹
  have hi : (κ univ)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.mpr hκ0
  have hs0' : ∀ᵐ x ∂η₀, x ∈ s₀ := by
    have ht : ∀ᵐ x ∂κ.map (fun γ => γ 0), x ∈ s₀ :=
      hs0.filter_mono hle0.absolutelyContinuous.ae_le
    exact ht.filter_mono Measure.smul_absolutelyContinuous.ae_le
  have hs1' : ∀ᵐ x ∂η₁, x ∈ s₁ := by
    have ht : ∀ᵐ x ∂κ.map (fun γ => γ 1), x ∈ s₁ :=
      hs1.filter_mono hle1.absolutelyContinuous.ae_le
    exact ht.filter_mono Measure.smul_absolutelyContinuous.ae_le
  obtain ⟨τ, hτ, hgτ, hpτ, hvolτ⟩ := hcd.exists_time_ac_support_bound μ η₀ η₁
    hden0 hden1 ((hm0.of_le hle0).smul hi) ((hm1.of_le hle1).smul hi)
    s₀ s₁ hs0' hs1' hn t β hβ
  let := hτ
  have hatop : a ≠ ∞ := ne_top_of_le_ne_top (by simp) ha1
  let q := a * κ univ
  have hq0 : q ≠ 0 := mul_ne_zero ha0.ne' hκ0
  have hqtop : q ≠ ∞ := ENNReal.mul_ne_top hatop hκtop
  have hcancel : q * (κ univ)⁻¹ = a := by
    dsimp only [q]
    rw [mul_assoc, ENNReal.mul_inv_cancel hκ0 hκtop, mul_one]
  have hasub : a • κ ≤ π := by
    calc
      _ ≤ (1 : ℝ≥0∞) • κ := fun S => by
        simpa only [Measure.smul_apply, smul_eq_mul] using mul_le_mul_left ha1 (κ S)
      _ = κ := one_smul _ _
      _ ≤ π := hκ
  have hscaled : IsOptimalCoupling ((a • κ).map (fun γ => γ 0))
      ((a • κ).map (fun γ => γ 1)) ((q • τ).map (fun γ => (γ 0, γ 1))) := by
    have hh := hpτ.smul hq0 hqtop
    simpa only [η₀, η₁, Measure.map_smul _ (measurable_path_eval 0).aemeasurable,
      Measure.map_smul _ (measurable_path_eval 1).aemeasurable, Measure.map_smul _ ((measurable_path_eval 0).prodMk (measurable_path_eval 1)).aemeasurable, smul_smul, hcancel] using hh
  have hgscaled : ∀ᵐ γ ∂(q • τ), IsGeodesic γ :=
    hgτ.filter_mono Measure.smul_absolutelyContinuous.ae_le
  obtain ⟨hprob', hg', hp'⟩ := optimalPlan_replace_subplan hp hg hasub hscaled hgscaled
  let η := (q • τ).map (fun γ => γ t)
  let : IsFiniteMeasure (q • τ) := ⟨by
    simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact hqtop.lt_top⟩
  have hκmid : κ.map (fun γ => γ t) =
      (π.map (fun γ => γ t)).restrict B :=
    (Measure.restrict_map (measurable_path_eval t) hB).symm
  refine ⟨π - a • κ + q • τ, η, hprob', inferInstance, hg', hp', ?_, ?_, ?_⟩
  · rw [Measure.map_add _ _ (measurable_path_eval t),
      map_sub_of_le π (a • κ) hasub _ (measurable_path_eval t),
      Measure.map_smul _ (measurable_path_eval t).aemeasurable, hκmid]
  · simp only [η, Measure.map_smul _ (measurable_path_eval t).aemeasurable, Measure.smul_apply, smul_eq_mul,
      Measure.map_apply_of_aemeasurable (measurable_path_eval t).aemeasurable
        MeasurableSet.univ, preimage_univ, measure_univ, mul_one, q, hmass]
  · have hsupport : μ {x | η.rnDeriv μ x ≠ 0} =
        μ {x | (τ.map (fun γ => γ t)).rnDeriv μ x ≠ 0} := by
      apply measure_congr
      have hr := Measure.rnDeriv_smul_left_of_ne_top
        (τ.map (fun γ => γ t)) μ hqtop
      change ∀ᵐ x ∂μ, (η.rnDeriv μ x ≠ 0) =
        ((τ.map (fun γ => γ t)).rnDeriv μ x ≠ 0)
      dsimp only [η]
      rw [Measure.map_smul _ (measurable_path_eval t).aemeasurable]
      filter_upwards [hr] with x hx
      rw [hx, Pi.smul_apply, smul_eq_mul]
      rw [mul_ne_zero_iff]
      apply propext
      exact ⟨And.right, fun h => ⟨hq0, h⟩⟩
    rw [hsupport]
    change timeSupportFactor n β (C₀ * (κ univ)⁻¹) ≤ _ at hvolτ
    rw [timeSupportFactor_scale (by omega : 0 < n) β hC₀ hκ0, hmass] at hvolτ
    exact hvolτ

end RegularPointCoordinates

end OAI
