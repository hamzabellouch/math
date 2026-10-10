import OAI.Geometry.RCD.Harmonic.RadialTimeReplacement

namespace OAI

/-! # A compressed marginal at a prescribed radial time

Actual CD replacements minimize excess mass at the chosen time. Only the
source capacity enters the resulting bound; bounded endpoint support is
used for compactness, independently of the sharper distortion supports.
-/

open Set Filter Metric MeasureTheory TopologicalSpace
open scoped ENNReal

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
attribute [local instance] pathBorel pathBorelSpace

theorem FullCD.improve_time_saturation
    (μ : Measure X) [SigmaFinite μ]
    (W : Set X) (hW : MeasurableSet W) [IsFiniteMeasure (μ.restrict W)]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C₁ C : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (_hC₁ : C₁ ≠ ∞) (hC : C ≠ ∞) (hCpos : C ≠ 0)
    (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₁ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (s₀ s₁ : Set X) (hs0 : ∀ᵐ x ∂ν₀, x ∈ s₀) (hs1 : ∀ᵐ x ∂ν₁, x ∈ s₁)
    (hn : 2 ≤ n) (t : Time) (β : ℝ≥0∞)
    (hβ : ∀ x ∈ s₀, ∀ y ∈ s₁, β ≤ tau K n (1 - (t : ℝ)) (dist x y))
    (hsupport : ∀ (q : Measure C(Time, X)), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      ∀ᵐ x ∂q.map (fun γ => γ t), x ∈ W)
    (hfill : C⁻¹ ≤ timeSupportFactor n β C₀)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (hpos : transportExcessMass (μ.restrict W) (π.map (fun γ => γ t)) C ≠ 0)
    (hmin : ∀ (π' : Measure C(Time, X)), IsProbabilityMeasure π' →
      (∀ᵐ γ ∂π', IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) →
      transportExcessMass (μ.restrict W) (π.map (fun γ => γ t)) C ≤
        transportExcessMass (μ.restrict W) (π'.map (fun γ => γ t)) C) :
    ∃ π' : Measure C(Time, X), IsProbabilityMeasure π' ∧
      (∀ᵐ γ ∂π', IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) ∧
      transportExcessMass (μ.restrict W) (π'.map (fun γ => γ t)) C =
        transportExcessMass (μ.restrict W) (π.map (fun γ => γ t)) C ∧
      (μ.restrict W) {x | C < (π.map (fun γ => γ t)).rnDeriv (μ.restrict W) x} +
        transportExcessMass (μ.restrict W) (π.map (fun γ => γ t)) C / 2 * C⁻¹ <
      (μ.restrict W) {x | C < (π'.map (fun γ => γ t)).rnDeriv (μ.restrict W) x} := by
  let ν := π.map (fun γ => γ t)
  have hvprob : IsProbabilityMeasure ν :=
    inferInstance
  let e := transportExcessMass (μ.restrict W) ν C
  let v := (μ.restrict W) {x | C < ν.rnDeriv (μ.restrict W) x}
  have hetop : e ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top ν univ)
    (transportExcessMass_le (μ.restrict W) ν C)
  obtain ⟨s, hs, hμs, hνs⟩ := (Measure.mutuallySingular_singularPart ν (μ.restrict W)).symm
  have hthreshold : e / 2 + C * v < ν (s ∪ {x | C < ν.rnDeriv (μ.restrict W) x}) := by
    rw [positive_region_mass (μ.restrict W) ν hC hs hμs hνs]
    exact ENNReal.add_lt_add_right
      (ENNReal.mul_ne_top hC (measure_ne_top (μ.restrict W) _)) (ENNReal.half_lt_self hpos hetop)
  obtain ⟨δ, hδ0, hδtop, hδmass⟩ :=
    exists_buffer_positive_region (μ.restrict W) ν hC s hthreshold
  let B := s ∪ {x | C + δ < ν.rnDeriv (μ.restrict W) x}
  have hB : MeasurableSet B := hs.union
    (measurableSet_lt measurable_const (ν.measurable_rnDeriv (μ.restrict W)))
  have hB0 : ν B ≠ 0 := (lt_of_le_of_lt zero_le hδmass).ne'
  let a := δ / (C + δ)
  have ha : a ≤ 1 := ENNReal.div_le_of_le_mul
    (by simp)
  have ha0 : 0 < a := ENNReal.div_pos hδ0.ne' (ENNReal.add_ne_top.mpr ⟨hC, hδtop⟩)
  have hrem : a • ν.restrict B ≤ ν - C • μ.restrict W :=
    buffer_fraction_le_excess (μ.restrict W) ν hC hδ0 hδtop hs hμs
  let : IsFiniteMeasure (a • ν.restrict B) :=
    isFiniteMeasure_of_le ν (hrem.trans Measure.sub_le)
  obtain ⟨π', η, hπ', hη, hg', hp', heq, hmass, hvol⟩ :=
    hcd.replace_time_region μ K n ν₀ ν₁ hC₀ h0 h1 hm0 hm1 s₀ s₁ hs0 hs1
      hn t β hβ π hg hp B hB hB0 ha0 ha
  let := hπ'
  let := hη
  have hηle : η ≤ π'.map (fun γ => γ t) := by
    rw [heq]
    exact Measure.le_add_left le_rfl
  have hηsupp : ∀ᵐ x ∂η, x ∈ W :=
    (hsupport π' hπ' hg' hp').filter_mono hηle.absolutelyContinuous.ae_le
  have hvolLoc := hvol.trans_eq (ac_support_volume_restrict μ η hW hηsupp)
  have hmin' := hmin π' hπ' hg' hp'
  have hmass' : η univ = (a • ν.restrict B) univ := by
    simpa only [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ] using hmass
  have hequal : transportExcessMass (μ.restrict W) (π'.map (fun γ => γ t)) C = e := by
    apply le_antisymm _ hmin'
    rw [heq]
    exact (transportExcessMass_add_le (μ.restrict W) (ν - a • ν.restrict B) η hC).trans_eq (by
      rw [hmass', transportExcessMass_remove (μ.restrict W) ν (a • ν.restrict B) hC hrem])
  have hsaturated : ∀ᵐ x ∂μ.restrict W, η.rnDeriv (μ.restrict W) x ≠ 0 →
      C < (π'.map (fun γ => γ t)).rnDeriv (μ.restrict W) x := by
    rw [heq]
    apply ac_support_saturated_of_minimizing_replacement (μ.restrict W) ν (a • ν.restrict B) η
      hC hrem hmass'
    simpa only [heq] using hmin'
  refine ⟨π', hπ', hg', hp', hequal, ?_⟩
  have hgain : v + e / 2 * C⁻¹ < ν B * C⁻¹ := by
    have hh := ENNReal.mul_lt_mul_left (ENNReal.inv_ne_zero.mpr hC)
      (ENNReal.inv_ne_top.mpr hCpos) hδmass
    convert hh using 1
    rw [add_mul, mul_assoc, mul_comm v, ← mul_assoc, ENNReal.mul_inv_cancel hCpos hC]
    simp only [one_mul, add_comm]
  exact hgain.trans_le (calc
    ν B * C⁻¹ ≤ ν B * (timeSupportFactor n β C₀) :=
      mul_le_mul_right hfill _
    _ = timeSupportFactor n β C₀ * ν B := by ac_rfl
    _ ≤ (μ.restrict W) {x | η.rnDeriv (μ.restrict W) x ≠ 0} := hvolLoc
    _ ≤ (μ.restrict W) {x | C < (π'.map (fun γ => γ t)).rnDeriv (μ.restrict W) x} :=
      measure_mono_ae hsaturated)



theorem FullCD.time_excess_minimizer_zero
    (μ : Measure X) [SigmaFinite μ]
    (W : Set X) (hW : MeasurableSet W) [IsFiniteMeasure (μ.restrict W)]
    (K : ℝ) (n : ℕ) (hcd : FullCD μ K n) (ν₀ ν₁ : Measure X)
    [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C₁ C : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hC₁ : C₁ ≠ ∞) (hC : C ≠ ∞) (hCpos : C ≠ 0)
    (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₁ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (s₀ s₁ : Set X) (hs0 : ∀ᵐ x ∂ν₀, x ∈ s₀) (hs1 : ∀ᵐ x ∂ν₁, x ∈ s₁)
    (hn : 2 ≤ n) (t : Time) (β : ℝ≥0∞)
    (hβ : ∀ x ∈ s₀, ∀ y ∈ s₁, β ≤ tau K n (1 - (t : ℝ)) (dist x y))
    (hsupport : ∀ (q : Measure C(Time, X)), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      ∀ᵐ x ∂q.map (fun γ => γ t), x ∈ W)
    (hfill : C⁻¹ ≤ timeSupportFactor n β C₀)
    (π : Measure C(Time, X)) [IsProbabilityMeasure π]
    (hg : ∀ᵐ γ ∂π, IsGeodesic γ)
    (hp : IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))))
    (hmin : ∀ (π' : Measure C(Time, X)), IsProbabilityMeasure π' →
      (∀ᵐ γ ∂π', IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) →
      transportExcessMass (μ.restrict W) (π.map (fun γ => γ t)) C ≤
        transportExcessMass (μ.restrict W) (π'.map (fun γ => γ t)) C) :
    transportExcessMass (μ.restrict W) (π.map (fun γ => γ t)) C = 0 := by
  by_contra hpos
  let e := transportExcessMass (μ.restrict W) (π.map (fun γ => γ t)) C
  let A := {ρ : Measure C(Time, X) // IsProbabilityMeasure ρ ∧
    (∀ᵐ γ ∂ρ, IsGeodesic γ) ∧
    IsOptimalCoupling ν₀ ν₁ (ρ.map (fun γ => (γ 0, γ 1))) ∧
    transportExcessMass (μ.restrict W) (ρ.map (fun γ => γ t)) C = e}
  have : Nonempty A := ⟨⟨π, inferInstance, hg, hp, rfl⟩⟩
  let v (ρ : A) := (μ.restrict W) {x | C < (ρ.val.map (fun γ => γ t)).rnDeriv (μ.restrict W) x}
  let S := ⨆ ρ : A, v ρ
  have hS : S ≠ ∞ := ne_top_of_le_ne_top (measure_ne_top (μ.restrict W) univ)
    (iSup_le fun _ => measure_mono (subset_univ _))
  have hstep : S + e / 2 * C⁻¹ ≤ S := by
    rw [ENNReal.iSup_add]
    apply iSup_le
    intro ρ
    let : IsProbabilityMeasure ρ.val := ρ.property.1
    have hposρ : transportExcessMass (μ.restrict W) (ρ.val.map (fun γ => γ t)) C ≠ 0 := by
      rw [ρ.property.2.2.2]
      exact hpos
    have hminρ : ∀ (π' : Measure C(Time, X)), IsProbabilityMeasure π' →
        (∀ᵐ γ ∂π', IsGeodesic γ) →
        IsOptimalCoupling ν₀ ν₁ (π'.map (fun γ => (γ 0, γ 1))) →
        transportExcessMass (μ.restrict W) (ρ.val.map (fun γ => γ t)) C ≤
          transportExcessMass (μ.restrict W) (π'.map (fun γ => γ t)) C := by
      intro π' hπ' hg' hp'
      rw [ρ.property.2.2.2]
      exact hmin π' hπ' hg' hp'
    obtain ⟨π', hπ', hg', hp', hequal, hgain⟩ :=
      hcd.improve_time_saturation μ W hW K n ν₀ ν₁
        hC₀ hC₁ hC hCpos h0 h1 hm0 hm1 s₀ s₁ hs0 hs1 hn t β hβ hsupport hfill
        ρ.val ρ.property.2.1 ρ.property.2.2.1 hposρ hminρ
    let ρ' : A := ⟨π', hπ', hg', hp', hequal.trans ρ.property.2.2.2⟩
    rw [ρ.property.2.2.2] at hgain
    exact hgain.le.trans (le_iSup v ρ')
  have hδ : 0 < e / 2 * C⁻¹ := ENNReal.mul_pos
    (ENNReal.div_pos hpos (by simp)).ne' (ENNReal.inv_ne_zero.mpr hC)
  have hstrict := ENNReal.add_lt_add_left hS hδ
  rw [add_zero] at hstrict
  exact (not_lt_of_ge hstep) hstrict


section Attainment
variable [ProperSpace X] [SeparableSpace X]

theorem FullCD.exists_compressed_time
    (μ : Measure X) [SigmaFinite μ] (K : ℝ) (n : ℕ) (hcd : FullCD μ K n)
    (ν₀ ν₁ : Measure X) [IsProbabilityMeasure ν₀] [IsProbabilityMeasure ν₁]
    {C₀ C₁ C : ℝ≥0∞} (hC₀ : C₀ ≠ ∞) (hC₁ : C₁ ≠ ∞) (hC : C ≠ ∞) (hCpos : C ≠ 0)
    (h0 : ν₀ ≤ C₀ • μ) (h1 : ν₁ ≤ C₁ • μ)
    (hm0 : FiniteSecondMoment ν₀) (hm1 : FiniteSecondMoment ν₁)
    (p : X) {R : ℝ} (hR : 0 ≤ R)
    [IsFiniteMeasure (μ.restrict (closedBall p (3 * R)))]
    [Measure.OuterRegular (μ.restrict (closedBall p (3 * R)))]
    (hs0 : ∀ᵐ x ∂ν₀, dist x p ≤ R) (hs1 : ∀ᵐ x ∂ν₁, dist x p ≤ R)
    (hn : 2 ≤ n) (t : Time) (β : ℝ≥0∞)
    (s₀ s₁ : Set X) (hs₀ : ∀ᵐ x ∂ν₀, x ∈ s₀) (hs₁ : ∀ᵐ x ∂ν₁, x ∈ s₁)
    (hβ : ∀ x ∈ s₀, ∀ y ∈ s₁, β ≤ tau K n (1 - (t : ℝ)) (dist x y))
    (hfill : C⁻¹ ≤ timeSupportFactor n β C₀) :
    ∃ π : Measure C(Time, X), IsProbabilityMeasure π ∧
      (∀ᵐ γ ∂π, IsGeodesic γ) ∧
      IsOptimalCoupling ν₀ ν₁ (π.map (fun γ => (γ 0, γ 1))) ∧
      π.map (fun γ => γ t) ≤ C • μ := by
  let W := closedBall p (3 * R)
  have hW : MeasurableSet W := isClosed_closedBall.measurableSet
  have hsupport : ∀ (q : Measure C(Time, X)), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      ∀ᵐ x ∂q.map (fun γ => γ t), x ∈ W := by
    intro q hq hgq hpq
    apply (ae_map_iff (measurable_path_eval t).aemeasurable hW).mpr
    exact (optimal_geodesic_plan_bounded ν₀ ν₁ q hgq hpq p hR hs0 hs1).mono
      (fun γ hγ => hγ.2 t)
  let v0 : ProbabilityMeasure X := ⟨ν₀, inferInstance⟩
  let v1 : ProbabilityMeasure X := ⟨ν₁, inferInstance⟩
  obtain ⟨q, hq, hgq, hpq, _⟩ := hcd ν₀ ν₁ inferInstance inferInstance
    (Measure.absolutelyContinuous_of_le_smul h0)
    (Measure.absolutelyContinuous_of_le_smul h1) hm0 hm1
  have hne : (OptimalGeodesicPlans v0 v1).Nonempty := ⟨⟨q, hq⟩, hgq, hpq⟩
  obtain ⟨π, hπ, hmπ⟩ := exists_optimal_geodesic_plan_minimizing_excess
    (μ.restrict W) v0 v1 p hR hs0 hs1 hne t hC
  have hmin : ∀ (q : Measure C(Time, X)), IsProbabilityMeasure q →
      (∀ᵐ γ ∂q, IsGeodesic γ) →
      IsOptimalCoupling ν₀ ν₁ (q.map (fun γ => (γ 0, γ 1))) →
      transportExcessMass (μ.restrict W) ((π : Measure C(Time, X)).map (fun γ => γ t)) C ≤
        transportExcessMass (μ.restrict W) (q.map (fun γ => γ t)) C := by
    intro q hq hgq hpq
    exact hmπ ⟨q, hq⟩ ⟨hgq, hpq⟩
  have hz := hcd.time_excess_minimizer_zero μ W hW K n ν₀ ν₁ hC₀ hC₁ hC hCpos
    h0 h1 hm0 hm1 s₀ s₁ hs₀ hs₁ hn t β hβ
    hsupport hfill (π : Measure C(Time, X)) hπ.1 hπ.2 hmin
  refine ⟨π, inferInstance, hπ.1, hπ.2, ?_⟩
  have hs := hsupport (π : Measure C(Time, X)) inferInstance hπ.1 hπ.2
  have ht := localized_excess_zero_iff μ ((π : Measure C(Time, X)).map (fun γ => γ t))
    (B := W) (C := C) hs hC
  exact ht.mp hz

end Attainment
end RegularPointCoordinates

end OAI
