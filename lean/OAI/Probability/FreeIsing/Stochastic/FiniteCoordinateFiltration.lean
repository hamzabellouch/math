import Mathlib

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Problem367

def coordinateFiltration
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (s : ℕ → Set ι) (hs : Monotone s) :
    Filtration ℕ (MeasurableSpace.pi (X := X)) where
  seq n := cylinderEvents (s n)
  mono' _ _ h := cylinderEvents_mono (hs h)
  le' _ := cylinderEvents_le_pi

theorem coordinateFiltration_iSup
    {ι : Type*} {X : ι → Type*} [m : ∀ i, MeasurableSpace (X i)]
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n) :
    (⨆ n, coordinateFiltration (X := X) s hs n) = MeasurableSpace.pi := by
  apply le_antisymm
  · exact iSup_le fun n => (coordinateFiltration s hs).le n
  · change (⨆ i, (m i).comap (fun x : ∀ i, X i => x i)) ≤ _
    refine iSup_le fun i => ?_
    obtain ⟨n, hn⟩ := hex i
    exact le_iSup_of_le n (le_iSup_of_le i (le_iSup_of_le hn le_rfl))

theorem tendsto_ae_coordinate_condExp
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n)
    {f : (∀ i, X i) → ℝ} (hf : Measurable f) (hfi : Integrable f μ) :
    ∀ᵐ x ∂μ, Tendsto (fun n => μ[f | cylinderEvents (s n)] x) atTop (𝓝 (f x)) := by
  apply hfi.tendsto_ae_condExp (ℱ := coordinateFiltration s hs)
  rw [coordinateFiltration_iSup s hs hex]
  exact hf.stronglyMeasurable

theorem tendsto_L1_coordinate_condExp
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n)
    {f : (∀ i, X i) → ℝ} (hf : Measurable f) (hfi : Integrable f μ) :
    Tendsto (fun n => eLpNorm (μ[f | cylinderEvents (s n)] - f) 1 μ) atTop (𝓝 0) := by
  apply hfi.tendsto_eLpNorm_condExp (ℱ := coordinateFiltration s hs)
  rw [coordinateFiltration_iSup s hs hex]
  exact hf.stronglyMeasurable

theorem tendsto_Lp_coordinate_condExp_of_bounded
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n)
    {f : (∀ i, X i) → ℝ} (hf : Measurable f)
    {R : ℝ} (hbound : ∀ᵐ x ∂μ, ‖f x‖ ≤ R)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    Tendsto (fun n => eLpNorm (μ[f | cylinderEvents (s n)] - f) p μ) atTop (𝓝 0) := by
  have hb : ∀ᵐ x ∂μ, ‖f x‖ ≤ ‖R‖ :=
    hbound.mono fun x hx => hx.trans (by exact le_abs_self R)
  have hmem : MemLp f p μ := (memLp_const R).mono hf.aestronglyMeasurable hb
  have hfi : Integrable f μ := hmem.integrable hp
  have hcb (n : ℕ) : ∀ᵐ x ∂μ, ‖μ[f | cylinderEvents (s n)] x‖ ≤ ‖R‖ :=
    ae_bdd_norm_condExp_of_ae_bdd_norm hb
  have hui : UnifIntegrable (fun n => μ[f | cylinderEvents (s n)]) p μ := by
    apply unifIntegrable_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hδε⟩ :=
      unifIntegrable_iff.mp
        (unifIntegrable_const (ι := ℕ) (μ := μ) hp hpt (memLp_const R)) ε hε
    refine ⟨δ, hδ, fun index region hμregion => ?_⟩
    exact (eLpNorm_mono_ae
      (stronglyMeasurable_condExp.mono cylinderEvents_le_pi).aestronglyMeasurable.restrict
      ((hcb index).filter_mono ae_restrict_le)).trans
      (hδε index region hμregion)
  exact tendsto_Lp_finite_of_tendsto_ae hp hpt
    (fun n => (stronglyMeasurable_condExp.mono cylinderEvents_le_pi).aestronglyMeasurable)
    hmem hui (tendsto_ae_coordinate_condExp μ s hs hex hf hfi)

theorem tendsto_Lp_coordinate_condExp
    {ι : Type*} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]
    (μ : Measure (∀ i, X i)) [IsFiniteMeasure μ]
    (s : ℕ → Set ι) (hs : Monotone s) (hex : ∀ i, ∃ n, i ∈ s n)
    {f : (∀ i, X i) → ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) (hmem : MemLp f p μ) :
    Tendsto (fun n => eLpNorm (μ[f | cylinderEvents (s n)] - f) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hδ : ε / 3 ≠ 0 := ENNReal.div_ne_zero.mpr ⟨hε.ne', by norm_num⟩
  obtain ⟨g, hfg, hgm⟩ := hmem.exists_simpleFunc_eLpNorm_sub_lt hpt hδ
  obtain ⟨R, hR⟩ := (g.finite_range.image (fun y : ℝ => ‖y‖)).bddAbove
  have hgb : ∀ᵐ x ∂μ, ‖g x‖ ≤ R := Filter.Eventually.of_forall fun x =>
    hR ⟨g x, ⟨x, rfl⟩, rfl⟩
  have hlim := tendsto_Lp_coordinate_condExp_of_bounded μ s hs hex g.measurable hgb hp hpt
  have hev := ENNReal.tendsto_nhds_zero.mp hlim (ε / 3) (pos_iff_ne_zero.mpr hδ)
  filter_upwards [hev] with n hn
  have hcontract : eLpNorm (μ[f | cylinderEvents (s n)] - μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) p μ ≤
      eLpNorm (f - ⇑g) p μ := by
    rw [← eLpNorm_congr_ae (condExp_sub (hmem.integrable hp) (hgm.integrable hp) (cylinderEvents (s n)))]
    exact eLpNorm_condExp_le_eLpNorm _ hp
  have hdecomp : μ[f | cylinderEvents (s n)] - f =
      (μ[f | cylinderEvents (s n)] - μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) +
      (μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)] - ⇑g) + (⇑g - f) := by
    ext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  calc
    eLpNorm (μ[f | cylinderEvents (s n)] - f) p μ
      = eLpNorm ((μ[f | cylinderEvents (s n)] - μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) +
          (μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)] - ⇑g) + (⇑g - f)) p μ := by rw [hdecomp]
    _ ≤ (eLpNorm (μ[f | cylinderEvents (s n)] - μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)]) p μ +
          eLpNorm (μ[(g : (∀ i, X i) → ℝ) | cylinderEvents (s n)] - ⇑g) p μ) + eLpNorm (⇑g - f) p μ := by
      exact (eLpNorm_add_le hp).trans (add_le_add (eLpNorm_add_le hp) le_rfl)
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
      apply add_le_add
      · exact add_le_add (hcontract.trans hfg.le) hn
      · rw [eLpNorm_sub_comm]
        exact hfg.le
    _ = ε := ENNReal.add_thirds ε

end Problem367

end

end OAI
