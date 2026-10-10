import Mathlib

namespace OAI

universe u_1 u_2 u_3

noncomputable section

open MeasureTheory Function
open scoped ENNReal ProbabilityTheory BigOperators

namespace Problem336AdditiveD139.DensityBayes

variable {Ω : Type u_1} {E : Type u_2} [MeasurableSpace Ω] [mE : MeasurableSpace E]

theorem condExp_indicator_of_observation_densities
    (μ : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure E) [SigmaFinite ρ]
    (Y : Ω → E) (hY : Measurable Y) (A : Set Ω) (hA : MeasurableSet A)
    (num den : E → ℝ≥0∞) (hnum : Measurable num) (hden : Measurable den)
    (hden0 : ∀ᵐ y ∂ρ, den y ≠ 0) (hdenTop : ∀ᵐ y ∂ρ, den y ≠ ∞)
    (hnumLaw : Measure.map Y (μ.restrict A) = ρ.withDensity num)
    (hdenLaw : Measure.map Y μ = ρ.withDensity den) :
    μ[A.indicator (fun _ => (1 : ℝ)) | mE.comap Y] =ᵐ[μ]
      (fun ω => (num (Y ω) / den (Y ω)).toReal) := by
  let : IsFiniteMeasure (ρ.withDensity num) := hnumLaw ▸ inferInstance
  have hratio : (ρ.withDensity num).rnDeriv (ρ.withDensity den) =ᵐ[ρ]
      (fun y => num y / den y) := by
    filter_upwards [Measure.rnDeriv_withDensity_right (ρ.withDensity num) ρ
      hden.aemeasurable hden0 hdenTop, Measure.rnDeriv_withDensity ρ hnum]
      with y hy hn
    rw [hy, hn, div_eq_mul_inv, mul_comm]
  have hratioMap : (fun y => ((μ.restrict A).map Y).rnDeriv (μ.map Y) y) =ᵐ[μ.map Y]
      (fun y => num y / den y) := by
    rw [hnumLaw, hdenLaw]
    exact (withDensity_absolutelyContinuous ρ den).ae_eq hratio
  have hmap := toReal_rnDeriv_map ((Measure.restrict_le_self : μ.restrict A ≤ μ).absolutelyContinuous) hY
  have hsource : (fun ω => ((μ.restrict A).rnDeriv μ ω).toReal) =ᵐ[μ]
      A.indicator (fun _ => (1 : ℝ)) := by
    filter_upwards [Measure.rnDeriv_restrict_self μ hA] with ω hω
    rw [hω]
    by_cases hωA : ω ∈ A <;> simp [hωA]
  have hposterior := hmap.trans (condExp_congr_ae hsource)
  filter_upwards [hposterior, ae_of_ae_map hY.aemeasurable hratioMap] with ω hp hr
  rw [← hp, hr]

section FiniteSignal

variable {F : Type u_3} [Fintype F] [MeasurableSpace F] [MeasurableSingletonClass F]

theorem map_eq_withDensity_sum (μ : Measure Ω) (ρ : Measure E)
    (X : Ω → F) (hX : Measurable X) (Y : Ω → E) (hY : Measurable Y)
    (w : F → E → ℝ≥0∞) (hw : ∀ x, Measurable (w x))
    (hAtom : ∀ x, Measure.map Y (μ.restrict (X ⁻¹' {x})) = ρ.withDensity (w x)) :
    Measure.map Y μ = ρ.withDensity (fun y => ∑ x, w x y) := by
  classical
  have hcover : (⋃ x : F, X ⁻¹' {x}) = Set.univ := by
    ext ω
    simp
  have hdisj : Pairwise (Disjoint on (fun x : F => X ⁻¹' {x})) := by
    intro x z hxz
    exact (Set.disjoint_singleton.mpr hxz).preimage X
  have hdecomp := Measure.restrict_iUnion (μ := μ) hdisj
    (fun x => hX (measurableSet_singleton x))
  rw [hcover, Measure.restrict_univ] at hdecomp
  rw [hdecomp, Measure.map_sum hY.aemeasurable]
  simp_rw [hAtom]
  rw [← withDensity_tsum hw]
  congr 1
  funext y
  simp only [tsum_fintype, Finset.sum_apply]

theorem map_restrict_eq_withDensity_sum (μ : Measure Ω) (ρ : Measure E)
    (X : Ω → F) (hX : Measurable X) (Y : Ω → E) (hY : Measurable Y)
    (w : F → E → ℝ≥0∞) (hw : ∀ x, Measurable (w x))
    (hAtom : ∀ x, Measure.map Y (μ.restrict (X ⁻¹' {x})) = ρ.withDensity (w x))
    (C : Set F) [DecidablePred (· ∈ C)] :
    Measure.map Y (μ.restrict (X ⁻¹' C)) =
      ρ.withDensity (fun y => ∑ x, if x ∈ C then w x y else 0) := by
  classical
  apply map_eq_withDensity_sum (μ.restrict (X ⁻¹' C)) ρ X hX Y hY
    (fun x y => if x ∈ C then w x y else 0)
    (fun x => by split_ifs <;> fun_prop)
  intro x
  rw [Measure.restrict_restrict (hX (measurableSet_singleton x))]
  by_cases hx : x ∈ C
  · have heq : X ⁻¹' {x} ∩ X ⁻¹' C = X ⁻¹' {x} := by
      apply Set.inter_eq_left.mpr
      intro ω hω
      change X ω ∈ C
      rw [Set.mem_singleton_iff.mp hω]
      exact hx
    simp only [heq, hx, ite_true]
    exact hAtom x
  · have heq : X ⁻¹' {x} ∩ X ⁻¹' C = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro hω
      simpa [hω] using hx
    simp [heq, hx]

theorem finite_signal_condExp_indicator
    (μ : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure E) [SigmaFinite ρ]
    (X : Ω → F) (hX : Measurable X) (Y : Ω → E) (hY : Measurable Y)
    (w : F → E → ℝ≥0∞) (hw : ∀ x, Measurable (w x))
    (hAtom : ∀ x, Measure.map Y (μ.restrict (X ⁻¹' {x})) = ρ.withDensity (w x))
    (hden0 : ∀ᵐ y ∂ρ, (∑ x, w x y) ≠ 0)
    (hdenTop : ∀ᵐ y ∂ρ, (∑ x, w x y) ≠ ∞)
    (C : Set F) [DecidablePred (· ∈ C)] :
    μ[(X ⁻¹' C).indicator (fun _ => (1 : ℝ)) | mE.comap Y] =ᵐ[μ]
      (fun ω => ((∑ x, if x ∈ C then w x (Y ω) else 0) /
        (∑ x, w x (Y ω))).toReal) := by
  have hnum : Measurable (fun y => ∑ x, if x ∈ C then w x y else 0) := by
    apply Finset.measurable_sum
    intro x _
    by_cases hx : x ∈ C
    · simpa only [hx, ite_true] using hw x
    · simp only [hx, ite_false]
      exact measurable_const
  have hden : Measurable (fun y => ∑ x, w x y) :=
    Finset.measurable_sum _ (fun x _ => hw x)
  exact condExp_indicator_of_observation_densities μ ρ Y hY (X ⁻¹' C)
    (hX (Set.toFinite C).measurableSet)
    (fun y => ∑ x, if x ∈ C then w x y else 0) (fun y => ∑ x, w x y)
    hnum hden hden0 hdenTop
    (map_restrict_eq_withDensity_sum μ ρ X hX Y hY w hw hAtom C)
    (map_eq_withDensity_sum μ ρ X hX Y hY w hw hAtom)

theorem finite_signal_condExp_indicator_real
    (μ : Measure Ω) [IsFiniteMeasure μ] (ρ : Measure E) [SigmaFinite ρ]
    (X : Ω → F) (hX : Measurable X) (Y : Ω → E) (hY : Measurable Y)
    (w : F → E → ℝ) (hw : ∀ x, Measurable (w x))
    (hw0 : ∀ x y, 0 ≤ w x y) (hpos : ∀ y, 0 < ∑ x, w x y)
    (hAtom : ∀ x, Measure.map Y (μ.restrict (X ⁻¹' {x})) =
      ρ.withDensity (fun y => ENNReal.ofReal (w x y)))
    (C : Set F) [DecidablePred (· ∈ C)] :
    μ[(X ⁻¹' C).indicator (fun _ => (1 : ℝ)) | mE.comap Y] =ᵐ[μ]
      (fun ω => (∑ x, if x ∈ C then w x (Y ω) else 0) /
        (∑ x, w x (Y ω))) := by
  have hsum (y : E) : (∑ x, ENNReal.ofReal (w x y)) =
      ENNReal.ofReal (∑ x, w x y) :=
    (ENNReal.ofReal_sum_of_nonneg (fun x _ => hw0 x y)).symm
  have hnum0 (y : E) : 0 ≤ ∑ x, if x ∈ C then w x y else 0 := by
    apply Finset.sum_nonneg
    intro x _
    split_ifs
    · exact hw0 x y
    · exact le_rfl
  have hnum (y : E) : (∑ x, if x ∈ C then ENNReal.ofReal (w x y) else 0) =
      ENNReal.ofReal (∑ x, if x ∈ C then w x y else 0) := by
    rw [ENNReal.ofReal_sum_of_nonneg]
    · apply Finset.sum_congr rfl
      intro x _
      split_ifs <;> simp
    · intro x _
      split_ifs
      · exact hw0 x y
      · exact le_rfl
  have hz : ∀ᵐ y ∂ρ, (∑ x, ENNReal.ofReal (w x y)) ≠ 0 :=
    Filter.Eventually.of_forall (fun y => by
      rw [hsum y]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr (hpos y)))
  have ht : ∀ᵐ y ∂ρ, (∑ x, ENNReal.ofReal (w x y)) ≠ ∞ :=
    Filter.Eventually.of_forall (fun y => by
      rw [hsum y]
      exact ENNReal.ofReal_ne_top)
  have h := finite_signal_condExp_indicator μ ρ X hX Y hY
    (fun x y => ENNReal.ofReal (w x y)) (fun x => (hw x).ennreal_ofReal) hAtom
    hz ht C
  filter_upwards [h] with ω hω
  simpa only [hnum, hsum, ENNReal.toReal_div,
    ENNReal.toReal_ofReal (hnum0 (Y ω)),
    ENNReal.toReal_ofReal (le_of_lt (hpos (Y ω)))] using hω

end FiniteSignal

end Problem336AdditiveD139.DensityBayes

end

end OAI
