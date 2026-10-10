import Mathlib

namespace OAI

universe u_I u_Ω u_K

noncomputable section

namespace Problem310.SelectorMoment

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

lemma product_eq_pow_active {I : Type u_I} [Fintype I] [DecidableEq I]
    (a : I → Bool) (q : ℝ≥0∞) :
    (∏ i, if a i then q else 1) = q ^ Fintype.card {i // a i = true} := by
  simp [Finset.prod_ite, Fintype.card_subtype]

/-- Exponential moment of the number of active independent Boolean trials. -/
theorem independent_boolean_moment
    {Ω : Type u_Ω} {I : Type u_I} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Bool)
    (X : I → Ω → Bool) (hX : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i)) (hmap : ∀ i, μ.map (X i) = ν)
    (q : ℝ≥0∞) :
    (∫⁻ ω, q ^ Fintype.card {i // X i ω = true} ∂μ) =
      (ν {false} + q * ν {true}) ^ Fintype.card I := by
  classical
  let g : Bool → ℝ≥0∞ := fun b => if b then q else 1
  have hg : Measurable g := measurable_of_countable g
  have hind : iIndepFun (fun i => g ∘ X i) μ := hX.comp (fun _ => g) (fun _ => hg)
  have hsingle (i : I) : (∫⁻ ω, g (X i ω) ∂μ) = ν {false} + q * ν {true} := by
    rw [← lintegral_map hg (hXm i), hmap i, lintegral_fintype]
    simp [g, add_comm]
  calc
    (∫⁻ ω, q ^ Fintype.card {i // X i ω = true} ∂μ) =
        ∫⁻ ω, ∏ i, g (X i ω) ∂μ := by
      apply lintegral_congr
      intro ω
      exact (product_eq_pow_active (fun i => X i ω) q).symm
    _ = ∏ i, ∫⁻ ω, g (X i ω) ∂μ := by
      exact lintegral_prod_eq_prod_lintegral_of_indepFun Finset.univ
        (fun i => g ∘ X i) hind (fun i => hg.comp (hXm i))
    _ = (ν {false} + q * ν {true}) ^ Fintype.card I := by simp_rw [hsingle]; simp

/-- The same moment for injective coordinate lookups in a larger product table. -/
theorem lookup_boolean_moment
    {I : Type u_I} {K : Type u_K} [Fintype I] [DecidableEq I] [Fintype K]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (addr : I → K) (hinj : Function.Injective addr) (q : ℝ≥0∞) :
    (∫⁻ ω : K → Bool, q ^ Fintype.card {i // ω (addr i) = true}
      ∂(Measure.pi (fun _ : K => ν))) =
      (ν {false} + q * ν {true}) ^ Fintype.card I := by
  apply independent_boolean_moment
  · exact iIndepFun.precomp hinj
      (iIndepFun_pi (X := fun _ => id) (fun _ => aemeasurable_id))
  · intro i
    exact measurable_pi_apply (addr i)
  · intro i
    exact (measurePreserving_eval (fun _ : K => ν) (addr i)).map_eq

/-- Fair fresh selector entries, with an arbitrary nonnegative failure factor. -/
theorem lookup_fair_moment
    {I : Type u_I} {K : Type u_K} [Fintype I] [DecidableEq I] [Fintype K]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfalse : ν {false} = 1 / 2) (htrue : ν {true} = 1 / 2)
    (addr : I → K) (hinj : Function.Injective addr) (q : ℝ≥0∞) :
    (∫⁻ ω : K → Bool, q ^ Fintype.card {i // ω (addr i) = true}
      ∂(Measure.pi (fun _ : K => ν))) =
      (1 / 2 + q / 2) ^ Fintype.card I := by
  rw [lookup_boolean_moment ν addr hinj q, hfalse, htrue]
  simp [div_eq_mul_inv]

/-- The exact fixed-scale base, with real parameter p. -/
theorem lookup_fair_failure_moment
    {I : Type u_I} {K : Type u_K} [Fintype I] [DecidableEq I] [Fintype K]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfalse : ν {false} = 1 / 2) (htrue : ν {true} = 1 / 2)
    (addr : I → K) (hinj : Function.Injective addr)
    (p : ℝ) (hp : p ≤ 1) :
    (∫⁻ ω : K → Bool, (ENNReal.ofReal (1 - p)) ^ Fintype.card {i // ω (addr i) = true}
      ∂(Measure.pi (fun _ : K => ν))) =
      (ENNReal.ofReal (1 - p / 2)) ^ Fintype.card I := by
  rw [lookup_fair_moment ν hfalse htrue addr hinj]
  congr 1
  have hdiv (a : ℝ) : ENNReal.ofReal (a / 2) = ENNReal.ofReal a / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hhalf : (1 / 2 : ℝ≥0∞) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [hdiv]
    norm_num
  rw [hhalf, ← hdiv]
  rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (div_nonneg (sub_nonneg.mpr hp) (by norm_num))]
  congr 1
  ring

end Problem310.SelectorMoment

end

end OAI
