import Mathlib
import OAI.Probability.Ballisticity.Estimates.RapidDecay

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

lemma natural_integrable_of_coarse_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℕ) (hf : Measurable f)
    (T : ℕ → ℕ) (hT : ∀ k, ∃ n, k ≤ T n)
    (hs : Summable (fun n => (T (n+1):ℝ)*μ.real {x | T n < f x})) :
    Integrable (fun x => (f x:ℝ)) μ := by
  let F : ℕ → Ω → ℝ≥0∞ := fun n => {x | T n < f x}.indicator (fun _ => (T (n+1):ℝ≥0∞))
  have hE (n : ℕ) : MeasurableSet {x | T n < f x} := measurableSet_lt measurable_const hf
  have hF (n : ℕ) : Measurable (F n) := measurable_const.indicator (hE n)
  have hpoint (x : Ω) : (f x:ℝ≥0∞) ≤ (T 0:ℝ≥0∞)+∑' n,F n x := by
    by_cases hh : f x ≤ T 0
    · exact (by exact_mod_cast hh : (f x:ℝ≥0∞) ≤ T 0).trans (le_add_right le_rfl)
    · have hex := hT (f x)
      have hb := Nat.find_spec hex
      cases hk : Nat.find hex with
      | zero => exact (hh (hk ▸ hb)).elim
      | succ n =>
        have hlo : T n < f x := Nat.lt_of_not_ge (Nat.find_min hex (by omega : n < Nat.find hex))
        have hterm : F n x=(T (n+1):ℝ≥0∞) := Set.indicator_of_mem (show x ∈ {x | T n < f x} from hlo) _
        calc
          _ ≤ (T (n+1):ℝ≥0∞) := by exact_mod_cast (show f x ≤ T (n+1) by simpa only [hk] using hb)
          _ = F n x := hterm.symm
          _ ≤ ∑' i,F i x := ENNReal.le_tsum (f := fun index => F index x) n
          _ ≤ _ := le_add_left le_rfl
  have hIf (n : ℕ) : (∫⁻ x,F n x ∂μ) = (T (n+1):ℝ≥0∞)*μ {x | T n < f x} := by
    dsimp only [F]
    rw [lintegral_indicator (hE n),lintegral_const,Measure.restrict_apply_univ]
  have hfinite : (∑' n,(T (n+1):ℝ≥0∞)*μ {x | T n < f x}) < ⊤ := by
    have he (n : ℕ) : (T (n+1):ℝ≥0∞)*μ {x | T n < f x} =
        ENNReal.ofReal ((T (n+1):ℝ)*μ.real {x | T n < f x}) := by
      rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),ENNReal.ofReal_natCast,measureReal_def,
        ENNReal.ofReal_toReal (measure_ne_top _ _)]
    simp_rw [he]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg) hs]
    exact ENNReal.ofReal_lt_top
  refine ⟨((measurable_of_countable (fun n : ℕ => (n:ℝ))).comp hf).aestronglyMeasurable,
    (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun x => Nat.cast_nonneg (f x)))).mpr ?_⟩
  calc
    (∫⁻ x,ENNReal.ofReal (f x:ℝ) ∂μ) ≤ ∫⁻ x,(T 0:ℝ≥0∞)+∑' n,F n x ∂μ :=
      lintegral_mono (fun x => by simpa only [ENNReal.ofReal_natCast] using hpoint x)
    _ = (T 0:ℝ≥0∞)+∑' n,(T (n+1):ℝ≥0∞)*μ {x | T n < f x} := by
      rw [lintegral_add_left measurable_const,lintegral_const,measure_univ,mul_one,
        lintegral_tsum (fun n => (hF n).aemeasurable)]
      simp_rw [hIf]
    _ < ⊤ := ENNReal.add_lt_top.mpr ⟨ENNReal.natCast_lt_top _,hfinite⟩

lemma natural_integrable_of_polynomial_rapid_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (f : Ω → ℕ) (hf : Measurable f)
    (A q : ℕ) (hA : 0 < A) (hq : 0 < q)
    (ht : RapidDecay (fun n => μ.real {x | A*(n+1)^q < f x})) :
    Integrable (fun x => (f x:ℝ)) μ := by
  apply natural_integrable_of_coarse_tail μ f hf (fun n => A*(n+1)^q)
  · intro k
    refine ⟨k,?_⟩
    have hpow : k+1 ≤ (k+1)^q := by
      obtain ⟨q,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
      rw [pow_succ]
      have hp : 1 ≤ (k+1)^q := Nat.one_le_pow _ _ (by omega)
      nlinarith
    nlinarith
  · have hs := (ht q).mul_left ((A:ℝ)*2^q)
    apply hs.of_norm_bounded
    intro n
    rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg)]
    have hbound : (A*(n+1+1)^q:ℕ) ≤ (A:ℝ)*2^q*(n+1:ℝ)^q := by
      push_cast
      calc
        _ ≤ (A:ℝ)*(2*(n+1:ℝ))^q := mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (by positivity) (by linarith [Nat.cast_nonneg (α := ℝ) n]) _) (Nat.cast_nonneg _)
        _ = _ := by rw [mul_pow,mul_assoc]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hbound
      (show 0 ≤ μ.real {x | A*(n+1)^q < f x} from measureReal_nonneg)

end DirectionalTransience

end

end OAI
