import OAI.Probability.DilutedSpin.CompoundPoisson
import OAI.Probability.DilutedSpin.PatternComparison

namespace OAI

section
section
namespace DilutedSpinGlass
open Set

noncomputable def probeLow (j : ℕ) : ℝ := extractionProbe j ^ (j+4)
noncomputable def probeHigh (j : ℕ) : ℝ := 2*probeLow j

lemma extractionProbe_le_quarter (j : ℕ) : extractionProbe j ≤ 1/4 := by
  unfold extractionProbe
  rw [div_le_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+4)]
  have := Nat.cast_nonneg (α := ℝ) j
  linarith

lemma extractionProbe_abs_le_quarter (j : ℕ) : |extractionProbe j| ≤ 1/4 := by
  rw [abs_of_pos (extractionProbe_pos j)]
  exact extractionProbe_le_quarter j

lemma probeLow_pos (j : ℕ) : 0 < probeLow j := pow_pos (extractionProbe_pos j) _
lemma probeLow_lt_high (j : ℕ) : probeLow j < probeHigh j := by
  have := probeLow_pos j
  unfold probeHigh
  linarith
lemma probeHigh_lt_quarter (j : ℕ) : probeHigh j < 1/4 := by
  have hp : probeLow j ≤ (1/4:ℝ)^4 := by
    apply (pow_le_pow_left₀ (extractionProbe_pos j).le (extractionProbe_le_quarter j) (j+4)).trans
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
  unfold probeHigh
  nlinarith

lemma probe_interval_quarter (j : ℕ) :
    Icc (probeLow j) (probeHigh j) ⊆ Icc (-(1:ℝ)/4) (1/4) := by
  intro u hu
  have := probeLow_pos j
  have := probeHigh_lt_quarter j
  exact ⟨by linarith [hu.1],by linarith [hu.2]⟩

end DilutedSpinGlass
end

end

section
namespace DilutedSpinGlass
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [BorelSpace E] [SecondCountableTopology E] in
lemma charFunDual_nnreal_smul (r : ℝ≥0) (μ : Measure E) (L : StrongDual ℝ E) :
    charFunDual ((r:ℝ≥0∞) • μ) L = (r:ℂ)*charFunDual μ L := by
  simp only [charFunDual_apply,integral_smul_measure,ENNReal.coe_toReal,Complex.real_smul]

omit [SecondCountableTopology E] in
lemma charFunDual_add_measure (μ ν : Measure E) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (L : StrongDual ℝ E) : charFunDual (μ+ν) L = charFunDual μ L+charFunDual ν L := by
  have h (ξ : Measure E) [IsFiniteMeasure ξ] :
      Integrable (fun x : E => Complex.exp ((L x:ℂ)*Complex.I)) ξ := by
    apply Integrable.of_bound (by fun_prop) 1
    exact Filter.Eventually.of_forall (fun x => (Complex.norm_exp_ofReal_mul_I _).le)
  exact integral_add_measure (h μ) (h ν)

/-- Superposition of marked Poisson sums follows solely from equality of
 the finite intensity measures. No independence of coordinates of a mark is needed. -/
lemma compoundPoisson_superposition [CompleteSpace E] (s t : ℝ≥0)
    (μ ν τ : Measure E) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure τ]
    (h : ((s+t:ℝ≥0):ℝ≥0∞) • μ = (s:ℝ≥0∞) • ν+(t:ℝ≥0∞) • τ) :
    compoundPoisson (s+t) μ = compoundPoisson s ν ∗ compoundPoisson t τ := by
  apply Measure.ext_of_charFunDual
  funext L
  let : IsFiniteMeasure ((s:ℝ≥0∞) • ν) := inferInstanceAs (IsFiniteMeasure (s • ν))
  let : IsFiniteMeasure ((t:ℝ≥0∞) • τ) := inferInstanceAs (IsFiniteMeasure (t • τ))
  have hh := congrArg (fun ξ : Measure E => charFunDual ξ L) h
  simp only [charFunDual_add_measure,charFunDual_nnreal_smul] at hh
  rw [charFunDual_conv,charFunDual_compoundPoisson,charFunDual_compoundPoisson,
    charFunDual_compoundPoisson,← Complex.exp_add]
  congr 1
  push_cast at hh ⊢
  linear_combination hh

lemma compoundPoisson_add [CompleteSpace E] (s t : ℝ≥0)
    (μ : Measure E) [IsProbabilityMeasure μ] :
    compoundPoisson (s+t) μ = compoundPoisson s μ ∗ compoundPoisson t μ := by
  apply compoundPoisson_superposition
  simp only [ENNReal.coe_add,add_smul]

end DilutedSpinGlass

end

section
namespace DilutedSpinGlass
open Filter
open scoped Topology BigOperators

lemma mixture_double_limit (f : ℕ → ℕ → ℕ → ℝ) (w B : ℕ → ℝ)
    (hw : ∀ k, 0≤w k) (hf : ∀ k L n, 0≤f k L n)
    (hB : ∀ k L n, f k L n≤B k)
    (hs : Summable (fun k => w k*B k))
    (hlim : ∀ k, Tendsto (fun L => limsup (f k L) atTop) atTop (𝓝 0)) :
    Tendsto (fun L => limsup (fun n => ∑' k, w k*f k L n) atTop) atTop (𝓝 0) := by
  have hi (L n : ℕ) : Summable (fun k => w k*f k L n) :=
    hs.of_nonneg_of_le (fun k => mul_nonneg (hw k) (hf k L n))
      (fun k => mul_le_mul_of_nonneg_left (hB k L n) (hw k))
  apply series_double_limit (fun L n => ∑' k, w k*f k L n) f w
    (fun K => ∑' k, w (k+K)*B (k+K))
  · intro L n; exact tsum_nonneg (fun k => mul_nonneg (hw k) (hf k L n))
  · intro L
    refine isBoundedUnder_of_eventually_le (a := ∑' k,w k*B k) (Eventually.of_forall (fun n => ?_))
    exact (hi L n).tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left (hB k L n) (hw k)) hs
  · exact hw
  · intro k L
    exact isBoundedUnder_of_eventually_le (a := B k) (Eventually.of_forall (hB k L))
  · exact hlim
  · exact tendsto_sum_nat_add (fun k => w k*B k)
  · intro K L n
    rw [← (hi L n).sum_add_tsum_nat_add K]
    have he : (∑' k,w (k+K)*f (k+K) L n) ≤ ∑' k,w (k+K)*B (k+K) :=
      ((hi L n).comp_injective (fun _ _ h => Nat.add_right_cancel h)).tsum_le_tsum
        (fun k => mul_le_mul_of_nonneg_left (hB (k+K) L n) (hw (k+K)))
        (hs.comp_injective (fun _ _ h => Nat.add_right_cancel h))
    linarith

end DilutedSpinGlass

end

end OAI
