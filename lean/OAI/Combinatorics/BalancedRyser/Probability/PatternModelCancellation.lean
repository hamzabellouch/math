import OAI.Combinatorics.BalancedRyser.Probability.PatternCancellation
import OAI.Combinatorics.BalancedRyser.Probability.PatternMomentsLemmas

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Balanced.PatternProof

variable (P : PatternModel)

noncomputable def fillFresh (K : Finset P.Color) (x : P.Sample) (a : P.Label)
    (z : (c : ↥(P.support a \ K)) → P.Value c) : P.Sample := by
  classical
  exact fun c => if hc : c ∈ P.support a \ K then z ⟨c, hc⟩ else x c

lemma measurable_fillFresh (K : Finset P.Color) (x : P.Sample) (a : P.Label) :
    Measurable (fillFresh P K x a) := by
  classical
  apply Measurable.of_eval
  intro c
  by_cases hc : c ∈ P.support a \ K
  · simpa [fillFresh, hc] using (measurable_pi_apply (⟨c, hc⟩ : ↥(P.support a \ K)))
  · simp [fillFresh, hc, measurable_const]

lemma measurable_indicator (a : P.Label) : Measurable (P.indicator a) :=
  measurable_const.indicator (P.eventMeasurable a)

lemma indicator_mem_Icc (a : P.Label) (ω : P.Sample) :
    P.indicator a ω ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  by_cases h : ω ∈ P.event a <;> simp [PatternModel.indicator, h]

lemma indicator_fillFresh_eq_fixed (K : Finset P.Color) (x ω : P.Sample) (a : P.Label) :
    P.indicator a (fillFresh P K x a (fun c => ω c)) =
      P.indicator a (P.fixCoordinates K x ω) := by
  classical
  have hcoords : ∀ c ∈ P.support a,
      fillFresh P K x a (fun c => ω c) c = P.fixCoordinates K x ω c := by
    intro c hc
    by_cases hK : c ∈ K <;> simp [fillFresh, PatternModel.fixCoordinates, hc, hK]
  have hmem := P.dependsOn a _ _ hcoords
  simp only [PatternModel.indicator, Set.indicator_apply, hmem]

theorem fixedExpectation_centered_prod_eq_zero
    (K : Finset P.Color) (x : P.Sample) (n : ℕ) (a : Fin n → P.Label)
    (i : Fin n)
    (hisol : ∀ j, i ≠ j → Disjoint (P.support (a i) \ K) (P.support (a j) \ K)) :
    P.fixedExpectation K x (fun ω => ∏ j,
      (P.indicator (a j) ω - P.fixedExpectation K x (P.indicator (a j)))) = 0 := by
  classical
  let : IsProbabilityMeasure P.measure := by
    unfold PatternModel.measure
    infer_instance
  let C : Fin n → Finset P.Color := fun j => P.support (a j) \ K
  let F : (j : Fin n) → ((c : C j) → P.Value c) → ℝ :=
    fun j z => P.indicator (a j) (fillFresh P K x (a j) z)
  have hF (j : Fin n) : Measurable (F j) :=
    (measurable_indicator P (a j)).comp (measurable_fillFresh P K x (a j))
  have hξ : iIndepFun (fun c (ω : P.Sample) => ω c) P.measure := by
    exact iIndepFun_pi (fun _ => aemeasurable_id)
  have hFi (j : Fin n) : Integrable (fun ω : P.Sample => F j (fun c => ω c)) P.measure := by
    apply Integrable.of_mem_Icc 0 1
    · have hm : Measurable (fun ω : P.Sample => fun c : C j => ω c) :=
        Measurable.of_eval (fun color => measurable_pi_apply (color : P.Color))
      exact ((hF j).comp hm).aemeasurable
    · exact Filter.Eventually.of_forall (fun ω => indicator_mem_Icc P (a j) _)
  have hcanc := Balanced.Pattern.integral_centered_pattern_prod_eq_zero
    hξ (fun c => measurable_pi_apply c) C F hF hFi Finset.univ (Finset.mem_univ i)
    (fun j hj => hisol j (Finset.mem_erase.mp hj).1.symm)
  dsimp only [F, C] at hcanc
  simp_rw [indicator_fillFresh_eq_fixed] at hcanc
  simpa only [PatternModel.fixedExpectation] using hcanc

lemma measurable_fixedCoordinates (K : Finset P.Color) (x : P.Sample) :
    Measurable (P.fixCoordinates K x) := by
  classical
  apply Measurable.of_eval
  intro c
  by_cases hc : c ∈ K
  · simp [PatternModel.fixCoordinates, hc, measurable_const]
  · simpa [PatternModel.fixCoordinates, hc] using (measurable_pi_apply c)

lemma fixedExpectation_indicator_mem_Icc (K : Finset P.Color) (x : P.Sample) (a : P.Label) :
    P.fixedExpectation K x (P.indicator a) ∈ Set.Icc (0 : ℝ) 1 := by
  let : IsProbabilityMeasure P.measure := by
    unfold PatternModel.measure
    infer_instance
  have hm : Measurable (fun ω => P.indicator a (P.fixCoordinates K x ω)) :=
    (measurable_indicator P a).comp (measurable_fixedCoordinates P K x)
  have hr := fun ω => indicator_mem_Icc P a (P.fixCoordinates K x ω)
  have hi : Integrable (fun ω => P.indicator a (P.fixCoordinates K x ω)) P.measure :=
    Integrable.of_mem_Icc 0 1 hm.aemeasurable (Filter.Eventually.of_forall hr)
  constructor
  · exact integral_nonneg (fun ω => (hr ω).1)
  · have hb := integral_mono_ae hi (integrable_const (1 : ℝ))
      (Filter.Eventually.of_forall (fun ω => (hr ω).2))
    simpa [PatternModel.fixedExpectation] using hb

theorem abs_fixedExpectation_centered_prod_le
    (K : Finset P.Color) (x : P.Sample) (n : ℕ) (a : Fin n → P.Label) :
    |P.fixedExpectation K x (fun ω => ∏ j,
      (P.indicator (a j) ω - P.fixedExpectation K x (P.indicator (a j))))| ≤
    P.fixedExpectation K x (fun ω => ∏ j,
      (P.indicator (a j) ω + P.fixedExpectation K x (P.indicator (a j)))) := by
  classical
  let : IsProbabilityMeasure P.measure := by
    unfold PatternModel.measure
    infer_instance
  let f : Fin n → P.Sample → ℝ := fun j ω => P.indicator (a j) (P.fixCoordinates K x ω)
  let m : Fin n → ℝ := fun j => P.fixedExpectation K x (P.indicator (a j))
  have hfm (j : Fin n) : Measurable (f j) :=
    (measurable_indicator P (a j)).comp (measurable_fixedCoordinates P K x)
  have hfr (j : Fin n) (ω : P.Sample) : f j ω ∈ Set.Icc (0 : ℝ) 1 :=
    indicator_mem_Icc P (a j) _
  have hmr (j : Fin n) : m j ∈ Set.Icc (0 : ℝ) 1 :=
    fixedExpectation_indicator_mem_Icc P K x (a j)
  have henvm : Measurable (fun ω => ∏ j, (f j ω + m j)) :=
    Finset.measurable_fun_prod _ (fun j _ => (hfm j).add_const (m j))
  have henvr (ω : P.Sample) : (∏ j, (f j ω + m j)) ∈ Set.Icc (0 : ℝ) (2 ^ n) := by
    constructor
    · exact Finset.prod_nonneg (fun j _ => add_nonneg (hfr j ω).1 (hmr j).1)
    · calc
        (∏ j, (f j ω + m j)) ≤ ∏ _j : Fin n, (2 : ℝ) := by
          apply Finset.prod_le_prod₀
          · intro j _
            exact add_nonneg (hfr j ω).1 (hmr j).1
          · intro j _
            have hf := (hfr j ω).2
            have hm := (hmr j).2
            linarith
        _ = 2 ^ n := by simp
  have henvi : Integrable (fun ω => ∏ j, (f j ω + m j)) P.measure :=
    Integrable.of_mem_Icc 0 (2 ^ n) henvm.aemeasurable (Filter.Eventually.of_forall henvr)
  change |∫ ω, ∏ j, (f j ω - m j) ∂P.measure| ≤ ∫ ω, ∏ j, (f j ω + m j) ∂P.measure
  refine abs_integral_le_integral_abs.trans
    (integral_mono_of_nonneg (Filter.Eventually.of_forall (fun _ => abs_nonneg _)) henvi ?_)
  filter_upwards with ω
  rw [Finset.abs_prod]
  apply Finset.prod_le_prod₀
  · intro j _
    exact abs_nonneg _
  · intro j _
    have hf := (hfr j ω).1
    have hm := (hmr j).1
    exact abs_le.mpr ⟨by linarith, by linarith⟩

end Balanced.PatternProof

end OAI
