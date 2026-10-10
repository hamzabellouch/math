import OAI.Combinatorics.GraphThreshold.BernoulliUnion

namespace OAI

/-!
# Monotonicity of finite Bernoulli probabilities

For `p ≤ q`, adjoin an independent Bernoulli set to a Bernoulli-`p` set.
The resulting union has parameter `q` and contains the first set. This gives
expectation and event monotonicity, including both endpoints of `[0, 1]`.
-/

noncomputable section
attribute [local instance] Classical.propDecidable

namespace LeanBlast.SecondKahnKalai

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A Bernoulli set with a larger parameter has larger expectation for every
function monotone under inclusion. The function need not be nonnegative. -/
theorem bernoulliExpectation_mono_parameter {p q : ℝ}
    (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1) (F : Finset X → ℝ)
    (hF : ∀ U V, U ⊆ V → F U ≤ F V) :
    bernoulliExpectation p F ≤ bernoulliExpectation q F := by
  have hp1 : p ≤ 1 := hpq.trans hq1
  by_cases hp : p = 1
  · have hq : q = 1 := by linarith
    simp [hp, hq]
  have hp_lt : p < 1 := by
    rcases lt_or_eq_of_le hp1 with hlt | heq
    · exact hlt
    · exact (hp heq).elim
  have hd : 0 < 1 - p := sub_pos.mpr hp_lt
  let r := (q - p) / (1 - p)
  have hr0 : 0 ≤ r := div_nonneg (sub_nonneg.mpr hpq) hd.le
  have hr1 : r ≤ 1 := (div_le_one hd).2 (by linarith)
  have hparam : p + r - p * r = q := by
    dsimp [r]
    field_simp [hd.ne']
    ring
  calc
    bernoulliExpectation p F =
        bernoulliExpectation p (fun U => bernoulliExpectation r (fun _ => F U)) := by
      simp
    _ ≤ bernoulliExpectation p (fun U => bernoulliExpectation r (fun V => F (U ∪ V))) :=
      bernoulliExpectation_mono hp0 hp1 fun U =>
        bernoulliExpectation_mono hr0 hr1 fun V => hF U (U ∪ V) Finset.subset_union_left
    _ = bernoulliExpectation q F := by
      rw [bernoulliExpectation_union, hparam]

/-- Inclusion-monotone events become more likely as the Bernoulli parameter
increases. The proof couples actual independent finite Bernoulli sets. -/
theorem bernoulliProbability_mono_parameter {p q : ℝ}
    (hp0 : 0 ≤ p) (hpq : p ≤ q) (hq1 : q ≤ 1) (P : Finset X → Prop)
    (hP : ∀ U V, U ⊆ V → P U → P V) :
    bernoulliProbability p P ≤ bernoulliProbability q P := by
  rw [bernoulliProbability_eq_expectation, bernoulliProbability_eq_expectation]
  apply bernoulliExpectation_mono_parameter hp0 hpq hq1
  intro U V hUV
  by_cases hu : P U
  · simp [hu, hP U V hUV hu]
  · by_cases hv : P V <;> simp [hu, hv]

end LeanBlast.SecondKahnKalai

end

end OAI
