import OAI.Combinatorics.BalancedRyser.Local.ReuseGlobalExtension
import OAI.Combinatorics.BalancedRyser.Probability.PatternMoments

namespace OAI

namespace Balanced.ReuseTower

open scoped BigOperators
noncomputable section
open scoped Classical

section FiniteTower
variable {Ω Y A : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Y] [DecidableEq Y]
  [Fintype A]

theorem uniform_probability_eq_average (E : Ω → Prop) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | E ω}).toReal =
      (∑ ω, if E ω then (1 : ℝ) else 0) / Fintype.card Ω := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, Fintype.card_subtype]
  simp

omit [Fintype Y] [DecidableEq Y] in
theorem fiber_supported (expose : Ω → Y) (a : Ω) :
    ∃ ω ∈ {ω | expose ω = expose a},
      ω ∈ (PMF.uniformOfFintype Ω).support :=
  ⟨a, rfl, PMF.mem_support_uniformOfFintype _⟩

omit [Fintype Y] in
theorem conditional_probability_eq_average (expose : Ω → Y) (a : Ω)
    (E : Ω → Prop) :
    (((PMF.uniformOfFintype Ω).filter {ω | expose ω = expose a}
      (fiber_supported expose a)).toOuterMeasure {ω | E ω}).toReal =
      (∑ ω : {ω // expose ω = expose a}, if E ω then (1 : ℝ) else 0) /
        Fintype.card {ω // expose ω = expose a} := by
  let : Nonempty {ω // expose ω = expose a} := ⟨⟨a, rfl⟩⟩
  let : Nonempty ({ω | expose ω = expose a} : Set Ω) := ⟨⟨a, rfl⟩⟩
  rw [Balanced.uniform_filter_eq_subtype_map, PMF.toOuterMeasure_map_apply]
  exact uniform_probability_eq_average (fun ω : {ω // expose ω = expose a} => E ω)

omit [Nonempty Ω] in
theorem weighted_uniform_fiber_bound (expose : Ω → Y) (Z f : Ω → ℝ) (C : ℝ)
    (hf : ∀ ω, 0 ≤ f ω)
    (hconst : ∀ ω ω', expose ω = expose ω' → f ω = f ω')
    (hbound : ∀ a : Ω,
      (∑ ω : {ω // expose ω = expose a}, Z ω) /
        Fintype.card {ω // expose ω = expose a} ≤ C) :
    (∑ ω, f ω * Z ω) / Fintype.card Ω ≤
      C * ((∑ ω, f ω) / Fintype.card Ω) := by
  have h := PatternMoments.weighted_fiber_bound
    (fun _ : Ω => (1 : ℝ)) Z f expose C hf hconst ?_
  · simpa only [PatternMoments.expectation, one_mul, mul_div_assoc] using
      (div_le_div_of_nonneg_right h (Nat.cast_nonneg (Fintype.card Ω)))
  intro y
  cases isEmpty_or_nonempty {ω // expose ω = y} with
  | inl h =>
      let := h
      simp
  | inr h =>
      obtain ⟨a, ha⟩ := h
      have hb := hbound a
      rw [ha] at hb
      have hcard : (0 : ℝ) < Fintype.card {ω // expose ω = y} := by
        let : Nonempty {ω // expose ω = y} := ⟨⟨a, ha⟩⟩
        exact_mod_cast (Fintype.card_pos (α := {ω // expose ω = y}))
      simpa only [one_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one] using (div_le_iff₀ hcard).mp hb

theorem event_extension_bound (expose : Ω → Y) (E : A → Ω → Prop)
    (P : Ω → Prop) (C : ℝ)
    (hP : ∀ ω ω', expose ω = expose ω' → (P ω ↔ P ω'))
    (hbound : ∀ a : Ω,
      (∑ i : A, (((PMF.uniformOfFintype Ω).filter
        {ω | expose ω = expose a} (fiber_supported expose a)).toOuterMeasure
          {ω | E i ω}).toReal) ≤ C) :
    (∑ i : A, ((PMF.uniformOfFintype Ω).toOuterMeasure
      {ω | P ω ∧ E i ω}).toReal) ≤
      C * ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | P ω}).toReal := by
  simp_rw [uniform_probability_eq_average]
  rw [← Finset.sum_div]
  have h := weighted_uniform_fiber_bound expose
    (fun ω => ∑ i : A, if E i ω then (1 : ℝ) else 0)
    (fun ω => if P ω then (1 : ℝ) else 0) C
    (fun _ => by split_ifs <;> norm_num)
    (fun ω ω' heq => by simp only [hP ω ω' heq]) ?_
  · convert h using 1
    rw [Finset.sum_comm]
    apply congrArg (fun x : ℝ => x / Fintype.card Ω)
    apply Finset.sum_congr rfl
    intro ω _
    by_cases hp : P ω <;> simp [hp]
  intro a
  have hb := hbound a
  simp_rw [conditional_probability_eq_average] at hb
  rw [← Finset.sum_div, Finset.sum_comm] at hb
  exact hb

end FiniteTower
end
end Balanced.ReuseTower

end OAI
