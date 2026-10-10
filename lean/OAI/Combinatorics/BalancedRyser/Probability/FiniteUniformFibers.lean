import OAI.Combinatorics.BalancedRyser.Probability.ConditionalRestriction

namespace OAI

namespace Balanced.FiniteUniformFibers

open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable

theorem probability_fintype_congr {Ω : Type*} (f g : Fintype Ω) [Nonempty Ω]
    {s t : Set Ω} (h : s = t) :
    ((@PMF.uniformOfFintype Ω f inferInstance).toOuterMeasure s).toReal =
      ((@PMF.uniformOfFintype Ω g inferInstance).toOuterMeasure t).toReal := by
  cases Subsingleton.elim f g
  cases h
  rfl

theorem probability_eq_sum {Ω : Type*} [Fintype Ω] [Nonempty Ω] (E : Ω → Prop) :
    ((PMF.uniformOfFintype Ω).toOuterMeasure {ω | E ω}).toReal =
      (∑ ω, if E ω then (1 : ℝ) else 0) / Fintype.card Ω := by
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast, Fintype.card_subtype, Finset.sum_boole, Set.mem_ofPred_eq]

theorem sum_inter_eq_mul {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    (expose : Ω → Y) (E B : Ω → Prop) (c : ℝ)
    (hE : ∀ x y, expose x = expose y → (E x ↔ E y))
    (hB : ∀ x, (∑ y : {y // expose y = expose x},
      if B y then (1 : ℝ) else 0) =
        c * Fintype.card {y // expose y = expose x}) :
    (∑ x, if E x ∧ B x then (1 : ℝ) else 0) =
      c * ∑ x, if E x then (1 : ℝ) else 0 := by
  classical
  rw [← Fintype.sum_fiberwise expose (fun x => if E x ∧ B x then (1 : ℝ) else 0),
    ← Fintype.sum_fiberwise expose (fun x => if E x then (1 : ℝ) else 0),
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  cases isEmpty_or_nonempty {x // expose x = z} with
  | inl h =>
      let := h
      simp
  | inr h =>
      obtain ⟨x⟩ := h
      have hx (y : {x // expose x = z}) : E y ↔ E x :=
        hE y x (y.property.trans x.property.symm)
      by_cases he : E x
      · have hb := hB x
        rw [x.property] at hb
        simpa only [hx, he, true_and, ite_true, Finset.sum_const,
          Finset.card_univ, nsmul_eq_mul, mul_one] using hb
      · simp only [hx, he, false_and, ite_false, Finset.sum_const_zero, mul_zero]

theorem fixed_probability_inter {D A : Type*} [Fintype D] [Fintype A]
    [DecidableEq D] [Nonempty A] (S : Finset D) (E B : (D → A) → Prop) (c : ℝ)
    (hE : ∀ x y, (∀ d ∈ S, x d = y d) → (E x ↔ E y))
    (hB : ∀ a : D → A,
      ((PMF.uniformOfFintype (ConditionalRestriction.FixedArray (fun d => d ∈ S) a)).toOuterMeasure
        {x | B x.1}).toReal = c) :
    ((PMF.uniformOfFintype (D → A)).toOuterMeasure {x | E x ∧ B x}).toReal =
      c * ((PMF.uniformOfFintype (D → A)).toOuterMeasure {x | E x}).toReal := by
  classical
  let expose : (D → A) → (S → A) := fun x d => x d
  have heq (x y : D → A) : expose x = expose y ↔ ∀ d ∈ S, x d = y d := by
    constructor
    · intro h d hd
      exact congrFun h ⟨d,hd⟩
    · intro h
      funext d
      exact h d d.2
  have hf (a : D → A) :
      (∑ x : {x // expose x = expose a}, if B x then (1 : ℝ) else 0) =
        c * Fintype.card {x // expose x = expose a} := by
    let e : {x // expose x = expose a} ≃
        ConditionalRestriction.FixedArray (fun d => d ∈ S) a :=
      Equiv.subtypeEquivRight (fun x => heq x a)
    let : Nonempty {x // expose x = expose a} := ⟨⟨a,rfl⟩⟩
    have hmap := TupleAlignment.uniform_map_equiv e
    have h := congrArg (fun law => (law.toOuterMeasure
      {x : ConditionalRestriction.FixedArray (fun d => d ∈ S) a | B x.1}).toReal) hmap
    rw [PMF.toOuterMeasure_map_apply] at h
    have hp : ((PMF.uniformOfFintype {x // expose x = expose a}).toOuterMeasure
        {x | B x.1}).toReal = c := h.trans (hB a)
    rw [probability_eq_sum] at hp
    exact (div_eq_iff (by exact_mod_cast Fintype.card_ne_zero)).mp hp
  have hsum := sum_inter_eq_mul expose E B c
    (fun x y h => hE x y ((heq x y).mp h)) (by
      intro x
      convert hf x using 1 <;> congr 1
      · ext y
        simp only [Finset.mem_univ]
      · congr 1
        unfold Fintype.card
        congr 1
        ext y
        simp only [Finset.mem_univ])
  simp only [probability_eq_sum]
  calc
    _ = (c * ∑ x, if E x then (1 : ℝ) else 0) / Fintype.card (D → A) := by
      congr 1
      convert hsum using 1
      congr 1
      funext x
      split_ifs <;> rfl
    _ = _ := by ring

end
end Balanced.FiniteUniformFibers

end OAI
