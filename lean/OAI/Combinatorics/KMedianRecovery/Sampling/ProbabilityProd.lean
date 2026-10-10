import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.Average
import OAI.Combinatorics.KMedianRecovery.Encoding.LabelRange

namespace OAI

namespace MetricKMedianRecovery.FiniteSampling
variable {I Ω Ξ : Type*} [Fintype I] [Fintype Ω] [Fintype Ξ]

lemma probability_prod (E : Ω → Ξ → Prop) :
    probability (fun p : Ω × Ξ => E p.1 p.2) =
      average (fun x => probability (E x)) := by
  classical
  exact average_prod _

lemma probability_prod_lower (P : Ω → Prop) (E : Ω → Ξ → Prop) {p : ℝ}
    (h : ∀ x, P x → p ≤ probability (E x)) :
    probability P * p ≤ probability (fun xy : Ω × Ξ => E xy.1 xy.2) := by
  classical
  rw [probability_prod,probability,← average_mul_const]
  apply average_mono
  intro x
  split_ifs with hx
  · simpa only [one_mul] using h x hx
  · simpa only [zero_mul] using probability_nonneg (E x)

lemma probability_prod_conj (P : Ω → Prop) (Q : Ξ → Prop) :
    probability (fun xy : Ω × Ξ => P xy.1 ∧ Q xy.2) = probability P * probability Q := by
  classical
  rw [probability_prod (fun x y => P x ∧ Q y)]
  have he : (fun x => probability (fun y => P x ∧ Q y)) =
      fun x => (if P x then (1:ℝ) else 0)*probability Q := by
    funext x
    by_cases hx : P x
    · simp only [hx,true_and,ite_true,one_mul]
    · simp only [hx,false_and,ite_false,zero_mul,probability_false]
  rw [he,average_mul_const]
  rfl

lemma average_pi_restrict [DecidableEq I] [Nonempty Ω] (Q : Finset I)
    (X : (↥Q → Ω) → ℝ) :
    average (fun seed : I → Ω => X (fun i => seed i)) = average X := by
  classical
  rw [average_equiv (Equiv.piEquivPiSubtypeProd (fun i => i ∈ Q) (fun _ => Ω))
    (fun seed : I → Ω => X (fun i => seed i)) (fun p => X p.1) (fun _ => rfl),average_prod]
  simp

lemma probability_pi_restrict [DecidableEq I] [Nonempty Ω] (Q : Finset I)
    (E : (↥Q → Ω) → Prop) :
    probability (fun seed : I → Ω => E (fun i => seed i)) = probability E := by
  classical
  exact average_pi_restrict Q (fun x => if E x then 1 else 0)

lemma probability_uniform_fun [DecidableEq I] (b : ℕ) (E : (I → Fin b) → Prop)
    [DecidablePred E] :
    probability E = ∑ seed : I → Fin b,
      if E seed then (1/(b:ℝ))^(Fintype.card I) else 0 := by
  classical
  rw [probability,average,Fintype.expect_eq_sum_div_card,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro s _
  simp only [Fintype.card_fun,Fintype.card_fin,Nat.cast_pow]
  split_ifs <;> simp

end MetricKMedianRecovery.FiniteSampling

namespace MetricKMedianRecovery.ColorLabel
open FiniteSampling
variable {I : Type*} [Fintype I] [DecidableEq I]

lemma color_event_probability (Q : Finset I) (required : I → Fin 3) :
    (1/4:ℝ)^Q.card ≤ probability (fun seed : I → Fin 4 =>
      ∀ i ∈ Q, color (seed i) = required i) := by
  rw [probability_uniform_fun]
  exact specified_color_probability Q required

lemma label_event_probability (B : Finset I) (b : ℕ) (hb : 0 < b) (hB : B.card = b) :
    (1/(2*Real.exp 1))^b ≤ probability (fun seed : I → Fin (labelRange b) =>
      Set.InjOn (fun i => label b hb (seed i)) (↑B)) := by
  classical
  have hr : 0 < labelRange b := pow_pos (by omega) _
  let : Nonempty (Fin (labelRange b)) := ⟨⟨0,hr⟩⟩
  have hrestrict : probability (fun seed : I → Fin (labelRange b) =>
        Set.InjOn (fun i => label b hb (seed i)) (↑B)) =
      probability (fun seed : ↥B → Fin (labelRange b) =>
        Function.Injective (fun i => label b hb (seed i))) := by
    rw [← probability_pi_restrict B (fun seed : ↥B → Fin (labelRange b) =>
      Function.Injective (fun i => label b hb (seed i)))]
    apply probability_congr
    intro seed
    constructor
    · intro h i j hij
      exact Subtype.ext (h i.property j.property hij)
    · intro h i hi j hj hij
      exact congrArg Subtype.val (h (a₁ := ⟨i,hi⟩) (a₂ := ⟨j,hj⟩) hij)
  rw [hrestrict]
  let e : ↥B ≃ Fin b := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe,Fintype.card_fin] using hB)
  let ee : (↥B → Fin (labelRange b)) ≃ (Fin b → Fin (labelRange b)) :=
    { toFun := fun f i => f (e.symm i)
      invFun := fun f i => f (e i)
      left_inv := by intro f; funext i; simp
      right_inv := by intro f; funext i; simp }
  have he (seed : ↥B → Fin (labelRange b)) :
      Function.Injective (fun i => label b hb (seed i)) ↔
      Function.Injective (fun i => label b hb (ee seed i)) := by
    constructor
    · intro hi i j hij
      exact e.symm.injective (hi hij)
    · intro hi i j hij
      apply e.injective
      apply hi
      simpa only [ee,Equiv.coe_fn_mk,e.symm_apply_apply] using hij
  have hev : probability (fun seed : ↥B → Fin (labelRange b) =>
        Function.Injective (fun i => label b hb (seed i))) =
      binaryDistinctMass b hb := by
    unfold probability
    rw [average_equiv ee _
      (fun seed => if Function.Injective (fun i => label b hb (seed i)) then 1 else 0)
      (fun seed => by simp only [he seed])]
    have hu := probability_uniform_fun (I := Fin b) (labelRange b)
      (fun seed => Function.Injective (fun i => label b hb (seed i)))
    simp only [probability,Fintype.card_fin,binaryDistinctMass] at hu ⊢
    convert hu using 1
    apply average_congr
    intro seed
    split_ifs <;> rfl
  rw [hev]
  exact binary_distinct_probability b hb

end MetricKMedianRecovery.ColorLabel

end OAI
