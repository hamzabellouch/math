import Mathlib
import OAI.Combinatorics.UniformKServer.ExactOptimum

namespace OAI

                               
section

/-! A finite additive-offset variant of the same exact rational flow system.
The source permits an arbitrarily large instance-dependent initialization delay.
This auxiliary system allows its horizon-independent finite-law endpoint to be
absorbed in a sufficiently long restart epoch; no main conclusion is assumed.
All original source definitions and their coefficient optimizer are unchanged. -/
namespace UniformKServer.OffsetLP
open EffectiveLP FourierMotzkin
def constraints {n k H : ℕ} [NeZero k] (d : RationalMetric n)
    (u : Config n k) (A : ℚ) : List (EffectiveLP.Row n k H) :=
  [Form.objective.scale (-1)] ++
  (enumerate.flatMap fun wc : Word n H × Config n k => [(massRow wc.1 wc.2).scale (-1)]) ++
  (enumerate.flatMap fun w : Word n H =>
    Form.eqRows ((Form.sum Finset.univ (massRow w)).sub (Form.constant 1))) ++
  (enumerate.flatMap fun c : Config n k =>
    Form.eqRows ((massRow (rootWord n H) c).sub (Form.constant (if c = u then 1 else 0)))) ++
  (enumerate.flatMap fun e : Edge n k H => [(flowRow e.1 e.2.1 e.2.2.1 e.2.2.2).scale (-1)]) ++
  (enumerate.flatMap fun w : Short n H =>
    enumerate.flatMap fun r : Fin n =>
      enumerate.flatMap fun c : Config n k =>
        Form.eqRows ((Form.sum Finset.univ (flowRow w r c)).sub (massRow w.val c))) ++
  (enumerate.flatMap fun w : Short n H =>
    enumerate.flatMap fun r : Fin n =>
      enumerate.flatMap fun c' : Config n k =>
        Form.eqRows ((Form.sum Finset.univ fun c : Config n k =>
          Form.sum Finset.univ fun j : Label c r =>
            if EffectiveLP.step c r j = c' then flowRow w r c j else Form.constant 0).sub (massRow (extend w r) c')) ) ++
  (enumerate.flatMap fun w : Word n H =>
    [((costRow d w).sub (Form.constant (A * OfflineDynamic.optRat d u.val w.val))).sub Form.objective])

-- Exact interpretation of the source constraints, over either rationals or reals.
def Valid {n k H : ℕ} {K : Type*} [Field K] [LinearOrder K]
    (d : RationalMetric n) (u : Config n k) (A : ℚ) (F : BoundedFlow n k H K) (a : K)
    [NeZero k] : Prop :=
  0 ≤ a ∧
  (∀ w c, 0 ≤ F.mass w c) ∧
  (∀ w, ∑ c, F.mass w c = 1) ∧
  (∀ c, F.mass (rootWord n H) c = if c = u then 1 else 0) ∧
  (∀ w r c j, 0 ≤ F.flow w r c j) ∧
  (∀ w r c, ∑ j, F.flow w r c j = F.mass w.val c) ∧
  (∀ w r c', (∑ c, ∑ j, if EffectiveLP.step c r j = c' then F.flow w r c j else 0) = F.mass (extend w r) c') ∧
  (∀ w, (∑ i : Fin w.val.length, ∑ c, ∑ j : Label c w.val[i],
     F.flow (prefixNode w i) w.val[i] c j * (d.distance (c.val j.val) w.val[i] : K)) ≤
       (A : K) * (OfflineDynamic.optRat d u.val w.val : K) + a)

theorem constraints_iff {n k H : ℕ} [NeZero k] {K : Type*} [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] (d : RationalMetric n) (u : Config n k) (A : ℚ)
    (x : Fin (Fintype.card (Variable n k H)+1) → K) :
    Satisfies (constraints d u A) x ↔
      Valid d u A (ofAssignment (Form.recover x)) (FourierMotzkin.objective x) := by
  classical
  unfold constraints
  simp only [satisfies_append, satisfies_flatMap, satisfies_singleton, Form.eqRows_iff]
  simp only [and_assoc]
  change _ ↔ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  apply and_congr
  · simp only [FourierMotzkin.Row.eval_scale, Form.eval_objective,
      Rat.cast_neg, Rat.cast_one, neg_one_mul, neg_nonpos]
  apply and_congr
  · simp only [Prod.forall, FourierMotzkin.Row.eval_scale, Rat.cast_neg,
      Rat.cast_one, neg_one_mul, neg_nonpos, massRow, Form.eval_var, ofAssignment]
  apply and_congr
  · simp only [FourierMotzkin.Row.eval_sub, Form.eval_sum, Form.eval_constant,
      Rat.cast_one, sub_eq_zero, massRow, Form.eval_var, ofAssignment]
  apply and_congr
  · apply forall_congr'
    intro c
    by_cases hc : c = u <;>
      simp only [hc, ite_true, ite_false, FourierMotzkin.Row.eval_sub,
        Form.eval_constant, sub_eq_zero, massRow, Form.eval_var, ofAssignment,
        Rat.cast_one, Rat.cast_zero]
  apply and_congr
  · simp only [Sigma.forall, FourierMotzkin.Row.eval_scale, Rat.cast_neg,
      Rat.cast_one, neg_one_mul, neg_nonpos, flowRow, Form.eval_var, ofAssignment]
  apply and_congr
  · simp only [FourierMotzkin.Row.eval_sub, Form.eval_sum, sub_eq_zero,
      massRow, flowRow, Form.eval_var, ofAssignment]
  apply and_congr
  · simp only [FourierMotzkin.Row.eval_sub, Form.eval_sum, sub_eq_zero,
      massRow, flowRow, Form.eval_var, ofAssignment, eval_if, Form.eval_constant,
      Rat.cast_zero]
  · simp only [FourierMotzkin.Row.eval_sub, eval_costRow, sub_nonpos,
      Form.eval_constant, Rat.cast_mul, Form.eval_objective]
    constructor <;> intro h w <;> have := h w <;> linarith

theorem rational_attainment {n k H : ℕ} [NeZero k] (d : RationalMetric n) (u : Config n k) (A : ℚ)
    (h : ∃ (F : BoundedFlow n k H ℝ) (a : ℝ), Valid d u A F a) :
    ∃ x : Fin (Fintype.card (Variable n k H)+1) → ℚ,
      optimize (Fintype.card (Variable n k H)) (constraints d u A) = some x ∧
      Valid d u A (ofAssignment (Form.recover x)) (FourierMotzkin.objective x) ∧
      ∀ (F : BoundedFlow n k H ℝ) (a : ℝ), Valid d u A F a →
        ((FourierMotzkin.objective x : ℚ) : ℝ) ≤ a := by
  have build (F : BoundedFlow n k H ℝ) (a : ℝ) (hF : Valid d u A F a) :
      Satisfies (constraints d u A) (Form.vector (toAssignment F) a) := by
    apply (constraints_iff d u A _).mpr
    simpa only [Form.recover_vector, Form.objective_vector, toAssignment, ofAssignment] using hF
  obtain ⟨F,a,ha⟩ := h
  have hex : ∃ y : Fin (Fintype.card (Variable n k H)+1) → ℝ,
      0 ≤ FourierMotzkin.objective y ∧ Satisfies (constraints d u A) y :=
    ⟨Form.vector (toAssignment F) a, by simpa only [Form.objective_vector] using ha.1, build F a ha⟩
  obtain ⟨x,hx,hn,hs,hm⟩ := optimize_rational_attainment _ (constraints d u A) hex
  refine ⟨x,hx,(constraints_iff d u A x).mp hs, ?_⟩
  intro F a ha
  simpa only [Form.objective_vector] using hm (Form.vector (toAssignment F) a)
    (by simpa only [Form.objective_vector] using ha.1) (build F a ha)


end UniformKServer.OffsetLP

end


end OAI
