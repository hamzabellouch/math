import OAI.Probability.DilutedSpin.RawPatternIdentity
import OAI.Probability.DilutedSpin.ReservoirShapeLimit

namespace OAI

section
namespace DilutedSpinGlass
open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory
open scoped BigOperators

/-- The actual independent index/fresh-label sampling for a fixed old replica
array. A fresh label is one whole tree sample, not a new draw at each leaf. -/
noncomputable def insertionCoefficient {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (M : Model p) (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) : ℝ :=
  ∫ z : InteractionSample p,
    (FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)).bind (fun _ => Q))).expect
      (fun w => ∏ a : Fin n, -(z.2.2.1 * ∏ l : Fin p,
        if sel l then z.2.2.2 l (old (w l).1 a)
        else averagedFactor (z.2.2.2 l) (x (w l).2 a))) ∂M.disorder.toMeasure

lemma insertionCoefficient_eq_raw {Z : Type} [Fintype Z] {p n N : ℕ} [NeZero N]
    (M : Model p) (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z)
    (x : Z → Fin n → ℝ) (sel : Fin p → Bool) :
    insertionCoefficient M old Q x sel = rawReplicaMoment M
      (fun l : Fin p => if sel l then oldPatternLaw old else freshPatternLaw Q x) := by
  rw [raw_mixedPatternMoment]
  unfold insertionCoefficient
  apply integral_congr_ae
  filter_upwards [] with z
  let g := fun (l : Fin p) (w : Fin N × Z) (a : Fin n) =>
    if sel l then z.2.2.2 l (old w.1 a) else averagedFactor (z.2.2.2 l) (x w.2 a)
  have he (w : Fin p → Fin N × Z) :
      (∏ a : Fin n,-(z.2.2.1*∏ l : Fin p,g l (w l) a))=
        (-z.2.2.1)^n*∏ l : Fin p,∏ a : Fin n,g l (w l) a := by
    simp only [neg_mul_eq_neg_mul]
    rw [Finset.prod_mul_distrib]
    simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [Finset.prod_comm]
  change ((FiniteLaw.pi (fun _ : Fin p => (FiniteLaw.uniform : FiniteLaw (Fin N)).bind (fun _ => Q))).expect
    (fun w => ∏ a : Fin n,-(z.2.2.1*∏ l : Fin p,g l (w l) a)))=_
  simp_rw [he]
  rw [FiniteLaw.expect_mul_left]
  congr 1
  rw [FiniteLaw.expect_pi_product _ (fun l w => ∏ a : Fin n,g l w a)]
  apply Finset.prod_congr rfl
  intro l _
  rw [FiniteLaw.expect_bind]
  cases h : sel l
  · simp only [g,h,Bool.false_eq_true,↓reduceIte,FiniteLaw.expect_const]
  · simp only [g,h,↓reduceIte,FiniteLaw.expect_const]

lemma insertionCoefficient_combination_nonneg {Z : Type} [Fintype Z]
    {p n N : ℕ} [NeZero N] (M : Model p) (hM : Admissible M) (hn : 1≤n)
    (old : Fin N → Fin n → Spin) (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (j : Fin p) :
    0 ≤ insertionCoefficient M old Q x (fun _ => true) -
      (p:ℝ)*insertionCoefficient M old Q x (fun l => decide (l=j)) +
      ((p-1:ℕ):ℝ)*insertionCoefficient M old Q x (fun _ => false) := by
  simp only [insertionCoefficient_eq_raw,↓reduceIte,Bool.false_eq_true,decide_eq_true_eq]
  exact rawReplica_combination_nonneg M hM hn j _ _

/-- The coefficient sign remains valid after sampling the old tilted tree;
its sampling law is common to the bond, cavity and real insertions. -/
lemma expected_insertionCoefficient_nonneg {Ω Z : Type} [Fintype Ω] [Fintype Z]
    {p n N : ℕ} [NeZero N] (M : Model p) (hM : Admissible M) (hn : 1≤n)
    (P : FiniteLaw Ω) (old : Ω → Fin N → Fin n → Spin)
    (Q : FiniteLaw Z) (x : Z → Fin n → ℝ) (j : Fin p) :
    0 ≤ P.expect (fun w => insertionCoefficient M (old w) Q x (fun _ => true)) -
      (p:ℝ)*P.expect (fun w => insertionCoefficient M (old w) Q x (fun l => decide (l=j))) +
      ((p-1:ℕ):ℝ)*P.expect (fun w => insertionCoefficient M (old w) Q x (fun _ => false)) := by
  rw [← FiniteLaw.expect_mul_left,← FiniteLaw.expect_sub,← FiniteLaw.expect_mul_left,
    ← FiniteLaw.expect_add]
  exact P.expect_nonneg (fun w => insertionCoefficient_combination_nonneg M hM hn (old w) Q x j)

end DilutedSpinGlass

end

end OAI
