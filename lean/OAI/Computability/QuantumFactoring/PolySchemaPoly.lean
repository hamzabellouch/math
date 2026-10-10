import Mathlib
import OAI.Computability.QuantumFactoring.ConcreteExpressionResources

namespace OAI

section
namespace ExactQuantumFactoring

namespace PolySchemaPoly
variable {v : ℕ → Type*} {a b : ∀ n, PolyExpr (v n)}
lemma coeffs (ha : PolySchemaPoly a) : PolyExprPoly a := by
  simpa only [PolyExpr.comp_X] using ha (fun _=>PolyExpr.X) PolyExprPoly.X
lemma C {r : ∀ n, RatExpr (v n)} (hr : RatExprPoly r) : PolySchemaPoly (fun n => .C (r n)) :=
  fun _ _ => PolyExprPoly.C hr
lemma X : PolySchemaPoly (fun _ => PolyExpr.X : ∀ n, PolyExpr (v n)) := fun _ hb => hb
lemma constant (r : ℚ) : PolySchemaPoly (fun _ => PolyExpr.const r : ∀ n, PolyExpr (v n)) :=
  C (RatExprPoly.constant r)
lemma add (ha : PolySchemaPoly a) (hb : PolySchemaPoly b) :
    PolySchemaPoly (fun n => (a n).add (b n)) := fun c hc => (ha c hc).add (hb c hc)
lemma negation (ha : PolySchemaPoly a) : PolySchemaPoly (fun n => (a n).negation) :=
  fun c hc => (ha c hc).negation
lemma sub (ha : PolySchemaPoly a) (hb : PolySchemaPoly b) :
    PolySchemaPoly (fun n => (a n).sub (b n)) := ha.add hb.negation
lemma mul (ha : PolySchemaPoly a) (hb : PolySchemaPoly b) :
    PolySchemaPoly (fun n => (a n).mul (b n)) := fun c hc => (ha c hc).mul (hb c hc)
lemma pow (ha : PolySchemaPoly a) (k : ℕ) : PolySchemaPoly (fun n => (a n).pow k) := by
  induction k with
  | zero => exact constant 1
  | succ k ih => exact ih.mul ha
lemma comp (ha : PolySchemaPoly a) (hb : PolySchemaPoly b) :
    PolySchemaPoly (fun n => (a n).comp (b n)) := by
  intro c hc
  simpa only [PolyExpr.comp_comp] using ha (fun n => (b n).comp (c n)) (hb c hc)
end PolySchemaPoly

syntax "schema_poly" : tactic
macro_rules
  | `(tactic| schema_poly) => `(tactic|
    with_reducible_and_instances first
    | assumption
    | exact PolySchemaPoly.X
    | exact PolySchemaPoly.constant _
    | (apply PolySchemaPoly.C; expr_poly)
    | (apply PolySchemaPoly.add <;> schema_poly)
    | (apply PolySchemaPoly.sub <;> schema_poly)
    | (apply PolySchemaPoly.mul <;> schema_poly)
    | (apply PolySchemaPoly.negation; schema_poly)
    | (apply PolySchemaPoly.pow; schema_poly)
    | (apply PolySchemaPoly.comp <;> schema_poly))

namespace OrderTrial.Expressions
variable {v : ℕ → Type*} {d Q B j u : ∀ n, NatExpr (v n)}
  {η : ∀ n, RatExpr (v n)} {q q₀ q₁ : ∀ n, IntExpr (v n)}
lemma dynamicRamp_poly (hq : IntExprPoly q) (a : ℤ) :
    PolySchemaPoly (fun n => dynamicRamp (q n) a) := by
  have ha : IntExprPoly (fun _=>IntExpr.ofInt a : ∀ n, IntExpr (v n)) :=
    IntExprPoly.ofInt (PolyBound.const _)
  unfold dynamicRamp
  schema_poly
lemma dynamicRampLin_poly (hq : IntExprPoly q) (a : ℤ) :
    PolySchemaPoly (fun n => dynamicRampLin (q n) a) := by
  have ha : IntExprPoly (fun _=>IntExpr.ofInt a : ∀ n, IntExpr (v n)) :=
    IntExprPoly.ofInt (PolyBound.const _)
  unfold dynamicRampLin
  schema_poly
lemma dynamicSplineRe_poly (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicSplineRe (q n)) := by
  have h0 := dynamicRamp_poly hq 0
  have h2 := dynamicRamp_poly hq 2
  have h4 := dynamicRamp_poly hq 4
  unfold dynamicSplineRe
  schema_poly
lemma dynamicSplineIm_poly (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicSplineIm (q n)) := by
  have h0 := dynamicRamp_poly hq (-1)
  have h2 := dynamicRamp_poly hq 1
  have h4 := dynamicRamp_poly hq 3
  have h5 := dynamicRamp_poly hq 5
  unfold dynamicSplineIm
  schema_poly
lemma dynamicPhaseRe_poly (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicPhaseRe (q n)) := by
  have h0 := dynamicRampLin_poly hq 0
  have h2 := dynamicRampLin_poly hq 2
  have h4 := dynamicRampLin_poly hq 4
  unfold dynamicPhaseRe
  schema_poly
lemma dynamicPhaseIm_poly (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicPhaseIm (q n)) := by
  have h0 := dynamicRampLin_poly hq (-1)
  have h2 := dynamicRampLin_poly hq 1
  have h4 := dynamicRampLin_poly hq 3
  have h5 := dynamicRampLin_poly hq 5
  unfold dynamicPhaseIm
  schema_poly
lemma linearPoly_poly (hd : NatExprPoly d) (hη : RatExprPoly η) :
    PolySchemaPoly (fun n => linearPoly (d n) (η n)) := by
  unfold linearPoly
  schema_poly
lemma integralZero_poly {A : ∀ n, PolyExpr (v n)} (hd : NatExprPoly d) (hA : PolySchemaPoly A) :
    PolySchemaPoly (fun n => integralZero (d n) (A n)) := by
  have hlin := linearPoly_poly hd (RatExprPoly.constant 0)
  unfold integralZero
  schema_poly
lemma integralSlope_poly {A C : ∀ n, PolyExpr (v n)} (hd : NatExprPoly d)
    (hη : RatExprPoly η) (hA : PolySchemaPoly A) (hC : PolySchemaPoly C) :
    PolySchemaPoly (fun n => integralSlope (d n) (η n) (A n) (C n)) := by
  have hlin := linearPoly_poly hd hη
  have hzero := linearPoly_poly hd (RatExprPoly.constant 0)
  unfold integralSlope
  schema_poly
lemma dynamicMassZero_poly (hd : NatExprPoly d) (hq : IntExprPoly q) :
    PolySchemaPoly (fun n => dynamicMassZero (d n) (q n)) :=
  ((integralZero_poly hd (dynamicPhaseRe_poly hq)).pow 2).add
    ((integralZero_poly hd (dynamicPhaseIm_poly hq)).pow 2)
lemma dynamicMassSlope_poly (hd : NatExprPoly d) (hη : RatExprPoly η)
    (hq0 : IntExprPoly q₀) (hq1 : IntExprPoly q₁) :
    PolySchemaPoly (fun n => dynamicMassSlope (d n) (η n) (q₀ n) (q₁ n)) :=
  ((integralSlope_poly hd hη (dynamicSplineRe_poly hq0) (dynamicSplineRe_poly hq1)).pow 2).add
    ((integralSlope_poly hd hη (dynamicSplineIm_poly hq0) (dynamicSplineIm_poly hq1)).pow 2)
lemma dynamicMassCoeff_poly (hd : NatExprPoly d) (hη : RatExprPoly η)
    (hq0 : IntExprPoly q₀) (hq1 : IntExprPoly q₁) (k : ℕ) :
    RatExprPoly (fun n => dynamicMassCoeff (d n) (η n) (q₀ n) (q₁ n) k) :=
  hη.ifEq (RatExprPoly.constant 0) ((dynamicMassZero_poly hd hq0).coeffs k)
    ((dynamicMassSlope_poly hd hη hq0 hq1).coeffs k)
end OrderTrial.Expressions
end ExactQuantumFactoring

end



end OAI
