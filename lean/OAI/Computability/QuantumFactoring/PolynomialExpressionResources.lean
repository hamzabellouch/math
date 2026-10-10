import Mathlib
import OAI.Computability.QuantumFactoring.RationalExpressionResources

namespace OAI



section

namespace ExactQuantumFactoring
namespace RatExprPoly
variable {v : ℕ → Type*}
lemma ite (p : ℕ → Prop) [∀ n, Decidable (p n)] {a b : ∀ n, RatExpr (v n)}
    (ha : RatExprPoly a) (hb : RatExprPoly b) :
    RatExprPoly (fun n => if p n then a n else b n) := by
  constructor
  · convert IntExprPoly.ite p ha.1 hb.1 using 1; funext n; dsimp only; split_ifs <;> rfl
  · convert NatExprPoly.ite p ha.2 hb.2 using 1; funext n; dsimp only; split_ifs <;> rfl
lemma sum {f : ℕ → ∀ n, RatExpr (v n)} (hf : ∀ i, RatExprPoly (f i)) (k : ℕ) :
    RatExprPoly (fun n => RatExpr.sum (fun i => f i n) k) := by
  induction k with
  | zero => exact constant 0
  | succ k ih => exact ih.add (hf k)
end RatExprPoly

/-- Every fixed-index coefficient of this family has polynomial syntax. -/
def PolyExprPoly {v : ℕ → Type*} (a : ∀ n, PolyExpr (v n)) : Prop :=
  ∀ k, RatExprPoly (fun n => (a n).coeff k)
namespace PolyExprPoly
variable {v : ℕ → Type*} {a b : ∀ n, PolyExpr (v n)}
lemma C {r : ∀ n, RatExpr (v n)} (hr : RatExprPoly r) : PolyExprPoly (fun n => .C (r n)) := by
  intro k
  by_cases h : k=0
  · simpa only [PolyExpr.coeff,ite_eq_left h] using hr
  · simpa only [PolyExpr.coeff,ite_eq_right h] using (RatExprPoly.constant (v:=v) 0)
lemma X : PolyExprPoly (fun _ => PolyExpr.X : ∀ n, PolyExpr (v n)) := by
  intro k
  by_cases h : k=1
  · simpa only [PolyExpr.coeff,ite_eq_left h] using (RatExprPoly.constant (v:=v) 1)
  · simpa only [PolyExpr.coeff,ite_eq_right h] using (RatExprPoly.constant (v:=v) 0)
lemma constant (r : ℚ) : PolyExprPoly (fun _ => PolyExpr.const r : ∀ n, PolyExpr (v n)) :=
  C (RatExprPoly.constant r)
lemma add (ha : PolyExprPoly a) (hb : PolyExprPoly b) : PolyExprPoly (fun n => (a n).add (b n)) :=
  fun k => (ha k).add (hb k)
lemma negation (ha : PolyExprPoly a) : PolyExprPoly (fun n => (a n).negation) :=
  fun k => (ha k).negation
lemma sub (ha : PolyExprPoly a) (hb : PolyExprPoly b) : PolyExprPoly (fun n => (a n).sub (b n)) :=
  ha.add hb.negation
lemma mul (ha : PolyExprPoly a) (hb : PolyExprPoly b) : PolyExprPoly (fun n => (a n).mul (b n)) :=
  fun k => RatExprPoly.sum (fun i => (ha i).mul (hb (k-i))) (k+1)
lemma pow (ha : PolyExprPoly a) (k : ℕ) : PolyExprPoly (fun n => (a n).pow k) := by
  induction k with
  | zero => exact constant 1
  | succ k ih => exact ih.mul ha
end PolyExprPoly

namespace OrderTrial.Expressions
variable {v : Type*}
lemma coveringPow_maxConst (d : NatExpr v) (k : ℕ) :
    (coveringPow d k).maxConst ≤ max d.maxConst (2^k) := by
  induction k with
  | zero => exact le_max_right _ _
  | succ k ih =>
    have h : 2^k ≤ 2^(k+1) := Nat.pow_le_pow_right (by omega) (by omega)
    exact max_le (max_le (le_max_left _ _) (h.trans (le_max_right _ _)))
      (max_le (ih.trans (max_le_max_left _ h)) (le_max_right _ _))
lemma coveringPow_weight (d : NatExpr v) (k : ℕ) :
    (coveringPow d k).weight ≤ (k+1)*(d.weight+7) := by
  have h := Nat.size_le_size (coveringPow_maxConst d k)
  rw [nat_size_max,Nat.size_pow] at h
  have hh : (coveringPow d k).maxConst.size ≤ d.maxConst.size+k+1 := h.trans (by omega)
  simp only [NatExpr.weight,coveringPow_size,coveringPow_sharedCost]
  nlinarith
lemma coveringPow_poly {v : ℕ → Type*} {d : ∀ n, NatExpr (v n)} {f : ℕ → ℕ}
    (hd : NatExprPoly d) (hf : PolyBound f) :
    NatExprPoly (fun n => coveringPow (d n) (f n)) :=
  ((hf.add (PolyBound.const 1)).mul (PolyBound.add hd (PolyBound.const 7))).of_le
    (fun n => coveringPow_weight (d n) (f n))
end OrderTrial.Expressions

syntax "expr_poly" : tactic
macro_rules
  | `(tactic| expr_poly) => `(tactic|
    with_reducible_and_instances first
    | assumption
    | exact NatExprPoly.var _
    | exact RatExprPoly.constant _
    | exact PolyExprPoly.X
    | exact PolyExprPoly.constant _
    | (apply RatExprPoly.ofNat; expr_poly)
    | (apply RatExprPoly.ofInt; expr_poly)
    | (apply RatExprPoly.normalize; expr_poly)
    | (apply RatExprPoly.add <;> expr_poly)
    | (apply RatExprPoly.sub <;> expr_poly)
    | (apply RatExprPoly.mul <;> expr_poly)
    | (apply RatExprPoly.negation; expr_poly)
    | (apply RatExprPoly.inverse; expr_poly)
    | (apply RatExprPoly.div <;> expr_poly)
    | (apply RatExprPoly.pow; expr_poly)
    | (apply RatExprPoly.ifNatLe <;> expr_poly)
    | (apply RatExprPoly.ifIntLe <;> expr_poly)
    | (apply RatExprPoly.ifLe <;> expr_poly)
    | (apply RatExprPoly.ifLt <;> expr_poly)
    | (apply RatExprPoly.ifEq <;> expr_poly)
    | (apply RatExprPoly.max <;> expr_poly)
    | (apply RatExprPoly.min <;> expr_poly)
    | (apply IntExprPoly.ofNat; expr_poly)
    | (apply IntExprPoly.add <;> expr_poly)
    | (apply IntExprPoly.sub <;> expr_poly)
    | (apply IntExprPoly.mul <;> expr_poly)
    | (apply IntExprPoly.scale <;> expr_poly)
    | (apply IntExprPoly.negation; expr_poly)
    | (apply IntExprPoly.iteLe <;> expr_poly)
    | (apply IntExprPoly.ifLe <;> expr_poly)
    | (apply IntExprPoly.toNat; expr_poly)
    | (apply IntExprPoly.natAbs; expr_poly)
    | (apply IntExprPoly.ceilRatioNat <;> expr_poly)
    | (apply IntExprPoly.floorRatio <;> expr_poly)
    | (apply RatExprPoly.ceilNat; expr_poly)
    | (apply RatExprPoly.floor; expr_poly)
    | (apply RatExprPoly.ceil; expr_poly)
    | (apply PolyExprPoly.C; expr_poly)
    | (apply PolyExprPoly.add <;> expr_poly)
    | (apply PolyExprPoly.sub <;> expr_poly)
    | (apply PolyExprPoly.mul <;> expr_poly)
    | (apply PolyExprPoly.negation; expr_poly)
    | (apply PolyExprPoly.pow; expr_poly)
    | (apply NatExprPoly.add <;> expr_poly)
    | (apply NatExprPoly.sub <;> expr_poly)
    | (apply NatExprPoly.mul <;> expr_poly)
    | (apply NatExprPoly.div <;> expr_poly)
    | (apply NatExprPoly.mod <;> expr_poly)
    | (apply NatExprPoly.iteLe <;> expr_poly)
    | (apply NatExprPoly.const; poly_bound))
end ExactQuantumFactoring

end


end OAI
