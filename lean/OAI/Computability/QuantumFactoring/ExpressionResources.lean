import Mathlib
import OAI.Computability.QuantumFactoring.RationalPowerCircuit
import OAI.Computability.QuantumFactoring.PolyBounds

namespace OAI



section

namespace ExactQuantumFactoring

lemma nat_size_max (a b : ℕ) : (max a b).size = max a.size b.size := by
  rcases le_total a b with h | h
  · rw [max_eq_right h, max_eq_right (Nat.size_le_size h)]
  · rw [max_eq_left h, max_eq_left (Nat.size_le_size h)]

namespace NatExpr
variable {v : Type*}

/-- Actual syntax length, sharing-sensitive compiler cost and constant bit size. -/
def weight (e : NatExpr v) : ℕ := e.size + e.sharedCost + e.maxConst.size
@[simp] lemma weight_var (a : v) : (var a).weight = 2 := rfl
@[simp] lemma weight_const (a : ℕ) : (const (v:=v) a).weight = a.size+2 := by
  simp [weight,size,sharedCost,maxConst]; omega
lemma weight_add (a b : NatExpr v) : (add a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_sub (a b : NatExpr v) : (sub a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_mul (a b : NatExpr v) : (mul a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_div (a b : NatExpr v) : (div a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_mod (a b : NatExpr v) : (mod a b).weight ≤ 2*(a.weight+b.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_iteLe (a b c d : NatExpr v) :
    (iteLe a b c d).weight ≤ 2*(a.weight+b.weight+c.weight+d.weight+1) := by
  simp only [weight,size,sharedCost,maxConst,nat_size_max]; omega
lemma weight_pos (a : NatExpr v) : 0<a.weight := by
  have := a.size_pos
  dsimp only [weight]
  omega
lemma size_le_weight (a : NatExpr v) : a.size ≤ a.weight := by dsimp [weight]; omega
lemma sharedCost_le_weight (a : NatExpr v) : a.sharedCost ≤ a.weight := by dsimp [weight]; omega
lemma constSize_le_weight (a : NatExpr v) : a.maxConst.size ≤ a.weight := by dsimp [weight]; omega
lemma weight_pow (a : NatExpr v) (k : ℕ) :
    (a.pow k).weight ≤ (k+1)*(a.weight+3) := by
  have h := Nat.size_le_size (pow_maxConst a k)
  rw [nat_size_max, Nat.size_one] at h
  have h' : (a.pow k).maxConst.size ≤ a.maxConst.size+1 := h.trans (by omega)
  simp only [weight,pow_size,pow_sharedCost]
  nlinarith
lemma templateWidth_le (a : NatExpr v) (b : ℕ) :
    a.templateWidth b ≤ (b+a.weight+1)*a.weight := by
  exact Nat.mul_le_mul (by have := a.constSize_le_weight; omega) a.size_le_weight

lemma template_weight_count {k b c : ℕ} (a : NatExpr v)
    (vars : v → BooleanNetwork k b) (hc : ∀ i, (vars i).net.count ≤ c) :
    (a.template vars).net.count ≤
      a.weight*(operationBound ((b+a.weight+1)*a.weight)+c+(b+a.weight+1)*a.weight) := by
  have h := a.template_shared_count vars hc
  apply h.trans
  apply Nat.mul_le_mul a.sharedCost_le_weight
  have hw := a.templateWidth_le b
  dsimp [operationBound]
  gcongr
end NatExpr

/-- Uniform polynomial growth of a family of literal natural expressions.
Nothing here bounds the values of dynamic variables or assumes arithmetic is free. -/
def NatExprPoly {v : ℕ → Type*} (f : ∀ n, NatExpr (v n)) : Prop :=
  PolyBound (fun n => (f n).weight)

namespace NatExprPoly
variable {v : ℕ → Type*} {a b c d : ∀ n, NatExpr (v n)}
lemma var (i : ∀ n, v n) : NatExprPoly (fun n => .var (i n)) := by
  simpa only [NatExprPoly,NatExpr.weight_var] using PolyBound.const 2
lemma const {f : ℕ → ℕ} (h : PolyBound (fun n => (f n).size)) :
    NatExprPoly (fun n => NatExpr.const (f n) : ∀ n, NatExpr (v n)) := by
  simpa only [NatExprPoly,NatExpr.weight_const] using h.add (PolyBound.const 2)
lemma add (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .add (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_add (a n) (b n))
lemma sub (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .sub (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_sub (a n) (b n))
lemma mul (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .mul (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_mul (a n) (b n))
lemma div (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .div (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_div (a n) (b n))
lemma mod (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => .mod (a n) (b n)) :=
  ((PolyBound.const 2).mul ((PolyBound.add ha hb).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_mod (a n) (b n))
lemma iteLe (ha : NatExprPoly a) (hb : NatExprPoly b) (hc : NatExprPoly c) (hd : NatExprPoly d) :
    NatExprPoly (fun n => .iteLe (a n) (b n) (c n) (d n)) :=
  ((PolyBound.const 2).mul ((((PolyBound.add ha hb).add hc).add hd).add (PolyBound.const 1))).of_le
    (fun n => NatExpr.weight_iteLe (a n) (b n) (c n) (d n))
lemma pow {f : ℕ → ℕ} (ha : NatExprPoly a) (hf : PolyBound f) :
    NatExprPoly (fun n => (a n).pow (f n)) :=
  ((hf.add (PolyBound.const 1)).mul (PolyBound.add ha (PolyBound.const 3))).of_le
    (fun n => NatExpr.weight_pow (a n) (f n))
lemma templateWidth {f : ℕ → ℕ} (ha : NatExprPoly a) (hf : PolyBound f) :
    PolyBound (fun n => (a n).templateWidth (f n)) :=
  (((hf.add ha).add (PolyBound.const 1)).mul ha).of_le
    (fun n => NatExpr.templateWidth_le (a n) (f n))
end NatExprPoly
end ExactQuantumFactoring

end



end OAI
