import Mathlib
import OAI.Computability.QuantumFactoring.ExpressionResources

namespace OAI



section

namespace ExactQuantumFactoring

namespace PolyBound
lemma twoPowSize {f : ℕ → ℕ} (hf : PolyBound f) :
    PolyBound (fun n => (2^(f n)).size) := by
  simpa only [Nat.size_pow] using hf.add (PolyBound.const 1)
end PolyBound

namespace NatExprPoly
variable {v : ℕ → Type*}
lemma ite (p : ℕ → Prop) [∀ n, Decidable (p n)] {a b : ∀ n, NatExpr (v n)}
    (ha : NatExprPoly a) (hb : NatExprPoly b) :
    NatExprPoly (fun n => if p n then a n else b n) := by
  change PolyBound _
  convert PolyBound.ite p ha hb using 1
  funext n; dsimp only; split_ifs <;> rfl
lemma constPoly {f : ℕ → ℕ} (hf : PolyBound f) :
    NatExprPoly (fun n => NatExpr.const (f n) : ∀ n, NatExpr (v n)) := const hf.natSize
end NatExprPoly

/-- All balanced integer components have polynomial literal circuit syntax. -/
def IntExprPoly {v : ℕ → Type*} (a : ∀ n, IntExpr (v n)) : Prop :=
  NatExprPoly (fun n => (a n).pos) ∧ NatExprPoly (fun n => (a n).neg)
namespace IntExprPoly
variable {v : ℕ → Type*} {a b c d : ∀ n, IntExpr (v n)}
lemma ofNat {f : ∀ n, NatExpr (v n)} (hf : NatExprPoly f) :
    IntExprPoly (fun n => IntExpr.ofNat (f n)) :=
  ⟨hf, NatExprPoly.constPoly (PolyBound.const 0)⟩
lemma ofInt {f : ℕ → ℤ} (hf : PolyBound (fun n => (f n).natAbs.size)) :
    IntExprPoly (fun n => IntExpr.ofInt (f n) : ∀ n, IntExpr (v n)) := by
  constructor <;> apply NatExprPoly.const
  · exact hf.of_le (fun n => Nat.size_le_size (by omega))
  · exact hf.of_le (fun n => Nat.size_le_size (by omega))
lemma negation (ha : IntExprPoly a) : IntExprPoly (fun n => (a n).negation) := ⟨ha.2,ha.1⟩
lemma add (ha : IntExprPoly a) (hb : IntExprPoly b) : IntExprPoly (fun n => (a n).add (b n)) :=
  ⟨ha.1.add hb.1,ha.2.add hb.2⟩
lemma sub (ha : IntExprPoly a) (hb : IntExprPoly b) : IntExprPoly (fun n => (a n).sub (b n)) :=
  ha.add hb.negation
lemma mul (ha : IntExprPoly a) (hb : IntExprPoly b) : IntExprPoly (fun n => (a n).mul (b n)) :=
  ⟨(ha.1.mul hb.1).add (ha.2.mul hb.2),(ha.2.mul hb.1).add (ha.1.mul hb.2)⟩
lemma scale {f : ∀ n, NatExpr (v n)} (ha : IntExprPoly a) (hf : NatExprPoly f) :
    IntExprPoly (fun n => (a n).scale (f n)) := ha.mul (ofNat hf)
lemma toNat (ha : IntExprPoly a) : NatExprPoly (fun n => (a n).toNat) := ha.1.sub ha.2
lemma natAbs (ha : IntExprPoly a) : NatExprPoly (fun n => (a n).natAbs) :=
  (ha.1.sub ha.2).add (ha.2.sub ha.1)
lemma iteLe {f g : ∀ n, NatExpr (v n)} (hf : NatExprPoly f) (hg : NatExprPoly g)
    (hc : IntExprPoly c) (hd : IntExprPoly d) :
    IntExprPoly (fun n => IntExpr.iteLe (f n) (g n) (c n) (d n)) :=
  ⟨hf.iteLe hg hc.1 hd.1,hf.iteLe hg hc.2 hd.2⟩
lemma ifLe (ha : IntExprPoly a) (hb : IntExprPoly b)
    (hc : IntExprPoly c) (hd : IntExprPoly d) :
    IntExprPoly (fun n => IntExpr.ifLe (a n) (b n) (c n) (d n)) :=
  iteLe (ha.1.add hb.2) (hb.1.add ha.2) hc hd
lemma ite (p : ℕ → Prop) [∀ n, Decidable (p n)] (ha : IntExprPoly a) (hb : IntExprPoly b) :
    IntExprPoly (fun n => if p n then a n else b n) := by
  constructor
  · convert NatExprPoly.ite p ha.1 hb.1 using 1; funext n; dsimp only; split_ifs <;> rfl
  · convert NatExprPoly.ite p ha.2 hb.2 using 1; funext n; dsimp only; split_ifs <;> rfl
lemma signedPower {f : ℕ → ℕ} (ha : IntExprPoly a) (hf : PolyBound f) :
    IntExprPoly (fun n => (a n).signedPower (f n)) :=
  ite (fun n => Even (f n)) (ofNat (ha.natAbs.pow hf))
    (iteLe ha.2 ha.1 (ofNat (ha.natAbs.pow hf)) (ofNat (ha.natAbs.pow hf)).negation)
lemma ceilRatioNat {f : ∀ n, NatExpr (v n)} (ha : IntExprPoly a) (hf : NatExprPoly f) :
    NatExprPoly (fun n => (a n).ceilRatioNat (f n)) :=
  ((ha.toNat.add hf).sub (NatExprPoly.constPoly (PolyBound.const 1))).div hf
lemma floorRatio {f : ∀ n, NatExpr (v n)} (ha : IntExprPoly a) (hf : NatExprPoly f) :
    IntExprPoly (fun n => (a n).floorRatio (f n)) :=
  (ofNat (ha.toNat.div hf)).sub (ofNat (ha.negation.ceilRatioNat hf))
end IntExprPoly

/-- Polynomial literal numerator and denominator syntax; no bound on dynamic values is assumed. -/
def RatExprPoly {v : ℕ → Type*} (a : ∀ n, RatExpr (v n)) : Prop :=
  IntExprPoly (fun n => (a n).num) ∧ NatExprPoly (fun n => (a n).den)
namespace RatExprPoly
variable {v : ℕ → Type*} {a b c d : ∀ n, RatExpr (v n)}
lemma ofNat {f : ∀ n, NatExpr (v n)} (hf : NatExprPoly f) :
    RatExprPoly (fun n => RatExpr.ofNat (f n)) :=
  ⟨IntExprPoly.ofNat hf,NatExprPoly.constPoly (PolyBound.const 1)⟩
lemma ofInt {f : ∀ n, IntExpr (v n)} (hf : IntExprPoly f) :
    RatExprPoly (fun n => RatExpr.ofInt (f n)) :=
  ⟨hf,NatExprPoly.constPoly (PolyBound.const 1)⟩
lemma const {f : ℕ → ℚ} (hn : PolyBound (fun n => (f n).num.natAbs.size))
    (hd : PolyBound (fun n => (f n).den.size)) :
    RatExprPoly (fun n => RatExpr.const (f n) : ∀ n, RatExpr (v n)) :=
  ⟨IntExprPoly.ofInt hn,NatExprPoly.const hd⟩
lemma constant (r : ℚ) : RatExprPoly (fun _ => RatExpr.const r : ∀ n, RatExpr (v n)) :=
  const (PolyBound.const _) (PolyBound.const _)
lemma normalize (ha : RatExprPoly a) : RatExprPoly (fun n => (a n).normalize) :=
  ⟨IntExprPoly.iteLe ha.2 (NatExprPoly.constPoly (PolyBound.const 0))
    (IntExprPoly.ofInt (PolyBound.const 0)) ha.1,
   ha.2.iteLe (NatExprPoly.constPoly (PolyBound.const 0))
    (NatExprPoly.constPoly (PolyBound.const 1)) ha.2⟩
lemma add (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).add (b n)) :=
  ⟨(ha.normalize.1.scale hb.normalize.2).add (hb.normalize.1.scale ha.normalize.2),
    ha.normalize.2.mul hb.normalize.2⟩
lemma negation (ha : RatExprPoly a) : RatExprPoly (fun n => (a n).negation) := ⟨ha.1.negation,ha.2⟩
lemma sub (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).sub (b n)) :=
  ha.add hb.negation
lemma mul (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).mul (b n)) :=
  ⟨ha.1.mul hb.1,ha.2.mul hb.2⟩
lemma inverse (ha : RatExprPoly a) : RatExprPoly (fun n => (a n).inverse) :=
  ⟨ha.1.scale ha.2,ha.1.natAbs.mul ha.1.natAbs⟩
lemma div (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).div (b n)) :=
  ha.mul hb.inverse
lemma pow (ha : RatExprPoly a) (k : ℕ) : RatExprPoly (fun n => (a n).pow k) := by
  induction k with
  | zero => exact constant 1
  | succ k ih => exact ih.mul ha
lemma signedPower {f : ℕ → ℕ} (ha : RatExprPoly a) (hf : PolyBound f) :
    RatExprPoly (fun n => (a n).signedPower (f n)) := ⟨ha.1.signedPower hf,ha.2.pow hf⟩
lemma repeatedSuccess {f : ℕ → ℕ} (ha : RatExprPoly a) (hf : PolyBound f) :
    RatExprPoly (fun n => (a n).repeatedSuccess (f n)) :=
  (constant 1).sub (((constant 1).sub ha).signedPower hf)
lemma ifNatLe {f g : ∀ n, NatExpr (v n)} (hf : NatExprPoly f) (hg : NatExprPoly g)
    (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifNatLe (f n) (g n) (c n) (d n)) :=
  ⟨IntExprPoly.iteLe hf hg hc.1 hd.1,hf.iteLe hg hc.2 hd.2⟩
lemma ifIntLe {f g : ∀ n, IntExpr (v n)} (hf : IntExprPoly f) (hg : IntExprPoly g)
    (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifIntLe (f n) (g n) (c n) (d n)) :=
  ifNatLe (hf.1.add hg.2) (hg.1.add hf.2) hc hd
lemma ifLe (ha : RatExprPoly a) (hb : RatExprPoly b) (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifLe (a n) (b n) (c n) (d n)) :=
  ifIntLe (ha.normalize.1.scale hb.normalize.2) (hb.normalize.1.scale ha.normalize.2) hc hd
lemma ifLt (ha : RatExprPoly a) (hb : RatExprPoly b) (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifLt (a n) (b n) (c n) (d n)) := hb.ifLe ha hd hc
lemma ifEq (ha : RatExprPoly a) (hb : RatExprPoly b) (hc : RatExprPoly c) (hd : RatExprPoly d) :
    RatExprPoly (fun n => RatExpr.ifEq (a n) (b n) (c n) (d n)) := ha.ifLe hb (hb.ifLe ha hc hd) hd
lemma max (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).max (b n)) :=
  ha.ifLe hb hb ha
lemma min (ha : RatExprPoly a) (hb : RatExprPoly b) : RatExprPoly (fun n => (a n).min (b n)) :=
  ha.ifLe hb ha hb
lemma ceilNat (ha : RatExprPoly a) : NatExprPoly (fun n => (a n).ceilNat) := ha.1.ceilRatioNat ha.2
lemma floor (ha : RatExprPoly a) : IntExprPoly (fun n => (a n).floor) := ha.1.floorRatio ha.2
lemma ceil (ha : RatExprPoly a) : IntExprPoly (fun n => (a n).ceil) := ha.negation.floor.negation
end RatExprPoly
end ExactQuantumFactoring

end



end OAI
