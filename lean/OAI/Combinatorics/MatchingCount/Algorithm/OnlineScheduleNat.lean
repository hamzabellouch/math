import Mathlib
import OAI.Combinatorics.MatchingCount.Sampling.DiscreteLadderSteps
import OAI.Combinatorics.MatchingCount.Machines.TreeSum

namespace OAI

namespace MatchingFPRAS.TreeTyped
variable {A : Type} [Codec A]
def Realizer.addNat {f g : A→ℕ} (F : Realizer f) (G : Realizer g) :
    Realizer (fun a=>f a+g a) := composition (pair F G) add
def Realizer.mulNat {f g : A→ℕ} (F : Realizer f) (G : Realizer g) :
    Realizer (fun a=>f a*g a) := composition (pair F G) multiply
lemma polynomial_addNat {f g : A→ℕ} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (F.addNat G) :=
  polynomial_composition (polynomial_pair hF hG) polynomial_add
lemma polynomial_mulNat {f g : A→ℕ} {F : Realizer f} {G : Realizer g}
    (hF : PolynomialTime F) (hG : PolynomialTime G) : PolynomialTime (F.mulNat G) :=
  polynomial_composition (polynomial_pair hF hG) polynomial_multiply

def fixedPower : (k : ℕ)→Realizer (fun n : ℕ=>n^k)
  | 0 => (constant 1).congr (by intro n; simp)
  | k+1 => ((fixedPower k).mulNat identity).congr (by intro n; simp [pow_succ])
lemma polynomial_fixedPower (k : ℕ) : PolynomialTime (fixedPower k) := by
  induction k with
  | zero => exact polynomial_congr _ (polynomial_constant 1)
  | succ k ih => exact polynomial_congr _ (polynomial_mulNat ih polynomial_identity)
lemma clog_two_size_pred (n : ℕ) : Nat.clog 2 n=Nat.size (n-1) := by
  apply Nat.le_antisymm
  · apply Nat.clog_le_of_le_pow
    have hp:=Nat.lt_size_self (n-1)
    omega
  · apply Nat.size_le.mpr
    have hp:=Nat.le_pow_clog (by decide : 1<2) n
    have hpos:=Nat.two_pow_pos (Nat.clog 2 n)
    omega
def clogTwo : Realizer (Nat.clog 2) :=
  (composition predecessor bitSize).congr (fun n=>(clog_two_size_pred n).symm)
lemma polynomial_clogTwo : PolynomialTime clogTwo :=
  polynomial_congr _ (polynomial_composition polynomial_predecessor polynomial_bitSize)
end MatchingFPRAS.TreeTyped

namespace MatchingFPRAS.OnlineSchedule
open TreeTyped Transport

def lRealizer : Realizer (fun x : ℕ×ℕ=>ladderL x.1 x.2) :=
  (composition (((constant (10^4)).mulNat first).mulNat second) (fixedPower 100)).congr (fun _=>rfl)
lemma polynomial_l : PolynomialTime lRealizer := by
  unfold lRealizer
  apply polynomial_congr
  exact polynomial_composition (polynomial_mulNat (polynomial_mulNat (polynomial_constant _) polynomial_first)
    polynomial_second) (polynomial_fixedPower _)
def qRealizer : Realizer (fun x : ℕ×ℕ=>ladderQ x.1 x.2) :=
  ((constant 32).mulNat lRealizer).congr (fun _=>rfl)
lemma polynomial_q : PolynomialTime qRealizer :=
  polynomial_congr _ (polynomial_mulNat (polynomial_constant _) polynomial_l)

abbrev ScanInput := ((ℕ×ℕ)×(ℕ×ℕ))×ℕ

def mRealizer : Realizer (fun x : (ℕ×ℕ)×ℕ=>ladderM x.1.1 x.1.2 x.2) :=
  ((second.mulNat (composition (composition first qRealizer) (fixedPower 2))).addNat
    (composition first qRealizer)).congr (fun _=>rfl)
lemma polynomial_m : PolynomialTime mRealizer := by
  unfold mRealizer
  apply polynomial_congr
  exact polynomial_addNat (polynomial_mulNat polynomial_second
    (polynomial_composition (polynomial_composition polynomial_first polynomial_q) (polynomial_fixedPower 2)))
    (polynomial_composition polynomial_first polynomial_q)
def lambdaRealizer : Realizer (fun x : (ℕ×ℕ)×(ℕ×ℕ)=>ladderLambda x.1.1 x.1.2 x.2.1 x.2.2) :=
  (((((constant 10).mulNat first.fst).mulNat (composition first qRealizer)).mulNat
    (second.snd.addNat (constant 1))).mulNat
    ((second.fst.addNat (composition ((first.fst.mulNat first.snd).addNat (constant 2)) clogTwo)).addNat (constant 1))).congr
      (fun _=>rfl)
lemma polynomial_lambda : PolynomialTime lambdaRealizer := by
  unfold lambdaRealizer
  apply polynomial_congr
  exact polynomial_mulNat
    (polynomial_mulNat
      (polynomial_mulNat (polynomial_mulNat (polynomial_constant _) (polynomial_fst polynomial_first))
        (polynomial_composition polynomial_first polynomial_q))
      (polynomial_addNat (polynomial_snd polynomial_second) (polynomial_constant _)))
    (polynomial_addNat
      (polynomial_addNat (polynomial_fst polynomial_second)
        (polynomial_composition
          (polynomial_addNat (polynomial_mulNat (polynomial_fst polynomial_first)
            (polynomial_snd polynomial_first)) (polynomial_constant _)) polynomial_clogTwo))
      (polynomial_constant _))

def scansRealizer : Realizer (fun x : ScanInput=>discreteLadderSteps x.1.1.1 x.1.1.2 x.1.2.1 x.1.2.2 x.2) :=
  ((((constant 20).mulNat (composition first.fst lRealizer)).mulNat
    (composition (pair first.fst first.snd.snd) mRealizer)).mulNat
    (((composition first lambdaRealizer).addNat (composition second clogTwo)).addNat (constant 1))).congr
      (fun _=>rfl)
lemma polynomial_scans : PolynomialTime scansRealizer := by
  unfold scansRealizer
  apply polynomial_congr
  exact polynomial_mulNat
    (polynomial_mulNat
      (polynomial_mulNat (polynomial_constant _)
        (polynomial_composition (polynomial_fst polynomial_first) polynomial_l))
      (polynomial_composition
        (polynomial_pair (polynomial_fst polynomial_first) (polynomial_snd (polynomial_snd polynomial_first)))
        polynomial_m))
    (polynomial_addNat
      (polynomial_addNat (polynomial_composition polynomial_first polynomial_lambda)
        (polynomial_composition polynomial_second polynomial_clogTwo))
      (polynomial_constant _))

end MatchingFPRAS.OnlineSchedule

end OAI
