import OAI.Probability.SATComputability.ArithmeticEnclosures

namespace OAI

namespace FixedClauseThreshold.Computability.FiniteArithmetic

open Encodable Nat.Partrec RapidForcing.EffectiveProfile RapidForcing.EffectiveArithmetic
open PeriodicLattice.CertifiedReal Filter
open scoped Topology
local instance arithmeticSyntaxRatPrimcodable : Primcodable ℚ := PeriodicLattice.RecursiveArithmetic.ratPrimcodable
local instance arithmeticSyntaxCodeEq : DecidableEq Code := Encodable.decidableEqOfEncodable Code

noncomputable def clampBall (b : Ball) : Ball := ⟨max 1 b.center, b.radius⟩

@[fun_prop] theorem clampBall_computable : Computable clampBall := by
  unfold clampBall
  fun_prop

theorem clampBall_covers {b : Ball} {x : ℝ} (hb : b.Covers x) :
    (clampBall b).Covers (max 1 x) := by
  have h := abs_max_sub_max_le_abs (b.center : ℝ) x 1
  simpa only [clampBall, Ball.Covers, Rat.cast_max, Rat.cast_one, max_comm] using h.trans hb

theorem encloses_clamp {b : ℕ → Ball} {x : ℝ} (hb : Encloses b x) :
    Encloses (fun n => clampBall (b n)) (max 1 x) :=
  ⟨fun n => clampBall_covers (hb.1 n), hb.2⟩

noncomputable def decodedRational (e : Code) : ℚ := (decode (encode e)).getD 0

@[fun_prop] theorem decodedRational_computable : Computable decodedRational := by
  unfold decodedRational
  fun_prop

noncomputable def expressionValue : Code → ℝ
  | .zero => 0
  | .succ => 1
  | .left => 2
  | .right => 3
  | .pair a b => expressionValue a + expressionValue b
  | .comp a b => expressionValue a * expressionValue b
  | .prec tag b => if tag = .zero then (decodedRational b : ℝ)
      else if tag = .succ then Real.exp (expressionValue b)
      else if tag = .left then Real.log (max 1 (expressionValue b))
      else (max 1 (expressionValue b))⁻¹
  | .rfind' a => -expressionValue a

noncomputable def expressionBall : Code → ℕ → Ball
  | .zero, _ => Ball.exact 0
  | .succ, _ => Ball.exact 1
  | .left, _ => Ball.exact 2
  | .right, _ => Ball.exact 3
  | .pair a b, n => (expressionBall a n).add (expressionBall b n)
  | .comp a b, n => (expressionBall a n).mul (expressionBall b n)
  | .prec tag b, n => if tag = .zero then Ball.exact (decodedRational b)
      else if tag = .succ then expBall (expressionBall b n) n
      else if tag = .left then logBall (expressionBall b n) n
      else (clampBall (expressionBall b n)).denInv
  | .rfind' a, n => (Ball.exact (-1)).mul (expressionBall a n)

@[fun_prop] theorem expressionBall_computable :
    Computable (fun p : Code × ℕ => expressionBall p.1 p.2) := by
  have h := Code.computable_recOn (c := fun p : Code × ℕ => p.1) Computable.fst
    (z := fun _ => Ball.exact 0) (by fun_prop)
    (s := fun _ => Ball.exact 1) (by fun_prop)
    (l := fun _ => Ball.exact 2) (by fun_prop)
    (r := fun _ => Ball.exact 3) (by fun_prop)
    (pr := fun _ p => p.2.2.1.add p.2.2.2) (by unfold Computable₂; fun_prop)
    (co := fun _ p => p.2.2.1.mul p.2.2.2) (by unfold Computable₂; fun_prop)
    (pc := fun x p => if p.1 = .zero then Ball.exact (decodedRational p.2.1)
      else if p.1 = .succ then expBall p.2.2.2 x.2
      else if p.1 = .left then logBall p.2.2.2 x.2
      else (clampBall p.2.2.2).denInv) (by unfold Computable₂; fun_prop)
    (rf := fun _ p => (Ball.exact (-1)).mul p.2) (by unfold Computable₂; fun_prop)
  apply h.of_eq
  intro p
  induction p.1 <;> simp_all only [expressionBall]

theorem expressionBall_encloses (e : Code) : Encloses (expressionBall e) (expressionValue e) := by
  induction e with
  | zero => simpa only [expressionBall, expressionValue, Rat.cast_zero] using encloses_exact 0
  | succ => simpa only [expressionBall, expressionValue, Rat.cast_one] using encloses_exact 1
  | left => exact encloses_exact 2
  | right => exact encloses_exact 3
  | pair a b ha hb => exact ha.add hb
  | comp a b ha hb => exact ha.mul hb
  | prec tag b _ hb =>
    by_cases hz : tag = .zero
    · simpa only [expressionBall, expressionValue, hz, ite_true] using encloses_exact (decodedRational b)
    · by_cases he : tag = .succ
      · simpa [expressionBall, expressionValue, he] using Encloses.exp hb
      · by_cases hl : tag = .left
        · simpa [expressionBall, expressionValue, hl] using Encloses.log hb
        · simpa only [expressionBall, expressionValue, hz, he, hl, ite_false] using
            (encloses_clamp hb).denInv (show (1/16 : ℝ) ≤ max 1 (expressionValue b) from
              (by norm_num : (1/16 : ℝ) ≤ 1).trans (le_max_left _ _))
  | rfind' a ha =>
    simpa only [expressionBall, expressionValue, Rat.cast_neg, Rat.cast_one, neg_one_mul] using
      (encloses_exact (-1)).mul ha

theorem expressionValue_effective : Effective expressionValue := by
  apply of_enclosures
    (q := fun p => (expressionBall p.1 p.2).center)
    (e := fun p => (expressionBall p.1 p.2).radius)
  · exact primrec_ball_center.to_comp.comp expressionBall_computable
  · exact primrec_ball_radius.to_comp.comp expressionBall_computable
  · intro a n
    simpa only [Ball.Covers, abs_sub_comm] using (expressionBall_encloses a).1 n
  · intro a
    exact (expressionBall_encloses a).2

end FixedClauseThreshold.Computability.FiniteArithmetic

end OAI
