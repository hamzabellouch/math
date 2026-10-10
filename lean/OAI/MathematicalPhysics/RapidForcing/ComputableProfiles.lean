import OAI.MathematicalPhysics.RapidForcing.RatComputable
import OAI.MathematicalPhysics.RapidForcing.FormulaCoding
import OAI.MathematicalPhysics.RapidForcing.RatOperations

namespace OAI

section
open Encodable
open scoped BigOperators
namespace RapidForcing.EffectiveProfile
open EffectiveArithmetic

private def ballEquiv : Ball ≃ ℚ × ℚ :=
  ⟨fun b => (b.center, b.radius), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩
instance : Primcodable Ball := Primcodable.ofEquiv (ℚ × ℚ) ballEquiv
@[fun_prop] lemma primrec_ball_center : Primrec Ball.center := by
  exact Primrec.fst.comp (Primrec.of_equiv (e := ballEquiv))
@[fun_prop] lemma primrec_ball_radius : Primrec Ball.radius := by
  exact Primrec.snd.comp (Primrec.of_equiv (e := ballEquiv))
@[fun_prop] lemma primrec_ball_mk : Primrec (fun p : ℚ × ℚ => Ball.mk p.1 p.2) := by
  apply Primrec.encode_iff.mp
  exact (Primrec.encode : Primrec (@encode (ℚ × ℚ) _))
@[fun_prop] lemma computable_ball_exact : Computable Ball.exact := by
  unfold Ball.exact; fun_prop
@[fun_prop] lemma computable_ball_add : Computable (fun p : Ball × Ball => p.1.add p.2) := by
  unfold Ball.add; fun_prop
@[fun_prop] lemma computable_ball_mul : Computable (fun p : Ball × Ball => p.1.mul p.2) := by
  unfold Ball.mul; fun_prop
@[fun_prop] lemma computable_ball_denInv : Computable Ball.denInv := by
  unfold Ball.denInv; fun_prop
@[fun_prop] lemma computable_ball_pow : Computable (fun p : Ball × ℕ => p.1.pow p.2) := by
  have h := Computable.nat_rec (f := fun p : Ball × ℕ => p.2)
    (g := fun _ => Ball.exact 1) (h := fun p r => r.2.mul p.1)
    (by fun_prop) (by fun_prop) (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun p => by induction p.2 <;> simp [Ball.pow, *])

@[fun_prop] lemma computable_glueDiff : Computable glueDiff := by
  have h := computable_list_foldr (f := id)
    (h := fun (_ : GluePoly) (a : (ℚ × ℕ) × GluePoly) =>
      (a.1.1, a.1.2 + 2) :: (-(a.1.2 : ℚ) * a.1.1, a.1.2 + 1) :: a.2)
    (g := fun _ => ([] : GluePoly))
    (by fun_prop) (by fun_prop) (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun p => by induction p <;> simp_all [glueDiff])

@[fun_prop] lemma computable_glueBound : Computable glueBound := by
  have h := computable_list_foldr (f := id)
    (h := fun (_ : GluePoly) (a : (ℚ × ℕ) × ℚ) => |a.1.1| * (a.1.2.factorial : ℚ) + a.2)
    (g := fun _ => (0 : ℚ))
    (by fun_prop) (by fun_prop) (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun p => by induction p <;> simp_all [glueBound])

lemma computable_sum_range {A S : Type} [Primcodable A] [Primcodable S] [AddCommMonoid S]
    (hadd : Computable (fun p : S × S => p.1 + p.2))
    {n : A → ℕ} (hn : Computable n) {f : A → ℕ → S} (hf : Computable₂ f) :
    Computable (fun a => ∑ j ∈ Finset.range (n a), f a j) := by
  have h := Computable.nat_rec hn (Computable.const (0 : S))
    (h := fun a r => r.2 + f a r.1)
    (hadd.comp ((Computable.snd.comp Computable.snd).pair (hf.comp Computable.fst (Computable.fst.comp Computable.snd)))).to₂
  apply h.of_eq
  intro a
  induction n a <;> simp [Finset.sum_range_succ, *]

@[fun_prop] lemma computable_expTerms : Computable (fun p : ℚ × ℕ => expTerms p.1 p.2) := by
  unfold expTerms; fun_prop
private lemma computable_taylor_term : Computable (fun p : (ℚ × ℕ) × ℕ =>
    p.1.1 ^ p.2 / (p.2.factorial : ℚ)) := by fun_prop
private lemma computable_taylor_sum : Computable (fun p : ℚ × ℕ =>
    ∑ j ∈ Finset.range (expTerms p.1 p.2), p.1 ^ j / (j.factorial : ℚ)) :=
  computable_sum_range computable_rat_add computable_expTerms computable_taylor_term.to₂
private lemma computable_taylor_error_fn : Computable (fun p : ℚ × ℕ =>
    |p.1| ^ p.2 / (p.2.factorial : ℚ) * 2) := by fun_prop
lemma computable_expBall : Computable (fun p : ℚ × ℕ => expBall p.1 p.2) := by
  have herr : Computable (fun p : ℚ × ℕ =>
      (p.1, expTerms p.1 p.2)) := Computable.fst.pair computable_expTerms
  have h := primrec_ball_mk.to_comp.comp
    (computable_taylor_sum.pair (computable_taylor_error_fn.comp herr))
  exact h.of_eq (fun p => rfl)
@[fun_prop] lemma computable_monoBall : Computable (fun p : ℕ × ℚ × ℕ => monoBall p.1 p.2.1 p.2.2) := by
  have harg : Computable (fun p : ℕ × ℚ × ℕ => (-(p.2.1)⁻¹, p.2.2)) := by fun_prop
  have he := computable_expBall.comp harg
  have hx : Computable (fun p : ℕ × ℚ × ℕ => Ball.exact (p.2.1⁻¹ ^ p.1)) := by fun_prop
  have hm := computable_ball_mul.comp (hx.pair he)
  have hi := computable_ite (p := fun p : ℕ × ℚ × ℕ => p.2.1 ≤ 0)
    (by fun_prop) (Computable.const (Ball.exact 0)) hm
  exact hi.of_eq (fun p => rfl)
@[fun_prop] lemma computable_glueBall : Computable (fun p : GluePoly × ℚ × ℕ => glueBall p.1 p.2.1 p.2.2) := by
  have h := computable_list_foldr (f := fun p : GluePoly × ℚ × ℕ => p.1)
    (h := fun p (a : (ℚ × ℕ) × Ball) => ((Ball.exact a.1.1).mul (monoBall a.1.2 p.2.1 p.2.2)).add a.2)
    (g := fun _ => Ball.exact 0)
    (by fun_prop) (by fun_prop) (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun p => by induction p.1 <;> simp [glueBall, *])

@[fun_prop] lemma Expr.computable_bound : Computable Expr.bound := by
  have h := Expr.computable_recOn (e := id) Computable.id
    (c := fun _ q => |q|) (by unfold Computable₂; fun_prop)
    (l := fun _ p => glueBound p) (by unfold Computable₂; fun_prop)
    (r := fun _ p => glueBound p) (by unfold Computable₂; fun_prop)
    (d := fun _ n => (16 : ℚ) ^ n) (by unfold Computable₂; fun_prop)
    (a := fun _ p => p.2.2.1 + p.2.2.2) (by unfold Computable₂; fun_prop)
    (m := fun _ p => p.2.2.1 * p.2.2.2) (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun e => by induction e <;> simp_all only [id_eq, bound])

@[fun_prop] lemma Expr.computable_diff : Computable Expr.diff := by
  have h := Expr.computable_recOn (e := id) Computable.id
    (c := fun _ _ => Expr.const 0) (by unfold Computable₂; fun_prop)
    (l := fun _ p => Expr.left (glueDiff p)) (by unfold Computable₂; fun_prop)
    (r := fun _ p => Expr.mul (.const (-1)) (.right (glueDiff p))) (by unfold Computable₂; fun_prop)
    (d := fun _ n => Expr.mul (.mul (.const (-(n : ℚ)))
      (.add (.left (glueDiff [(1, 0)])) (.mul (.const (-1)) (.right (glueDiff [(1, 0)])))))
      (.invDen (n + 1))) (by unfold Computable₂; fun_prop)
    (a := fun _ p => Expr.add p.2.2.1 p.2.2.2) (by unfold Computable₂; fun_prop)
    (m := fun _ p => Expr.add (.mul p.2.2.1 p.2.1) (.mul p.1 p.2.2.2)) (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun e => by induction e <;> simp_all only [id_eq, diff])

@[fun_prop] lemma Expr.computable_numeric : Computable (fun p : Expr × ℚ × ℕ => p.1.numeric p.2.1 p.2.2) := by
  have h := Expr.computable_recOn (e := fun p : Expr × ℚ × ℕ => p.1) (by fun_prop)
    (c := fun _ q => Ball.exact q) (by unfold Computable₂; fun_prop)
    (l := fun a p => glueBall p a.2.1 a.2.2) (by unfold Computable₂; fun_prop)
    (r := fun a p => glueBall p (1 - a.2.1) a.2.2) (by unfold Computable₂; fun_prop)
    (d := fun a n => ((glueBall [(1, 0)] a.2.1 a.2.2).add
      (glueBall [(1, 0)] (1 - a.2.1) a.2.2)).denInv.pow n) (by unfold Computable₂; fun_prop)
    (a := fun _ p => p.2.2.1.add p.2.2.2) (by unfold Computable₂; fun_prop)
    (m := fun _ p => p.2.2.1.mul p.2.2.2) (by unfold Computable₂; fun_prop)
  exact h.of_eq (fun p => by induction p.1 <;> simp [numeric, *])

lemma Expr.partrec_approx : Partrec (fun p : Expr × ℚ × ℚ => p.1.approx p.2.1 p.2.2) := by
  apply Partrec.rfindOpt
  unfold Computable₂
  fun_prop
end RapidForcing.EffectiveProfile

end

end OAI
