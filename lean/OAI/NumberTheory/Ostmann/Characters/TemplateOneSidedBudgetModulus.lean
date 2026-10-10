import OAI.NumberTheory.Ostmann.Characters.TemplateOneSidedCancellationResidues
import OAI.NumberTheory.Ostmann.Characters.TemplateSupportRemovalHeightLog

namespace OAI

noncomputable section
namespace Ostmann.Characters
open SymbolicHistory

private lemma abs_mul_exp_bound {x y A B : ℝ}
    (hx : |x| ≤ Real.exp A) (hy : |y| ≤ Real.exp B) :
    |x*y| ≤ Real.exp (A+B) := by
  rw [abs_mul,Real.exp_add]
  exact mul_le_mul hx hy (abs_nonneg _) (Real.exp_pos _).le

namespace SymbolicHistory.Expr
variable {ι : Type*}

theorem denominator_abs_le_exp_size (e : Expr ι) {H : ℝ} (hH : Real.log 2 ≤ H)
    (he : e.FixedLogBound H) : |(e.denominator:ℝ)| ≤ Real.exp ((e.syntaxSize:ℝ)*H) :=
  (e.cleared_abs_le_exp_size hH he (fun _=>0)
    (fun _=>by simpa only [abs_zero] using (Real.exp_pos H).le)).2

theorem supportModulus_abs_le_exp_size_sq (e : Expr ι) {H : ℝ}
    (hH : Real.log 2 ≤ H) (he : e.FixedLogBound H) :
    |(e.supportModulus:ℝ)| ≤ Real.exp ((e.syntaxSize:ℝ)^2*H) := by
  have hH0 : 0 ≤ H := (Real.log_nonneg (by norm_num : (1:ℝ)≤2)).trans hH
  induction e with
  | atom i =>
    simp only [supportModulus,syntaxSize,Int.cast_one,abs_one,Nat.cast_one,one_pow,one_mul]
    exact Real.one_le_exp_iff.mpr hH0
  | fixed c =>
    simp only [supportModulus,syntaxSize,Int.cast_one,abs_one,Nat.cast_one,one_pow,one_mul]
    exact Real.one_le_exp_iff.mpr hH0
  | add a b ia ib | sub a b ia ib | mul a b ia ib =>
    have ha := ia he.1
    have hb := ib he.2
    simp only [supportModulus,Int.cast_mul]
    apply (abs_mul_exp_bound ha hb).trans
    apply Real.exp_le_exp.mpr
    simp only [syntaxSize,Nat.cast_add,Nat.cast_one]
    have hs : (a.syntaxSize:ℝ)^2+(b.syntaxSize:ℝ)^2 ≤
        ((a.syntaxSize:ℝ)+(b.syntaxSize:ℝ)+1)^2 := by
      nlinarith [Nat.cast_nonneg (α:=ℝ) a.syntaxSize,
        Nat.cast_nonneg (α:=ℝ) b.syntaxSize,
        mul_nonneg (Nat.cast_nonneg (α:=ℝ) a.syntaxSize) (Nat.cast_nonneg (α:=ℝ) b.syntaxSize)]
    nlinarith [mul_le_mul_of_nonneg_right hs hH0]
  | divide a d ia =>
    have ha := ia he.1
    have hd := denominator_abs_le_exp_size a hH he.1
    have hf : |(d:ℝ)| ≤ Real.exp H := he.2
    simp only [supportModulus,Int.cast_mul]
    apply (abs_mul_exp_bound ha (abs_mul_exp_bound hd hf)).trans
    apply Real.exp_le_exp.mpr
    simp only [syntaxSize,Nat.cast_add,Nat.cast_one]
    have hs : (a.syntaxSize:ℝ)^2+(a.syntaxSize:ℝ)+1 ≤ ((a.syntaxSize:ℝ)+1)^2 := by
      nlinarith [Nat.cast_nonneg (α:=ℝ) a.syntaxSize]
    nlinarith [mul_le_mul_of_nonneg_right hs hH0]

end SymbolicHistory.Expr
namespace TemplateOneSidedCancellation
variable {ι : Type*}

theorem ResidueGuard.modulus_abs_le_exp (g : ResidueGuard ι) {H : ℝ}
    (hH : Real.log 2 ≤ H) (he : g.expression.FixedLogBound H)
    (hf : (g.frequency:ℝ) ≤ Real.exp H) :
    |(g.modulus:ℝ)| ≤ Real.exp
      ((((g.expression.syntaxSize:ℝ)^2+(g.expression.syntaxSize:ℝ))+1)*H) := by
  have hh := abs_mul_exp_bound (g.expression.supportModulus_abs_le_exp_size_sq hH he)
    (abs_mul_exp_bound (g.expression.denominator_abs_le_exp_size hH he)
      (show |(g.frequency:ℝ)| ≤ Real.exp H by simpa only [abs_of_nonneg (Nat.cast_nonneg (α:=ℝ) g.frequency)] using hf))
  simpa only [ResidueGuard.modulus,Int.cast_mul,Int.cast_natCast,
    show (g.expression.syntaxSize:ℝ)^2*H+((g.expression.syntaxSize:ℝ)*H+H)=
      (((g.expression.syntaxSize:ℝ)^2+(g.expression.syntaxSize:ℝ))+1)*H by ring] using hh

theorem residueModulus_abs_le_exp (g : List (ResidueGuard ι)) (D : ℕ) {H : ℝ}
    (hH : Real.log 2 ≤ H)
    (he : ∀q∈g,q.expression.FixedLogBound H)
    (hs : ∀q∈g,q.expression.syntaxSize ≤ D)
    (hf : ∀q∈g,(q.frequency:ℝ) ≤ Real.exp H) :
    |(residueModulus g:ℝ)| ≤ Real.exp ((g.length:ℝ)*(((D:ℝ)^2+D+1)*H)) := by
  have hH0 : 0 ≤ H := (Real.log_nonneg (by norm_num : (1:ℝ)≤2)).trans hH
  induction g with
  | nil => simp [residueModulus]
  | cons q g ih =>
    have hq := q.modulus_abs_le_exp hH (he q List.mem_cons_self) (hf q List.mem_cons_self)
    have hsize : (q.expression.syntaxSize:ℝ) ≤ D := by exact_mod_cast hs q List.mem_cons_self
    have hq' : |(q.modulus:ℝ)| ≤ Real.exp (((D:ℝ)^2+D+1)*H) := by
      apply hq.trans (Real.exp_le_exp.mpr _)
      apply mul_le_mul_of_nonneg_right _ hH0
      nlinarith [Nat.cast_nonneg (α:=ℝ) q.expression.syntaxSize]
    have ht := ih (fun q hq=>he q (List.mem_cons_of_mem _ hq))
      (fun q hq=>hs q (List.mem_cons_of_mem _ hq))
      (fun q hq=>hf q (List.mem_cons_of_mem _ hq))
    have hh := abs_mul_exp_bound hq' ht
    change |((q.modulus * residueModulus g:ℤ):ℝ)| ≤ _
    rw [Int.cast_mul]
    apply hh.trans_eq
    congr 1
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    ring

end TemplateOneSidedCancellation
end Ostmann.Characters

end

end OAI
