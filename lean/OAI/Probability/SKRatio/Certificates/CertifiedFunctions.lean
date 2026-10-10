import Mathlib
import OAI.Probability.SKRatio.Variational.ScalarCoherent
import OAI.Probability.SKRatio.Certificates.CertifiedJet
import OAI.Probability.SKRatio.Certificates.CertifiedGaussian

namespace OAI

noncomputable section
open Real MeasureTheory ProbabilityTheory
namespace SKRatio.Certificate
open Scalar

namespace Expr
instance : Add Expr := ⟨Expr.add⟩
instance : Neg Expr := ⟨Expr.neg⟩
instance : Sub Expr := ⟨fun a b => Expr.add a (Expr.neg b)⟩
instance : Mul Expr := ⟨Expr.mul⟩
instance : Div Expr := ⟨fun a b => Expr.mul a (Expr.inv b)⟩
instance (n : ℕ) : OfNat Expr n := ⟨Expr.rat n⟩
@[simp] lemma val_add (a b : Expr) (x : ℝ) : (a+b).val x = a.val x+b.val x := rfl
@[simp] lemma val_sub (a b : Expr) (x : ℝ) : (a-b).val x = a.val x-b.val x := rfl
@[simp] lemma val_mul (a b : Expr) (x : ℝ) : (a*b).val x = a.val x*b.val x := rfl
@[simp] lemma val_div (a b : Expr) (x : ℝ) : (a/b).val x = a.val x/b.val x := rfl
@[simp] lemma val_ofNat (n : ℕ) (x : ℝ) : (ofNat(n) : Expr).val x = n := by
  change ((n:ℚ):ℝ) = n
  norm_cast
end Expr

def approxF (β A C h : ℝ) : ℝ := (v h+A)*h+2*β^2*(m h*v h)+
  (1/2-β^2*A/(64/100-(19/100)*A))*v h+(12/100)*m h+3*β^2*C*g h

def scalarFunction (β A C M Q : ℝ) (k : ℕ) (h : ℝ) : ℝ := match k with
  | 0 => v h
  | 1 => g h
  | 2 => m h*v h
  | 3 => rho h
  | 4 => (v h-A)^2
  | 5 => (g h-C)^2
  | 6 => (m h*v h-M)^2
  | 7 => (approxF β A C h-Q)^2
  | 8 => (1+v h)^2/multiplier h/16
  | 9 => v h^2/multiplier h/16
  | 10 => v h^2/(2-m h)/4
  | 11 => v h^2/(2-m h)^2/4
  | _ => v h*(1+m h)/4

def scalarExpr (β A C M Q : ℚ) (k : ℕ) (h : Expr) : Expr :=
  let m := Expr.tanh h
  let v := 1-Expr.sq m
  let g := v/(Expr.rat (7/4)-m)
  let L := Expr.rat (45/100)+Expr.rat (1/4)*Expr.sq m-Expr.rat (6/100)*m
  let F := (v+Expr.rat A)*h+Expr.rat (2*β^2)*(m*v)+
    Expr.rat (1/2-β^2*A/(64/100-(19/100)*A))*v+
      Expr.rat (12/100)*m+Expr.rat (3*β^2*C)*g
  match k with
  | 0 => v
  | 1 => g
  | 2 => m*v
  | 3 => Expr.rat (1/2)*((1+m)*v)-Expr.rat (3/2)*Expr.sq g
  | 4 => Expr.sq (v-Expr.rat A)
  | 5 => Expr.sq (g-Expr.rat C)
  | 6 => Expr.sq (m*v-Expr.rat M)
  | 7 => Expr.sq (F-Expr.rat Q)
  | 8 => Expr.rat (1/16)*(Expr.sq (1+v)/L)
  | 9 => Expr.rat (1/16)*(Expr.sq v/L)
  | 10 => Expr.rat (1/4)*(Expr.sq v/(2-m))
  | 11 => Expr.rat (1/4)*(Expr.sq v/Expr.sq (2-m))
  | _ => Expr.rat (1/4)*(v*(1+m))

def integrandExpr (β A C M Q : ℚ) (k : ℕ) : Expr :=
  (scalarExpr β A C M Q k (Expr.rat (β^2)+Expr.rat β*Expr.var))*
    (Expr.exp (Expr.rat (-1/2)*Expr.sq Expr.var))

lemma scalarExpr_val (β A C M Q : ℚ) (k : ℕ) (h : Expr) (x : ℝ) :
    (scalarExpr β A C M Q k h).val x = scalarFunction β A C M Q k (h.val x) := by
  have hg : (7/4:ℝ)-Real.tanh (h.val x) = w (h.val x)+3/4 := by unfold w m; ring
  unfold scalarExpr scalarFunction
  split <;> simp only [Expr.val_sub,Expr.val_div,
    Expr.val,Rat.cast_sub,Rat.cast_mul,Rat.cast_div,Rat.cast_pow,
    Rat.cast_ofNat,Rat.cast_one,hg] <;>
    dsimp [v,m,g,rho,multiplier,approxF] <;> ring

lemma integrandExpr_val (β A C M Q : ℚ) (k : ℕ) (x : ℝ) :
    (integrandExpr β A C M Q k).val x =
      scalarFunction β A C M Q k ((β:ℝ)^2+β*x)*gaussianWeight x := by
  unfold integrandExpr
  rw [Expr.val_mul,scalarExpr_val]
  simp only [Expr.val,Rat.cast_pow,Rat.cast_neg,
    Rat.cast_div,Rat.cast_one,Rat.cast_ofNat,gaussianWeight]
  congr 2
  ring

lemma continuous_approxF (β A C : ℝ) : Continuous (approxF β A C) := by
  unfold approxF
  exact (((((continuous_v.add continuous_const).mul continuous_id).add
    (continuous_const.mul (continuous_m.mul continuous_v))).add
    (continuous_const.mul continuous_v)).add (continuous_const.mul continuous_m)).add
      (continuous_const.mul continuous_g)

lemma continuous_scalarFunction (β A C M Q : ℝ) (k : ℕ) :
    Continuous (scalarFunction β A C M Q k) := by
  unfold scalarFunction
  split
  · exact continuous_v
  · exact continuous_g
  · exact continuous_m.mul continuous_v
  · exact continuous_rho
  · exact (continuous_v.sub continuous_const).pow 2
  · exact (continuous_g.sub continuous_const).pow 2
  · exact ((continuous_m.mul continuous_v).sub continuous_const).pow 2
  · exact ((continuous_approxF β A C).sub continuous_const).pow 2
  · exact (((continuous_const.add continuous_v).pow 2).div continuous_multiplier
      (fun h => (multiplier_strict_pos h).ne')).div_const 16
  · exact ((continuous_v.pow 2).div continuous_multiplier
      (fun h => (multiplier_strict_pos h).ne')).div_const 16
  · exact ((continuous_v.pow 2).div (continuous_const.sub continuous_m)
      (fun h => by change 2-m h ≠ 0; linarith [(m_bounds h).2])).div_const 4
  · exact ((continuous_v.pow 2).div ((continuous_const.sub continuous_m).pow 2)
      (fun h => pow_ne_zero _ (by change 2-m h ≠ 0; linarith [(m_bounds h).2]))).div_const 4
  · exact (continuous_v.mul (continuous_const.add continuous_m)).div_const 4

end SKRatio.Certificate

end

end OAI
