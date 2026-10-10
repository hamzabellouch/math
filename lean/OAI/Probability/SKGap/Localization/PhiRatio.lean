import Mathlib
import OAI.Probability.SKGap.Localization.PhiAlgebra

namespace OAI

section

noncomputable section
namespace SKGap.Stein

inductive RatioExpr where
  | constant (c : ℝ)
  | kernel (f : KernelExpr)
  | add (f g : RatioExpr)
  | mul (f g : RatioExpr)
namespace RatioExpr

def eval : RatioExpr → ℝ → ℝ → ℝ → ℝ
  | constant c,_,_,_  =>  c
  | kernel f,z,r,a  =>  f.eval z r a/phi z r a
  | add f g,z,r,a  =>  eval f z r a+eval g z r a
  | mul f g,z,r,a  =>  eval f z r a*eval g z r a

def mass : RatioExpr → ℝ
  | constant c  =>  |c|
  | kernel f  =>  f.mass
  | add f g  =>  mass f+mass g
  | mul f g  =>  mass f*mass g

lemma mass_nonneg (f : RatioExpr) : 0 ≤ mass f := by
  induction f with
  | constant c  =>  exact abs_nonneg c
  | kernel f  =>  exact f.mass_nonneg
  | add f g hf hg  =>  exact add_nonneg hf hg
  | mul f g hf hg  =>  exact mul_nonneg hf hg

lemma bounded (f : RatioExpr) (z r a : ℝ) : |eval f z r a| ≤ mass f := by
  induction f with
  | constant c  =>  exact le_refl _
  | kernel f  =>
    dsimp only [eval,mass]
    rw [abs_div,abs_of_pos (phi_pos z r a),div_le_iff₀ (phi_pos z r a)]
    exact f.relative_bound z r a
  | add f g hf hg  =>  exact (abs_add_le _ _).trans (add_le_add hf hg)
  | mul f g hf hg  =>
    dsimp only [eval,mass]
    rw [abs_mul]
    exact mul_le_mul hf hg (abs_nonneg _) f.mass_nonneg

def d (i : Axis) : RatioExpr → RatioExpr
  | constant _  =>  constant 0
  | kernel f  =>  add (kernel (f.d i))
      (mul (constant (-1)) (mul (kernel f) (kernel ((KernelExpr.atom 0 0 false).d i))))
  | add f g  =>  add (d i f) (d i g)
  | mul f g  =>  add (mul (d i f) g) (mul f (d i g))

lemma kernel_deriv_z (f : KernelExpr) (z r a : ℝ) :
    HasDerivAt (fun z => eval (kernel f) z r a) (eval (d .z (kernel f)) z r a) z := by
  have hphi : HasDerivAt (fun z => phi z r a)
      ((KernelExpr.atom 0 0 false).dz.eval z r a) z := by
    simpa only [KernelExpr.eval,moment_base] using (KernelExpr.atom 0 0 false).hasDerivAt_z z r a
  convert! (f.hasDerivAt_z z r a).div hphi (phi_pos z r a).ne' using 1
  dsimp only [eval,d,KernelExpr.d]
  field_simp
  ring

lemma kernel_deriv_r (f : KernelExpr) (z r a : ℝ) :
    HasDerivAt (fun r => eval (kernel f) z r a) (eval (d .r (kernel f)) z r a) r := by
  have hphi : HasDerivAt (fun r => phi z r a)
      ((KernelExpr.atom 0 0 false).dr.eval z r a) r := by
    simpa only [KernelExpr.eval,moment_base] using (KernelExpr.atom 0 0 false).hasDerivAt_r z r a
  convert! (f.hasDerivAt_r z r a).div hphi (phi_pos z r a).ne' using 1
  dsimp only [eval,d,KernelExpr.d]
  field_simp
  ring

lemma kernel_deriv_a (f : KernelExpr) (z r a : ℝ) :
    HasDerivAt (fun a => eval (kernel f) z r a) (eval (d .a (kernel f)) z r a) a := by
  have hphi : HasDerivAt (fun a => phi z r a)
      ((KernelExpr.atom 0 0 false).da.eval z r a) a := by
    simpa only [KernelExpr.eval,moment_base] using (KernelExpr.atom 0 0 false).hasDerivAt_a z r a
  convert! (f.hasDerivAt_a z r a).div hphi (phi_pos z r a).ne' using 1
  dsimp only [eval,d,KernelExpr.d]
  field_simp
  ring

lemma hasDerivAt_z (f : RatioExpr) (z r a : ℝ) :
    HasDerivAt (fun z => eval f z r a) (eval (d .z f) z r a) z := by
  induction f with
  | constant c  =>  exact hasDerivAt_const z c
  | kernel f  =>  exact kernel_deriv_z f z r a
  | add f g hf hg  =>  exact hf.add hg
  | mul f g hf hg  =>  exact hf.mul hg

lemma hasDerivAt_r (f : RatioExpr) (z r a : ℝ) :
    HasDerivAt (fun r => eval f z r a) (eval (d .r f) z r a) r := by
  induction f with
  | constant c  =>  exact hasDerivAt_const r c
  | kernel f  =>  exact kernel_deriv_r f z r a
  | add f g hf hg  =>  exact hf.add hg
  | mul f g hf hg  =>  exact hf.mul hg

lemma hasDerivAt_a (f : RatioExpr) (z r a : ℝ) :
    HasDerivAt (fun a => eval f z r a) (eval (d .a f) z r a) a := by
  induction f with
  | constant c  =>  exact hasDerivAt_const a c
  | kernel f  =>  exact kernel_deriv_a f z r a
  | add f g hf hg  =>  exact hf.add hg
  | mul f g hf hg  =>  exact hf.mul hg

lemma partial_eval (i : Axis) (f : RatioExpr) : coordinateDeriv i (eval f)=eval (d i f) := by
  funext z r a
  cases i with
  | z  =>  exact (hasDerivAt_z f z r a).deriv
  | r  =>  exact (hasDerivAt_r f z r a).deriv
  | a  =>  exact (hasDerivAt_a f z r a).deriv

def mixedExpr (l : List Axis) (f : RatioExpr) : RatioExpr := match l with
  | []  =>  f
  | i::l  =>  d i (mixedExpr l f)

lemma mixed_eval (l : List Axis) (f : RatioExpr) : mixed l (eval f)=eval (mixedExpr l f) := by
  induction l with
  | nil  =>  rfl
  | cons i l ih  =>  rw [mixed,ih,partial_eval]; rfl

theorem all_mixed_ratio_bounded (k l : List Axis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z r a,
      |mixed l (fun z r a => mixed k phi z r a/phi z r a) z r a| ≤ C := by
  let f:=kernel (KernelExpr.mixedExpr k (.atom 0 0 false))
  refine ⟨mass (mixedExpr l f),mass_nonneg _,?_⟩
  intro z r a
  have he : (fun z r a => mixed k phi z r a/phi z r a)=eval f := by
    have hp : phi=KernelExpr.eval (.atom 0 0 false) :=
      funext fun z => funext fun r => funext fun a => (moment_base z r a).symm
    rw [hp,KernelExpr.mixed_eval]
    simp only [f,eval,KernelExpr.eval,moment_base]
  rw [he,mixed_eval]
  exact bounded _ z r a

end RatioExpr
end SKGap.Stein

end
end

end OAI
