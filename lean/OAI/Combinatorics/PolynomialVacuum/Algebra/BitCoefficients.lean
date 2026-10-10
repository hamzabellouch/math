import OAI.Combinatorics.PolynomialVacuum.Algebra.PolynomialSlice

namespace OAI

namespace PolynomialVacuumAlgebra
open MvPolynomial Classical

noncomputable def bitCoefficient {V : Type*} [Sub V] (b : Bool) (f : ℂ → V) : V :=
  if b then f 1-f 0 else f 0

noncomputable def biCoefficient {V : Type*} [Sub V] (f : ℂ → ℂ → V) (i j : Bool) : V :=
  bitCoefficient i (fun x => bitCoefficient j (f x))

noncomputable def triCoefficient {V : Type*} [Sub V] (f : ℂ → ℂ → ℂ → V) (i j k : Bool) : V :=
  bitCoefficient i (fun x => bitCoefficient j (fun y => bitCoefficient k (f x y)))

variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def AffineFunction (f : ℂ → V) : Prop := ∀ x, f x=f 0+x • (f 1-f 0)

omit [Module ℂ V] in
@[simp] theorem bitCoefficient_false (f : ℂ → V) : bitCoefficient false f=f 0 := rfl
omit [Module ℂ V] in
@[simp] theorem bitCoefficient_true (f : ℂ → V) : bitCoefficient true f=f 1-f 0 := rfl
omit [Module ℂ V] in
@[simp] theorem bitCoefficient_zero (b : Bool) : bitCoefficient b (fun _ : ℂ => (0:V))=0 := by cases b <;> simp [bitCoefficient]

omit [Module ℂ V] in
theorem bitCoefficient_add (b : Bool) (f g : ℂ → V) :
    bitCoefficient b (fun x => f x+g x)=bitCoefficient b f+bitCoefficient b g := by
  cases b <;> simp only [bitCoefficient_true,bitCoefficient_false]
  abel

omit [Module ℂ V] in
theorem bitCoefficient_sub (b : Bool) (f g : ℂ → V) :
    bitCoefficient b (fun x => f x-g x)=bitCoefficient b f-bitCoefficient b g := by
  cases b <;> simp only [bitCoefficient_true,bitCoefficient_false]
  abel

theorem bitCoefficient_smul (b : Bool) (c : ℂ) (f : ℂ → V) :
    bitCoefficient b (fun x => c • f x)=c • bitCoefficient b f := by
  cases b <;> simp only [bitCoefficient_true,bitCoefficient_false,smul_sub]

theorem bitCoefficient_linearMap (b : Bool) (L : V →ₗ[ℂ] W) (f : ℂ → V) :
    bitCoefficient b (fun x => L (f x))=L (bitCoefficient b f) := by
  cases b <;> simp only [bitCoefficient_true,bitCoefficient_false,map_sub]

omit [Module ℂ V] in
theorem bitCoefficient_comm (i j : Bool) (f : ℂ → ℂ → V) :
    bitCoefficient i (fun x => bitCoefficient j (f x))=
      bitCoefficient j (fun y => bitCoefficient i (fun x => f x y)) := by
  cases i <;> cases j <;> simp only [bitCoefficient_true,bitCoefficient_false]
  abel

theorem affine_sub {f g : ℂ → V} (hf : AffineFunction f) (hg : AffineFunction g) :
    AffineFunction (fun x => f x-g x) := by
  intro x
  change f x-g x=(f 0-g 0)+x • ((f 1-g 1)-(f 0-g 0))
  rw [hf x,hg x]
  module

theorem affine_bitCoefficient (b : Bool) (f : ℂ → ℂ → V)
    (hf : ∀ y, AffineFunction (fun x => f x y)) : AffineFunction (fun x => bitCoefficient b (f x)) := by
  cases b
  · exact hf 0
  · exact affine_sub (hf 1) (hf 0)

theorem bilinear_expansion (f : ℂ → ℂ → V)
    (hx : ∀ y, AffineFunction (fun x => f x y)) (hy : ∀ x, AffineFunction (f x)) (x y : ℂ) :
    f x y=biCoefficient f false false+x • biCoefficient f true false+
      y • biCoefficient f false true+(x*y) • biCoefficient f true true := by
  have hxx := hx y x
  dsimp only at hxx
  rw [hxx,hy 0 y,hy 1 y]
  simp only [biCoefficient,bitCoefficient_false,bitCoefficient_true]
  module

theorem affine_zero {f : ℂ → V} (h : AffineFunction f) (hz : ∀ b, bitCoefficient b f=0) : f=0 := by
  funext x
  rw [h x]
  change bitCoefficient false f+x • bitCoefficient true f=0
  rw [hz false,hz true,smul_zero,add_zero]

theorem triaffine_zero (f : ℂ → ℂ → ℂ → V)
    (hx : ∀ y z, AffineFunction (fun x => f x y z))
    (hy : ∀ x z, AffineFunction (fun y => f x y z))
    (hz : ∀ x y, AffineFunction (f x y))
    (h : ∀ i j k, triCoefficient f i j k=0) : ∀ x y z, f x y z=0 := by
  have hc (k : Bool) (x y : ℂ) : bitCoefficient k (f x y)=0 := by
    have he := bilinear_expansion (fun x y => bitCoefficient k (f x y))
      (fun y => affine_bitCoefficient k _ (fun z => hx y z))
      (fun x => affine_bitCoefficient k _ (fun z => hy x z)) x y
    change bitCoefficient k (f x y)=triCoefficient f false false k+
      x • triCoefficient f true false k+y • triCoefficient f false true k+
      (x*y) • triCoefficient f true true k at he
    simp only [h,smul_zero,add_zero] at he
    exact he
  intro x y z
  have he := congrFun (affine_zero (hz x y) (fun k => hc k x y)) z
  exact he

theorem eval_update_affine {ι : Type*} (p : MvPolynomial ι ℂ) (i : ι) (Y : ι → ℂ)
    (hd : p.degreeOf i ≤ 1) : AffineFunction (fun x => eval (Function.update Y i x) p) := by
  have hnd := (polynomialSlice_natDegree i Y p).trans hd
  obtain ⟨a,b,he⟩ := Polynomial.exists_eq_X_add_C_of_natDegree_le_one hnd
  intro x
  simp only [← eval_polynomialSlice,he,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,smul_eq_mul]
  ring

theorem eval_update_constant {ι : Type*} (p : MvPolynomial ι ℂ) (i : ι) (Y : ι → ℂ)
    (hd : p.degreeOf i ≤ 0) (x : ℂ) : eval (Function.update Y i x) p=eval (Function.update Y i 0) p := by
  have hnd := (polynomialSlice_natDegree i Y p).trans hd
  have he := Polynomial.eq_C_of_natDegree_eq_zero (Nat.eq_zero_of_le_zero hnd)
  simp only [← eval_polynomialSlice]
  rw [he]
  simp only [Polynomial.eval_C]

end PolynomialVacuumAlgebra

end OAI
