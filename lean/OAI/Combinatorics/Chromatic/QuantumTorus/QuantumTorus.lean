import Mathlib

namespace OAI

section
section
namespace ElementaryPositivity.QuantumTorus

variable {R M : Type*} [CommRing R] [AddCommGroup M]

@[reducible] def Torus (_ : Rˣ) (_ : M →+ M →+ ℤ) := M →₀ R

namespace Torus
variable (v : Rˣ) (Ω : M →+ M →+ ℤ)

noncomputable instance : AddCommGroup (Torus v Ω) := inferInstanceAs (AddCommGroup (M →₀ R))
noncomputable instance : Module R (Torus v Ω) := inferInstanceAs (Module R (M →₀ R))

noncomputable def monomial (m : M) (r : R) : Torus v Ω := Finsupp.single m r
noncomputable def multiply (f g : Torus v Ω) : Torus v Ω :=
  Finsupp.sum f fun m a => Finsupp.sum g fun n b =>
    Finsupp.single (m+n) (a*b*↑(v^(Ω m n)))

noncomputable instance : Mul (Torus v Ω) := ⟨multiply v Ω⟩
noncomputable instance : One (Torus v Ω) := ⟨monomial v Ω 0 1⟩

@[simp] lemma monomial_zero (m : M) : monomial v Ω m (0 : R) = 0 := Finsupp.single_zero _
@[simp] lemma monomial_add (m : M) (a b : R) :
    monomial v Ω m (a+b) = monomial v Ω m a + monomial v Ω m b := Finsupp.single_add ..
lemma monomial_smul (m : M) (a b : R) :
    monomial v Ω m (a*b) = a • monomial v Ω m b := by
  simp only [monomial, Finsupp.smul_single, smul_eq_mul]

@[simp] lemma mul_zero (f : Torus v Ω) : f*0 = 0 := by simp [HMul.hMul, Mul.mul, multiply]
@[simp] lemma zero_mul (f : Torus v Ω) : (0 : Torus v Ω)*f = 0 := by
  simp [HMul.hMul, Mul.mul, multiply]

lemma add_mul (f g h : Torus v Ω) : (f+g)*h = f*h+g*h := by
  classical
  change multiply v Ω (f+g) h = multiply v Ω f h + multiply v Ω g h
  simp only [multiply]
  rw [Finsupp.sum_add_index']
  · intro m
    simp
  · intro m a b
    simp only [_root_.add_mul, Finsupp.single_add, Finsupp.sum_add]

lemma mul_add (f g h : Torus v Ω) : f*(g+h) = f*g+f*h := by
  classical
  change multiply v Ω f (g+h) = multiply v Ω f g + multiply v Ω f h
  simp only [multiply]
  rw [← Finsupp.sum_add]
  apply Finsupp.sum_congr
  intro m hm
  rw [Finsupp.sum_add_index']
  · intro n
    simp
  · intro n a b
    simp only [_root_.mul_add, _root_.add_mul, Finsupp.single_add]

@[simp] lemma monomial_mul_monomial (m n : M) (a b : R) :
    monomial v Ω m a * monomial v Ω n b =
      monomial v Ω (m+n) (a*b*↑(v^(Ω m n))) := by
  classical
  change multiply v Ω (Finsupp.single m a) (Finsupp.single n b) = _
  simp only [multiply, monomial, Finsupp.sum_single_index, MulZeroClass.zero_mul,
    MulZeroClass.mul_zero, Finsupp.single_zero]

lemma mul_assoc (f g h : Torus v Ω) : (f*g)*h=f*(g*h) := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f f' hf hf' => simp only [add_mul, hf, hf']
  | single m a =>
    induction g using Finsupp.induction_linear with
    | zero => simp
    | add g g' hg hg' => simp only [mul_add, add_mul, hg, hg']
    | single n b =>
      induction h using Finsupp.induction_linear with
      | zero => simp
      | add h h' hh hh' => simp only [mul_add, hh, hh']
      | single p c =>
        change (monomial v Ω m a * monomial v Ω n b) * monomial v Ω p c =
          monomial v Ω m a * (monomial v Ω n b * monomial v Ω p c)
        simp only [monomial_mul_monomial, map_add, AddMonoidHom.add_apply, add_assoc]
        congr 1
        simp only [zpow_add, Units.val_mul]
        ring

@[simp] lemma one_mul (f : Torus v Ω) : (1 : Torus v Ω)*f=f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [mul_add, hf, hg]
  | single m a =>
    change monomial v Ω 0 1 * monomial v Ω m a = monomial v Ω m a
    simp only [monomial_mul_monomial, map_zero, AddMonoidHom.zero_apply,
      zero_add, _root_.one_mul, zpow_zero, Units.val_one, _root_.mul_one]

@[simp] lemma mul_one (f : Torus v Ω) : f*(1 : Torus v Ω)=f := by
  classical
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [add_mul, hf, hg]
  | single m a =>
    change monomial v Ω m a * monomial v Ω 0 1 = monomial v Ω m a
    simp only [monomial_mul_monomial, map_zero, add_zero, _root_.mul_one, zpow_zero, Units.val_one]

noncomputable instance : Ring (Torus v Ω) :=
  Ring.ofMinimalAxioms _root_.add_assoc _root_.zero_add _root_.neg_add_cancel
    (mul_assoc v Ω) (one_mul v Ω) (mul_one v Ω) (mul_add v Ω) (add_mul v Ω)

noncomputable def X (m : M) : Torus v Ω := monomial v Ω m 1

@[simp] lemma X_zero : X v Ω 0 = 1 := rfl
lemma X_mul_X (m n : M) : X v Ω m * X v Ω n = (↑(v^(Ω m n)) : R) • X v Ω (m+n) := by
  simp only [X, monomial_mul_monomial, _root_.one_mul]
  simpa only [_root_.mul_one] using monomial_smul v Ω (m+n) (↑(v^(Ω m n)) : R) 1

lemma X_mul_X_of_pairing_zero (m n : M) (h : Ω m n = 0) :
    X v Ω m * X v Ω n = X v Ω (m+n) := by
  simp [X_mul_X, h]

lemma X_commute (m n : M) (h₁ : Ω m n = 0) (h₂ : Ω n m = 0) :
    Commute (X v Ω m) (X v Ω n) := by
  show X v Ω m * X v Ω n = X v Ω n * X v Ω m
  simp only [X_mul_X_of_pairing_zero v Ω m n h₁,
    X_mul_X_of_pairing_zero v Ω n m h₂, add_comm]

end Torus
end ElementaryPositivity.QuantumTorus
end
end

end OAI
