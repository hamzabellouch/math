import Mathlib
import OAI.Combinatorics.Chromatic.Shuffle.QuantumTorusTrace
import OAI.Combinatorics.Chromatic.GradedAlgebra.HNSeries

namespace OAI

section
namespace ElementaryPositivity.WeightedTorusSeries
open QuantumTorus RawShuffle PowerSeries
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
variable (w : I → ℕ) [Fact (∀i,0<w i)]
variable {R M : Type*} [CommRing R] [AddCommGroup M]
variable (v : Rˣ) (Ω : M →+ M →+ ℤ) (P : (I→ℕ) →+ M)
local instance : Ring (Torus v Ω) := Torus.instRing v Ω
local instance : AddCommMonoid (Torus v Ω) := (Torus.instRing v Ω).toAddCommMonoid
local instance : AddGroup (Torus v Ω) := (Torus.instRing v Ω).toAddGroup

omit [DecidableEq I] in
lemma push_twist (hΩ : ∀m,Ω m m=0) (m : M) (f : (I→ℕ) → R) :
    push w v Ω P f*C (Torus.X v Ω m)=
      C (Torus.X v Ω m)*push w v Ω P (fun d=>f d*↑(v^(2*Ω (P d) m))) := by
  classical
  apply PowerSeries.ext
  intro n
  rw [coeff_mul_C,coeff_C_mul]
  simp only [push,coeff_mk,pushCoeff]
  rw [torus_sum_mul,torus_mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [Torus.X,Torus.monomial_mul_monomial,mul_one,one_mul]
  rw [add_comm (P d.val) m,alternating_skew Ω hΩ m (P d.val)]
  congr 1
  rw [mul_assoc,←Units.val_mul,←zpow_add]
  congr 2
  ring_nf

lemma convolution_of_isotropic_support (f g : (I→ℕ) → R)
    (h : ∀d e,f d≠0 → g e≠0 → Ω (P d) (P e)=0) (d : I→ℕ) :
    convolution v Ω P f g d=∑s : DimensionSplit d,f s.left*g s.right := by
  classical
  apply Finset.sum_congr rfl
  intro s hs
  by_cases hf : f s.left=0
  · simp only [hf,zero_mul]
  by_cases hg : g s.right=0
  · simp only [hg,mul_zero,zero_mul]
  rw [h _ _ hf hg,zpow_zero,Units.val_one,mul_one]

lemma push_adjoint_of_convolution (hΩ : ∀m,Ω m m=0) (m : M)
    (f q : (I→ℕ) → R) (hf : f 0=1)
    (hq : (fun d=>f d*↑(v^(2*Ω (P d) m)))=convolution v Ω P q f) :
    push w v Ω P f*C (Torus.X v Ω m)*
        PowerSeries.invOfUnit (push w v Ω P f) 1=
      C (Torus.X v Ω m)*push w v Ω P q := by
  rw [push_twist w v Ω P hΩ, hq,push_convolution,mul_assoc]
  have H : push w v Ω P f*PowerSeries.invOfUnit (push w v Ω P f) 1=1 := by
    exact PowerSeries.mul_invOfUnit _ 1 (push_constant w v Ω P f hf)
  rw [mul_assoc,H,mul_one]

end
end ElementaryPositivity.WeightedTorusSeries

end

end OAI
