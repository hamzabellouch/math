import Mathlib
import OAI.Combinatorics.Chromatic.GradedAlgebra.PowerSeriesSplit

namespace OAI

section
section
namespace ElementaryPositivity.PowerSeriesSplit
open PowerSeries
noncomputable section
variable {R : Type*} [Ring R]
variable (P Q : R →+ R) (S : Subring R)
variable (hS : ∀x,x∈S ↔ P x=0)
variable (hP : ∀x,P (P x)=P x) (hQ : ∀x,Q (Q x)=Q x)
variable (hPQ : ∀x,P (Q x)=0)

 def positiveFactor (f : PowerSeries R) := leftFactor P f
 def zeroFactor (f : PowerSeries R) := leftFactor Q (rightFactor P f)
 def negativeFactor (f : PowerSeries R) := rightFactor Q (rightFactor P f)

lemma factor_three (f : PowerSeries R) (hf : constantCoeff f=1) :
    positiveFactor P f * zeroFactor P Q f * negativeFactor P Q f=f := by
  rw [positiveFactor,zeroFactor,negativeFactor,mul_assoc,
    factorization Q _ (right_constant P f),factorization P f hf]

include hS hP hPQ in
lemma zero_negative_nonpositive (f : PowerSeries R) :
    (∀n,coeff n (zeroFactor P Q f)∈S) ∧
    (∀n,coeff n (negativeFactor P Q f)∈S) := by
  apply factors_mem Q S
  · intro x hx
    exact (hS _).mpr (hPQ x)
  · intro n
    cases n with
    | zero => rw [coeff_zero_eq_constantCoeff_apply,right_constant]; exact S.one_mem
    | succ n => exact (hS _).mpr (right_killed P hP f n)

lemma three_constant (f : PowerSeries R) :
    constantCoeff (positiveFactor P f)=1 ∧ constantCoeff (zeroFactor P Q f)=1 ∧
      constantCoeff (negativeFactor P Q f)=1 := by
  exact ⟨left_constant P f,left_constant Q _,right_constant Q _⟩

include hS hP hQ hPQ in
lemma three_support (f : PowerSeries R) :
    (∀n,P (coeff (n+1) (positiveFactor P f))=coeff (n+1) (positiveFactor P f)) ∧
    (∀n,P (coeff n (zeroFactor P Q f))=0) ∧
    (∀n,Q (coeff (n+1) (zeroFactor P Q f))=coeff (n+1) (zeroFactor P Q f)) ∧
    (∀n,P (coeff n (negativeFactor P Q f))=0) ∧
    (∀n,Q (coeff (n+1) (negativeFactor P Q f))=0) := by
  have hs:=zero_negative_nonpositive P Q S hS hP hPQ f
  exact ⟨left_fixed P hP f,fun n=>(hS _).mp (hs.1 n),left_fixed Q hQ _,
    fun n=>(hS _).mp (hs.2 n),right_killed Q hQ _⟩

include hS in
lemma three_uniqueness (f a b c : PowerSeries R)
    (ha : constantCoeff a=1) (hb : constantCoeff b=1) (hc : constantCoeff c=1)
    (habc : a*b*c=f)
    (haP : ∀n,P (coeff (n+1) a)=coeff (n+1) a)
    (hbP : ∀n,P (coeff n b)=0) (hcP : ∀n,P (coeff n c)=0)
    (hbQ : ∀n,Q (coeff (n+1) b)=coeff (n+1) b)
    (hcQ : ∀n,Q (coeff (n+1) c)=0) :
    a=positiveFactor P f ∧ b=zeroFactor P Q f ∧ c=negativeFactor P Q f := by
  have hbc : ∀n,P (coeff n (b*c))=0 := by
    intro n
    apply (hS _).mp
    exact mul_mem S b c (fun k=>(hS _).mpr (hbP k))
      (fun k=>(hS _).mpr (hcP k)) n
  have hfirst:=uniqueness P f a (b*c) ha (by simp [hb,hc])
    (by rwa [←mul_assoc]) haP (fun n=>hbc (n+1))
  have hsecond:=uniqueness Q (rightFactor P f) b c hb hc hfirst.2 hbQ hcQ
  exact ⟨hfirst.1,hsecond.1,hsecond.2⟩
end
end ElementaryPositivity.PowerSeriesSplit
end
end

end OAI
