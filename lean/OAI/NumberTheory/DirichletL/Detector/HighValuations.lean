import OAI.NumberTheory.DirichletL.Detector.IdealFactorization
import OAI.NumberTheory.DirichletL.Detector.IdealUnit

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev HighIdeal := (Id×Id)×(Id×Id)

def highIdeals (v : PrimeIdeal→₀HighValuation) : HighIdeal :=
  ((idealFromValuations (v.mapRange (fun b=>b.1.1) rfl),
    idealFromValuations (v.mapRange (fun b=>b.1.2) rfl)),
   (idealFromValuations (v.mapRange (fun b=>b.2.1) rfl),
    idealFromValuations (v.mapRange (fun b=>b.2.2) rfl)))

lemma highIdeals_eq_equiv (v : PrimeIdeal→₀HighValuation) :
    highIdeals v =
      (((highValuationEquiv.symm v).1.1.val,(highValuationEquiv.symm v).1.2.val),
       ((highValuationEquiv.symm v).2.1.val,(highValuationEquiv.symm v).2.2.val)) := by
  apply Prod.ext <;> apply Prod.ext
  all_goals
    apply congrArg idealFromValuations
    ext P
    rfl

lemma highIdeals_injective : Function.Injective highIdeals := by
  intro v w h
  apply highValuationEquiv.symm.injective
  rw [highIdeals_eq_equiv,highIdeals_eq_equiv] at h
  apply Prod.ext
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.1.1) h)
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.1.2) h)
  · apply Prod.ext
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.2.1) h)
    · exact Subtype.ext (congrArg (fun b : HighIdeal=>b.2.2) h)

lemma highIdeals_zero : highIdeals 0=1 := by
  simp only [highIdeals,Finsupp.mapRange_zero,idealFromValuations_zero]
  rfl

lemma highIdeals_single (P : PrimeIdeal) (b : HighValuation) :
    highIdeals (Finsupp.single P b)=((P.val^b.1.1,P.val^b.1.2),(P.val^b.2.1,P.val^b.2.2)) := by
  simp only [highIdeals,Finsupp.mapRange_single,idealFromValuations_single]

lemma highIdeals_add (v w : PrimeIdeal→₀HighValuation) :
    highIdeals (v+w)=highIdeals v*highIdeals w := by
  have hproj (f : HighValuation→ℕ) (hf0 : f 0=0) (hf : ∀a b,f (a+b)=f a+f b) :
      (v+w).mapRange f hf0=v.mapRange f hf0+w.mapRange f hf0 := by
    ext P
    simp only [Finsupp.mapRange_apply,Finsupp.add_apply,hf]
  simp only [highIdeals,hproj (fun b=>b.1.1) rfl (fun _ _=>rfl),
    hproj (fun b=>b.1.2) rfl (fun _ _=>rfl),hproj (fun b=>b.2.1) rfl (fun _ _=>rfl),
    hproj (fun b=>b.2.2) rfl (fun _ _=>rfl),idealFromValuations_add]
  rfl

lemma prime_coprime_highIdeals (P : PrimeIdeal) (v : PrimeIdeal→₀HighValuation)
    (hv : v P=0) : IsCoprime P.val
      ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) := by
  have hc (f : HighValuation→ℕ) (hf0 : f 0=0) :
      IsCoprime P.val (idealFromValuations (v.mapRange f hf0)) := by
    apply prime_coprime_idealFromValuations
    simp only [Finsupp.mapRange_apply,hv,hf0]
  exact ((hc _ rfl).mul_right (hc _ rfl)).mul_right (hc _ rfl) |>.mul_right (hc _ rfl)

def highValuationTerm (η : HeckeFamily.Character) (x w z : ℂ)
    (v : PrimeIdeal→₀HighValuation) : ℂ :=
  bareIdealHighSummand η 1 x w z (highIdeals v).1.1 (highIdeals v).1.2
    (highIdeals v).2.1 (highIdeals v).2.2

def highPrimeTerm (η : HeckeFamily.Character) (x w z : ℂ)
    (P : PrimeIdeal) (b : HighValuation) : ℂ :=
  bareIdealHighSummand η 1 x w z (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)

lemma highPrimeTerm_zero (η : HeckeFamily.Character) (x w z : ℂ) (P : PrimeIdeal) :
    highPrimeTerm η x w z P 0=1 := by
  simp only [highPrimeTerm,Prod.fst_zero,Prod.snd_zero,pow_zero,bareIdealHighSummand_one]

theorem highValuationTerm_eq_prod (η : HeckeFamily.Character) (x w z : ℂ)
    (v : PrimeIdeal→₀HighValuation) :
    highValuationTerm η x w z v=v.prod (highPrimeTerm η x w z) := by
  induction v using Finsupp.induction with
  | zero =>
    simp only [highValuationTerm,highIdeals_zero,Prod.fst_one,Prod.snd_one,
      bareIdealHighSummand_one,Finsupp.prod_zero_index]
  | @single_add P b v hP hb ih =>
    have hv : v P=0 := Finsupp.notMem_support_iff.mp hP
    have hc := prime_coprime_highIdeals P v hv
    have hpow : IsCoprime (P.val^b.1.1*P.val^b.1.2*P.val^b.2.1*P.val^b.2.2)
        ((highIdeals v).1.1*(highIdeals v).1.2*(highIdeals v).2.1*(highIdeals v).2.2) :=
      ((hc.pow_left.mul_left hc.pow_left).mul_left hc.pow_left).mul_left hc.pow_left
    have hd : Disjoint (Finsupp.single P b).support v.support := by
      rw [Finsupp.support_single _ hb]
      exact Finset.disjoint_singleton_left.mpr hP
    rw [Finsupp.prod_add_index_of_disjoint hd,Finsupp.prod_single_index (highPrimeTerm_zero η x w z P),←ih]
    unfold highValuationTerm
    rw [highIdeals_add,highIdeals_single]
    exact bareIdealHighSummand_mul η x w z _ _ _ _ _ _ _ _ hpow

theorem highValuationTerm_summable_norm (η : HeckeFamily.Character) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    Summable (fun v : PrimeIdeal→₀HighValuation=>‖highValuationTerm η x w z v‖) :=
  (bareIdealHighSummand_summable η 1 x w z hx hw hz).norm.comp_injective highIdeals_injective

end SevenEighths.ProbePhysical
end

end OAI
