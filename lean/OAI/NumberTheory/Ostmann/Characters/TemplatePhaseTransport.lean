import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseProducts
import OAI.NumberTheory.Ostmann.Characters.TemplatePhaseTransportCore

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.Template
variable {H Y:Type*} [Fintype H] [Fintype Y] [DecidableEq H] [DecidableEq Y]

def crtPhase (p:OutputPrimeIndex H Y→ℕ) [∀i,NeZero (p i)] (a:∀i,ZMod (p i)) (s:ℤ) : ℂ :=
  ∏i,ZMod.stdAddChar (-(a i*Construction.crtFrequency p s i))

def leftTranslation (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (a:∀i,ZMod (p i)) (P v:ℤ) (i:H) : ℂ :=
  translatedAdditivePhase (a (.inl (i,true))) (v:ZMod (p (.inl (i,true))))
    ((P:ZMod (p (.inl (i,true))))*primeCopyOther p i true*primeOutsideProduct p)

def rightTranslation (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (a:∀i,ZMod (p i)) (P w:ℤ) (i:H) : ℂ :=
  translatedAdditivePhase (a (.inl (i,false))) (w:ZMod (p (.inl (i,false))))
    ((P:ZMod (p (.inl (i,false))))*primeCopyOther p i false*primeOutsideProduct p)

def outsideTranslation (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (a:∀i,ZMod (p i)) (P v:ℤ) (t:Bool) (i:Y) : ℂ :=
  translatedAdditivePhase (a (.inr i)) (v:ZMod (p (.inr i)))
    ((P:ZMod (p (.inr i)))*primeCopyProduct p t*primeOutsideOther p i)

omit [Fintype Y] [DecidableEq H] [DecidableEq Y] in
private theorem copy_cast_zero (p:OutputPrimeIndex H Y→ℕ) (i:H) (t:Bool) :
    (primeCopyProduct p t:ZMod (p (.inl (i,t))))=0 := by
  apply (ZMod.natCast_eq_zero_iff _ _).mpr
  exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)

omit [Fintype Y] [DecidableEq H] [DecidableEq Y] in
private theorem copy_coprime (p:OutputPrimeIndex H Y→ℕ)
    (hc:Pairwise (fun i j => (p i).Coprime (p j))) (i:OutputPrimeIndex H Y) (t:Bool)
    (hi:∀h:H,Sum.inl (h,t)≠i) : (primeCopyProduct p t).Coprime (p i) := by
  apply Nat.Coprime.prod_left
  intro h hh
  exact hc (hi h)

omit [Fintype Y] [DecidableEq H] [DecidableEq Y] in
private theorem reversal_cast (p:OutputPrimeIndex H Y→ℕ) (P s v w:ℤ)
    (he:s*P=v*(primeCopyProduct p false:ℤ)-w*(primeCopyProduct p true:ℤ))
    (i:OutputPrimeIndex H Y) :
    (s:ZMod (p i))*(P:ZMod (p i))=
      (v:ZMod (p i))*(primeCopyProduct p false:ZMod (p i))-
      (w:ZMod (p i))*(primeCopyProduct p true:ZMod (p i)) := by
  have hh := congrArg (fun x:ℤ => (x:ZMod (p i))) he
  simpa only [Int.cast_mul,Int.cast_sub,Int.cast_natCast] using hh

theorem leftTranslation_eq_crt (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (hc:Pairwise (fun i j => (p i).Coprime (p j))) (a:∀i,ZMod (p i)) (P s v w:ℤ)
    (he:s*P=v*(primeCopyProduct p false:ℤ)-w*(primeCopyProduct p true:ℤ)) (i:H)
    (hP:(P:ZMod (p (.inl (i,true))))≠0) :
    leftTranslation p a P v i=ZMod.stdAddChar (-(a (.inl (i,true))*
      Construction.crtFrequency p s (.inl (i,true)))) := by
  have hR := ((ZMod.isUnit_iff_coprime _ _).mpr
    (copy_coprime p hc (.inl (i,true)) false (by intro h; simp))).ne_zero
  have hh := translatedAdditivePhase_left (a (.inl (i,true))) P s v w
    (primeCopyProduct p true) (primeCopyProduct p false)
    ((primeCopyOther p i true:ZMod (p (.inl (i,true))))*primeOutsideProduct p)
    (reversal_cast p P s v w he _) (copy_cast_zero p i true) hP hR
  have hden := otherProduct_copied p i true (Fact.out : (p (.inl (i,true))).Prime).ne_zero
  simpa only [leftTranslation,translatedAdditivePhase,Construction.crtFrequency,hden,
    Bool.not_true,Nat.cast_mul,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh

theorem rightTranslation_eq_crt (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (hc:Pairwise (fun i j => (p i).Coprime (p j))) (a:∀i,ZMod (p i)) (P s v w:ℤ)
    (he:s*P=v*(primeCopyProduct p false:ℤ)-w*(primeCopyProduct p true:ℤ)) (i:H)
    (hP:(P:ZMod (p (.inl (i,false))))≠0) :
    conj (rightTranslation p a P w i)=ZMod.stdAddChar (-(a (.inl (i,false))*
      Construction.crtFrequency p s (.inl (i,false)))) := by
  have hL := ((ZMod.isUnit_iff_coprime _ _).mpr
    (copy_coprime p hc (.inl (i,false)) true (by intro h; simp))).ne_zero
  have hh := translatedAdditivePhase_right (a (.inl (i,false))) P s v w
    (primeCopyProduct p true) (primeCopyProduct p false)
    ((primeCopyOther p i false:ZMod (p (.inl (i,false))))*primeOutsideProduct p)
    (reversal_cast p P s v w he _) (copy_cast_zero p i false) hP hL
  have hden := otherProduct_copied p i false (Fact.out : (p (.inl (i,false))).Prime).ne_zero
  simpa only [rightTranslation,translatedAdditivePhase,Construction.crtFrequency,hden,
    Bool.not_false,Nat.cast_mul,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh

theorem outsideTranslation_eq_crt (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (hc:Pairwise (fun i j => (p i).Coprime (p j))) (a:∀i,ZMod (p i)) (P s v w:ℤ)
    (he:s*P=v*(primeCopyProduct p false:ℤ)-w*(primeCopyProduct p true:ℤ)) (i:Y)
    (hP:(P:ZMod (p (.inr i)))≠0) :
    outsideTranslation p a P v true i*conj (outsideTranslation p a P w false i)=
      ZMod.stdAddChar (-(a (.inr i)*Construction.crtFrequency p s (.inr i))) := by
  have hL := ((ZMod.isUnit_iff_coprime _ _).mpr
    (copy_coprime p hc (.inr i) true (by intro h; simp))).ne_zero
  have hR := ((ZMod.isUnit_iff_coprime _ _).mpr
    (copy_coprime p hc (.inr i) false (by intro h; simp))).ne_zero
  have hh := translatedAdditivePhase_outside (a (.inr i)) P s v w
    (primeCopyProduct p true) (primeCopyProduct p false) (primeOutsideOther p i)
    (reversal_cast p P s v w he _) hP hL hR
  have hden := otherProduct_outside p i (Fact.out : (p (.inr i)).Prime).ne_zero
  simpa only [outsideTranslation,translatedAdditivePhase,Construction.crtFrequency,hden,
    Nat.cast_mul,div_eq_mul_inv,mul_assoc] using hh

theorem translation_product_transport (p:OutputPrimeIndex H Y→ℕ) [∀i,Fact (p i).Prime]
    (hc:Pairwise (fun i j => (p i).Coprime (p j))) (a:∀i,ZMod (p i)) (P s v w:ℤ)
    (he:s*P=v*(primeCopyProduct p false:ℤ)-w*(primeCopyProduct p true:ℤ))
    (hP:∀i,(P:ZMod (p i))≠0) :
    (∏i:H,leftTranslation p a P v i)*conj (∏i:H,rightTranslation p a P w i)*
      (∏i:Y,outsideTranslation p a P v true i*conj (outsideTranslation p a P w false i))=
        crtPhase p a s := by
  rw [map_prod]
  simp_rw [leftTranslation_eq_crt p hc a P s v w he _ (hP _),
    rightTranslation_eq_crt p hc a P s v w he _ (hP _),
    outsideTranslation_eq_crt p hc a P s v w he _ (hP _)]
  simp only [crtPhase,Fintype.prod_sum_type,Fintype.prod_prod_type,Fintype.prod_bool,
    Finset.prod_mul_distrib]

end Ostmann.Characters.Template

end

end OAI
