import OAI.NumberTheory.Ostmann.Characters.TemplatePrimeRowUnits

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
variable {H Y:Type*} [Fintype H] [Fintype Y] [DecidableEq H] [DecidableEq Y]

def signedChildFrequency (v w:ℤ) (t:Bool) : ℤ := if t then v else -w

omit [Fintype Y] in
theorem primeRowUnits_opposite [Fintype Y] (p:OutputPrimeIndex H Y→ℕ)
    (hc:Pairwise (fun i j => (p i).Coprime (p j))) (i:H) (t:Bool) :
    (((∏h:H,primeRowUnits p hc (.inl (i,t)) (.inl (h,!t))):
      (ZMod (p (.inl (i,t))))ˣ):ZMod (p (.inl (i,t)))) = primeCopyProduct p (!t) := by
  rw [Units.coe_prod]
  simp only [primeCopyProduct,Nat.cast_prod]
  apply Finset.prod_congr rfl
  intro h _
  apply primeRowUnits_coe
  cases t <;> simp

omit [Fintype Y] [DecidableEq H] [DecidableEq Y] in
theorem reversal_copied_residue [Fintype Y] [DecidableEq H] [DecidableEq Y]
    (p:OutputPrimeIndex H Y→ℕ) (P s v w:ℤ)
    (he:s*P=v*(primeCopyProduct p false:ℤ)-w*(primeCopyProduct p true:ℤ))
    (i:H) (t:Bool) :
    (s:ZMod (p (.inl (i,t))))*(P:ZMod (p (.inl (i,t)))) =
      (signedChildFrequency v w t:ZMod (p (.inl (i,t))))*
        (primeCopyProduct p (!t):ZMod (p (.inl (i,t)))) := by
  have hself : (primeCopyProduct p t:ZMod (p (.inl (i,t))))=0 := by
    apply (ZMod.natCast_eq_zero_iff _ _).mpr
    exact Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  have hh := congrArg (fun x:ℤ => (x:ZMod (p (.inl (i,t))))) he
  simp only [Int.cast_mul,Int.cast_sub,Int.cast_natCast] at hh
  cases t <;> simpa [signedChildFrequency,hself] using hh

theorem reversal_root_residue_ne_zero (p:OutputPrimeIndex H Y→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (P s v w:ℤ)
    (he:s*P=v*(primeCopyProduct p false:ℤ)-w*(primeCopyProduct p true:ℤ))
    (i:H) (t:Bool)
    (hf:(signedChildFrequency v w t:ZMod (p (.inl (i,t))))≠0) :
    (s:ZMod (p (.inl (i,t))))≠0 := by
  have hu : (primeCopyProduct p (!t):ZMod (p (.inl (i,t))))≠0 := by
    rw [← primeRowUnits_opposite p hc i t]
    exact Units.ne_zero _
  have hh := reversal_copied_residue p P s v w he i t
  intro hs
  rw [hs,zero_mul] at hh
  exact (mul_ne_zero hf hu) hh.symm

theorem reversal_pivot_units (p:OutputPrimeIndex H Y→ℕ)
    [∀i,Fact (p i).Prime] (hc:Pairwise (fun i j => (p i).Coprime (p j)))
    (P s v w:ℤ)
    (he:s*P=v*(primeCopyProduct p false:ℤ)-w*(primeCopyProduct p true:ℤ))
    (i:H) (t:Bool)
    (hP:(P:ZMod (p (.inl (i,t))))≠0)
    (hf:(signedChildFrequency v w t:ZMod (p (.inl (i,t))))≠0) :
    Units.mk0 (P:ZMod (p (.inl (i,t)))) hP =
      (Units.mk0 (signedChildFrequency v w t:ZMod (p (.inl (i,t)))) hf /
        Units.mk0 (s:ZMod (p (.inl (i,t))))
          (reversal_root_residue_ne_zero p hc P s v w he i t hf))*
        ∏h:H,primeRowUnits p hc (.inl (i,t)) (.inl (h,!t)) := by
  have hs := reversal_root_residue_ne_zero p hc P s v w he i t hf
  apply Units.ext
  change (P:ZMod (p (.inl (i,t)))) =
    ((signedChildFrequency v w t:ZMod (p (.inl (i,t)))) / (s:ZMod (p (.inl (i,t)))))*
      ((∏h:H,primeRowUnits p hc (.inl (i,t)) (.inl (h,!t))):
        (ZMod (p (.inl (i,t))))ˣ)
  rw [primeRowUnits_opposite]
  rw [div_mul_eq_mul_div,eq_div_iff hs]
  simpa [mul_comm] using reversal_copied_residue p P s v w he i t

end Ostmann.Characters.Template

end

end OAI
