import OAI.NumberTheory.Ostmann.Characters.HarmonicResidueDomination
import OAI.NumberTheory.Ostmann.Characters.PriorResidueDomination
import OAI.NumberTheory.Ostmann.Characters.ShellPrior

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters
open Construction Preliminaries
attribute [local instance] Classical.propDecidable

def primeUnitResidue {N:ℕ} (Q:ℕ) (p:PrimeUpTo N) : (ZMod Q)ˣ :=
  if h:p.val.Coprime Q then ZMod.unitOfCoprime p.val h else 1

theorem coe_primeUnitResidue {N:ℕ} (Q:ℕ) (p:PrimeUpTo N)
    (h:p.val.Coprime Q) : (primeUnitResidue Q p:ZMod Q)=(p.val:ZMod Q) := by
  simp only [primeUnitResidue,dite_eq_left h,ZMod.coe_unitOfCoprime]

theorem primeShellPrior_fiber {N:ℕ} {β:Type*} [Fintype β]
    (E:Finset (PrimeUpTo N)) (hE:0<primeShellMass E) (f:PrimeUpTo N→β) (b:β) :
    (pushForwardPrior (primeShellPrior E hE) f).mass b =
      (∑p∈E.filter (fun p=>f p=b),(p.val:ℝ)⁻¹)/primeShellMass E := by
  classical
  unfold pushForwardPrior
  simp only [primeShellPrior_mass,Finset.sum_filter,← Finset.sum_div]
  congr 1
  calc
    _ = ∑p:PrimeUpTo N,if p∈E then (if f p=b then (p.val:ℝ)⁻¹ else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs <;> simp_all
    _ = _ := by rw [Finset.sum_ite_mem,Finset.univ_inter]

theorem primeShellPrior_unit_mass_le {N Q:ℕ} [NeZero Q] {J:Type*} [Fintype J]
    (E:Finset (PrimeUpTo N)) (hE:0<primeShellMass E)
    (L:J→ℕ) (hL:∀j,Q≤L j)
    (hcover:∀p∈E,∃j,L j≤p.val ∧ p.val≤2*L j)
    (hcop:∀p∈E,p.val.Coprime Q) (a:(ZMod Q)ˣ) :
    (pushForwardPrior (primeShellPrior E hE) (primeUnitResidue Q)).mass a ≤
      (3*Fintype.card J/(Q:ℝ))/primeShellMass E := by
  classical
  rw [primeShellPrior_fiber]
  apply div_le_div_of_nonneg_right _ hE.le
  let S : Finset ℕ := E.image Subtype.val
  have hnat : (∑p∈E.filter (fun p=>primeUnitResidue Q p=a),(p.val:ℝ)⁻¹) =
      ∑n∈S.filter (fun n:ℕ=>(n:ZMod Q)=(a:ZMod Q)),(n:ℝ)⁻¹ := by
    simp only [Finset.sum_filter,S]
    rw [Finset.sum_image (fun x _ y _ h=>Subtype.ext h)]
    apply Finset.sum_congr rfl
    intro p hp
    have he : primeUnitResidue Q p=a ↔ (p.val:ZMod Q)=(a:ZMod Q) := by
      rw [← coe_primeUnitResidue Q p (hcop p hp)]
      exact Units.val_inj.symm
    simp only [he]
  convert hnat.le.trans (HarmonicResidueDomination.harmonic_cover_le Q
    (Nat.pos_of_ne_zero (NeZero.ne Q)) L hL S a
    (by intro n hn; obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hn; exact hcover p hp)) using 1; congr 2

theorem primeShellPrior_unit_domination {N Q:ℕ} [NeZero Q] {J:Type*} [Fintype J]
    (E:Finset (PrimeUpTo N)) (hE:0<primeShellMass E)
    (L:J→ℕ) (hL:∀j,Q≤L j)
    (hcover:∀p∈E,∃j,L j≤p.val ∧ p.val≤2*L j)
    (hcop:∀p∈E,p.val.Coprime Q) (a:(ZMod Q)ˣ) :
    (pushForwardPrior (primeShellPrior E hE) (primeUnitResidue Q)).mass a ≤
      (3*Fintype.card J*(Fintype.card (ZMod Q)ˣ:ℝ)/((Q:ℝ)*primeShellMass E)) /
        (Fintype.card (ZMod Q)ˣ:ℝ) := by
  have hu : (Fintype.card (ZMod Q)ˣ:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  convert primeShellPrior_unit_mass_le E hE L hL hcover hcop a using 1; field_simp

end Ostmann.Characters

end

end OAI
