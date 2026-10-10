import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesGuards
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulus

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction HistorySignedDecode HistorySignedSupportReduction

def pairTestProduct {l : ℕ} (h k : History l) (outside : List ℕ) : ℤ :=
  testProduct h*testProduct k*(outside.prod:ℤ)

def pairPrecision {l : ℕ} (h k : History l) (outside : List ℕ) : ℤ :=
  (pairedDivisorProduct h k)^l*pairTestProduct h k outside

def pairModulus {l : ℕ} (h k : History l) (outside : List ℕ) : ℕ :=
  (pairPrecision h k outside).natAbs

theorem pairTestProduct_covers {l : ℕ} (h k : History l) (outside : List ℕ)
    (Xp Xm : ℤ) :
    Covers (pairTestProduct h k outside) (rebuild h Xp Xm) ∧
      Covers (pairTestProduct h k outside) (rebuild k Xp Xm) :=
  ⟨(testProduct_covers_rebuild h Xp Xm).mono (dvd_mul_of_dvd_left (dvd_mul_right _ _) _),
    (testProduct_covers_rebuild k Xp Xm).mono (dvd_mul_of_dvd_left (dvd_mul_left _ _) _)⟩

theorem outside_dvd_pairTestProduct {l : ℕ} (h k : History l) (outside : List ℕ)
    (q : ℕ) (hq : q∈outside) : (q:ℤ) ∣ pairTestProduct h k outside := by
  apply dvd_mul_of_dvd_right
  exact_mod_cast List.dvd_prod hq

theorem paired_residueGuarded_modEq {l : ℕ} (h k : History l)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside) (ks : k.Supported V outside)
    (Xp Xm Yp Ym : ℤ)
    (hp : Xp ≡ Yp [ZMOD pairPrecision h k outside])
    (hm : Xm ≡ Ym [ZMOD pairPrecision h k outside]) :
    (ResidueGuarded V outside (rebuild h Xp Xm) ∧ ResidueGuarded V outside (rebuild k Xp Xm)) ↔
      (ResidueGuarded V outside (rebuild h Yp Ym) ∧ ResidueGuarded V outside (rebuild k Yp Ym)) := by
  have hc := paired_rebuild_congruent h k hs ks (pairTestProduct h k outside) Xp Xm Yp Ym hp hm
  have hd := pairTestProduct_covers h k outside Xp Xm
  exact and_congr
    (residueGuarded_iff_of_congruent V outside (outside_dvd_pairTestProduct h k outside) hc.1 hd.1)
    (residueGuarded_iff_of_congruent V outside (outside_dvd_pairTestProduct h k outside) hc.2 hd.2)

def residueMask {l : ℕ} (V : ℕ → ℕ) (outside : List ℕ) (h k : History l)
    (z : ZMod (pairModulus h k outside) × ZMod (pairModulus h k outside)) : ℝ := by
  classical
  exact if ResidueGuarded V outside (rebuild h z.1.val z.2.val) ∧
      ResidueGuarded V outside (rebuild k z.1.val z.2.val) then 1 else 0

theorem residueMask_bounds {l : ℕ} (V : ℕ → ℕ) (outside : List ℕ) (h k : History l)
    (z : ZMod (pairModulus h k outside) × ZMod (pairModulus h k outside)) :
    0 ≤ residueMask V outside h k z ∧ residueMask V outside h k z ≤ 1 := by
  unfold residueMask
  split_ifs <;> norm_num

theorem residueMask_intCast {l : ℕ} (h k : History l)
    {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside) (ks : k.Supported V outside)
    [NeZero (pairModulus h k outside)] (Xp Xm : ℤ) :
    residueMask V outside h k ((Xp:ZMod (pairModulus h k outside)),(Xm:ZMod (pairModulus h k outside))) =
      (by classical exact if ResidueGuarded V outside (rebuild h Xp Xm) ∧
        ResidueGuarded V outside (rebuild k Xp Xm) then 1 else 0) := by
  classical
  have hp : Xp ≡ (((Xp:ZMod (pairModulus h k outside)).val:ℕ):ℤ)
      [ZMOD pairPrecision h k outside] := by
    apply Int.modEq_natAbs.mp
    change Xp ≡ (((Xp:ZMod (pairModulus h k outside)).val:ℕ):ℤ)
      [ZMOD (pairModulus h k outside:ℤ)]
    rw [ZMod.val_intCast]
    show Xp % (pairModulus h k outside:ℤ) =
      (Xp % (pairModulus h k outside:ℤ)) % (pairModulus h k outside:ℤ)
    rw [Int.emod_emod]
  have hm : Xm ≡ (((Xm:ZMod (pairModulus h k outside)).val:ℕ):ℤ)
      [ZMOD pairPrecision h k outside] := by
    apply Int.modEq_natAbs.mp
    change Xm ≡ (((Xm:ZMod (pairModulus h k outside)).val:ℕ):ℤ)
      [ZMOD (pairModulus h k outside:ℤ)]
    rw [ZMod.val_intCast]
    show Xm % (pairModulus h k outside:ℤ) =
      (Xm % (pairModulus h k outside:ℤ)) % (pairModulus h k outside:ℤ)
    rw [Int.emod_emod]
  unfold residueMask
  simp only [←paired_residueGuarded_modEq h k hs ks Xp Xm _ _ hp hm]

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
