import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesMask
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorBounds
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedSpectatorPeriodic

namespace OAI

noncomputable section
open scoped ComplexConjugate
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction HistorySignedDecode HistorySignedSupportReduction HistorySignedSpectator

theorem int_modEq_val_pairPrecision {l : ℕ} (h k : History l) (outside : List ℕ)
    [NeZero (pairModulus h k outside)] (x : ℤ) :
    x ≡ (((x : ZMod (pairModulus h k outside)).val : ℕ) : ℤ)
      [ZMOD pairPrecision h k outside] := by
  apply Int.modEq_natAbs.mp
  change x ≡ (((x : ZMod (pairModulus h k outside)).val : ℕ) : ℤ)
    [ZMOD (pairModulus h k outside : ℤ)]
  rw [ZMod.val_intCast]
  exact (Int.mod_modEq _ _).symm

def spectatorResidue {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    (outside : List ℕ) (h k : History l)
    (z : ZMod (pairModulus h k outside) × ZMod (pairModulus h k outside)) : ℂ :=
  pairSpectator g outside (rebuild h z.1.val z.2.val) (rebuild k z.1.val z.2.val)

theorem spectatorResidue_intCast {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    {V : ℕ → ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    [NeZero (pairModulus h k outside)] (Xp Xm : ℤ) :
    spectatorResidue g outside h k ((Xp : ZMod (pairModulus h k outside)),
      (Xm : ZMod (pairModulus h k outside))) =
      pairSpectator g outside (rebuild h Xp Xm) (rebuild k Xp Xm) := by
  have hc := paired_rebuild_congruent h k hs ks (pairTestProduct h k outside) Xp Xm _ _
    (int_modEq_val_pairPrecision h k outside Xp)
    (int_modEq_val_pairPrecision h k outside Xm)
  exact (pairSpectator_eq_of_congruent g outside
    (outside_dvd_pairTestProduct h k outside) _ _ _ _ hc.1 hc.2).symm

def residueTest {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l)
    (z : ZMod (pairModulus h k outside) × ZMod (pairModulus h k outside)) : ℂ :=
  (residueMask V outside h k z : ℂ) * spectatorResidue g outside h k z

theorem residueTest_intCast {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    {V : ℕ → ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    [NeZero (pairModulus h k outside)] (Xp Xm : ℤ) :
    residueTest g V outside h k ((Xp : ZMod (pairModulus h k outside)),
      (Xm : ZMod (pairModulus h k outside))) =
      (by classical exact if ResidueGuarded V outside (rebuild h Xp Xm) ∧
        ResidueGuarded V outside (rebuild k Xp Xm) then
        pairSpectator g outside (rebuild h Xp Xm) (rebuild k Xp Xm) else 0) := by
  classical
  rw [residueTest, residueMask_intCast h k hs ks, spectatorResidue_intCast g h k hs ks]
  split_ifs <;> simp

theorem norm_residueTest_le {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    (V : ℕ → ℕ) (outside : List ℕ) (h k : History l)
    (hg : ∀ q ∈ outside, ∀ x, ‖g q x‖ ≤ 1)
    (z : ZMod (pairModulus h k outside) × ZMod (pairModulus h k outside)) :
    ‖residueTest g V outside h k z‖ ≤ 1 := by
  classical
  unfold residueTest residueMask
  split_ifs
  · simpa only [Complex.ofReal_one, one_mul, spectatorResidue] using
      norm_pairSpectator_le g outside hg (rebuild h z.1.val z.2.val) (rebuild k z.1.val z.2.val)
  · simp

theorem residueTest_intCast_eq_projection {l : ℕ} (g : (q : ℕ) → ZMod q → ℂ)
    {V : ℕ → ℕ} {outside : List ℕ} (h k : History l)
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    [NeZero (pairModulus h k outside)] (Xp Xm : ℤ)
    (hn : (rebuild h Xp Xm).Nonnegative) (kn : (rebuild k Xp Xm).Nonnegative) :
    residueTest g V outside h k ((Xp : ZMod (pairModulus h k outside)),
      (Xm : ZMod (pairModulus h k outside))) =
      (by classical exact if ResidueGuarded V outside (rebuild h Xp Xm) ∧
        ResidueGuarded V outside (rebuild k Xp Xm) then
        ((rebuild h Xp Xm).toHistory.leafProduct (Construction.spectatorFactor g outside) *
          star ((rebuild k Xp Xm).toHistory.leafProduct (Construction.spectatorFactor g outside))) else 0) := by
  rw [residueTest_intCast g h k hs ks Xp Xm,
    pairSpectator_eq_projection g outside _ _ hn kn]
  rfl

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
