import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusActualDecode
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusActualScales
import OAI.NumberTheory.Ostmann.Construction.ActualAmplitude

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction Conclusion Filter

theorem selected_decoded_factorBound_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l ≤ k,
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let V := frequencyBound Bs BD Bz k L
      ∀ (x : OuterSample C.sources (Template.current seed l) C.giant) (s : ℤ)
        (c : HistoryChoices C.sources seed V l) (outside : List ℕ),
        (outerPrior C.sources (Template.current seed l) C.giant).mass x ≠ 0 →
        choicesMass C.sources seed V l c ≠ 0 →
        (decodeHistory C.sources seed V l
          (outerState C.sources (Template.current seed l) C.giant x s) c).Supported V outside →
        factorBound (actualFactorCount k L) (actualFactorCap Bs BD Bz k L)
          (decodeHistory C.sources seed V l
            (outerState C.sources (Template.current seed l) C.giant x s) c) := by
  filter_upwards [selected_sources_factorCap_eventually d Bs BD Bz hk,
    (bulkSize_tendsto_atTop hk).eventually_ge_atTop 1] with L hsource hm
  intro E C hG hcl hcu hb hd l hl
  dsimp only
  intro x s c outside hx hc hs
  have hm' : 1 ≤ bulkSize k L := by exact_mod_cast hm
  have hx' : C.giant.law.mass x.1*(C.giant.law.mass x.2.1*
      (assignmentPrior C.sources (Template.current (Template.initial (2*(bulkSize k L/2)) k) l)).mass x.2.2) ≠ 0 := hx
  have hmass := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp hx').2).2
  have hfreqNat : s.natAbs ≤ frequencyBound Bs BD Bz k L l := by
    simpa only [decodeHistory_root, outerState] using History.supported_root_frequency_bound hs
  have hfreqReal : |(s:ℝ)| ≤ (frequencyBound Bs BD Bz k L l:ℝ) := by
    have hh : (s.natAbs:ℝ) ≤ (frequencyBound Bs BD Bz k L l:ℝ) := by exact_mod_cast hfreqNat
    simpa only [Nat.cast_natAbs, Int.cast_abs] using hh
  apply factorBound_decode C.sources _ _ k (actualFactorCount k L) (actualFactorCap Bs BD Bz k L)
    (fun j hj => actual_current_length_le k L hj)
    (fun j hj => actual_frequency_le_cap Bs BD Bz k L hm' hj)
    (hsource E C hG hcl hcu hb hd) l hl _ c
    (Template.assignedSlots_matches _ _ _)
    (assignedSlots_source_mass_ne_zero _ _ _ hmass) hc
  exact hfreqReal.trans (actual_frequency_le_cap Bs BD Bz k L hm' hl)

theorem selected_decoded_pair_factorBound_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20:ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter:ℝ) →
      (C.giantCenter:ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin:ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin:ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ l ≤ k,
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let V := frequencyBound Bs BD Bz k L
      ∀ (x y : OuterSample C.sources (Template.current seed l) C.giant) (s t : ℤ)
        (c e : HistoryChoices C.sources seed V l) (outside : List ℕ),
        (outerPrior C.sources (Template.current seed l) C.giant).mass x ≠ 0 →
        (outerPrior C.sources (Template.current seed l) C.giant).mass y ≠ 0 →
        choicesMass C.sources seed V l c ≠ 0 → choicesMass C.sources seed V l e ≠ 0 →
        (decodeHistory C.sources seed V l
          (outerState C.sources (Template.current seed l) C.giant x s) c).Supported V outside →
        (decodeHistory C.sources seed V l
          (outerState C.sources (Template.current seed l) C.giant y t) e).Supported V outside →
        factorBound (actualFactorCount k L) (actualFactorCap Bs BD Bz k L)
          (decodeHistory C.sources seed V l
            (outerState C.sources (Template.current seed l) C.giant x s) c) ∧
        factorBound (actualFactorCount k L) (actualFactorCap Bs BD Bz k L)
          (decodeHistory C.sources seed V l
            (outerState C.sources (Template.current seed l) C.giant y t) e) := by
  filter_upwards [selected_decoded_factorBound_eventually d Bs BD Bz hk] with L hL
  intro E C hG hcl hcu hb hd l hl
  dsimp only
  intro x y s t c e outside hx hy hc he hs gs
  exact ⟨hL E C hG hcl hcu hb hd l hl x s c outside hx hc hs,
    hL E C hG hcl hcu hb hd l hl y t e outside hy he gs⟩

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
