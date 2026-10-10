import OAI.NumberTheory.Ostmann.Arithmetic.HistoryGiantIndependentModulusBasic
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesModulusActualComparison

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistoryGiantIndependentModulus
open Construction Conclusion Filter HistorySignedResidues HistoryCRTIntegration
open HistoryGiantReferenceMean HistorySignedXiTransport

theorem selected_integer_comparisonModulus_cap_eventually (d : Decomposition) (Bs BD Bz : ℝ)
    {k : ℕ} (hk : 0 < k) :
    ∀ᶠ L : ℝ in atTop, ∀ (E : Finset ℕ) (C : InitialSourceChoice d Bs BD Bz k L E),
      Real.exp ((1/20 : ℝ)*L) ≤ C.blockBase →
      C.blockBase-2 < (C.giantCenter : ℝ) →
      (C.giantCenter : ℝ) < C.blockBase+favorableBlockWidth L+2 →
      |(C.bulkBin : ℝ)| ≤ favorableBlockWidth L/16 →
      |(C.spectatorBin : ℝ)| ≤ favorableBlockWidth L/16 →
      ∀ spectator : PrimeSource,
      (∀ p : spectator.Sample, Real.log (p : ℕ) ≤ Real.exp ((1/1000 : ℝ)*L)) →
      ∀ ds : Fin (2*(bulkSize k L/2)) → spectator.Sample,
      let outside := spectatorList spectator ds
      ∀ l ≤ k,
      let seed := Template.initial (2*(bulkSize k L/2)) k
      let V := frequencyBound Bs BD Bz k L
      let T := Template.current seed l
      ∀ (x y : SourceAssignment C.sources T) (s t P Q : ℤ)
        (c e : HistoryChoices C.sources seed V l),
        (assignmentPrior C.sources T).mass x ≠ 0 →
        (assignmentPrior C.sources T).mass y ≠ 0 →
        choicesMass C.sources seed V l c ≠ 0 → choicesMass C.sources seed V l e ≠ 0 →
        let h := decodeHistory C.sources seed V l (giantState (sourceState C.sources T x s) P Q) c
        let g := decodeHistory C.sources seed V l (giantState (sourceState C.sources T y t) P Q) e
        h.Supported V outside → g.Supported V outside →
        0 < comparisonModulus h g outside (k+2) ∧
          Real.log (comparisonModulus h g outside (k+2) : ℝ) ≤ Real.exp ((3/250 : ℝ)*L) ∧
          (comparisonModulus h g outside (k+2) : ℝ) ≤ Real.exp (Real.exp ((3/250 : ℝ)*L)) := by
  filter_upwards [selected_fixedSmall_factorBound_eventually d Bs BD Bz hk,
    actual_comparisonModulus_log_le_eventually Bs BD Bz k,
    eventually_ge_atTop (0 : ℝ)] with L hbound hlog hL
  intro E C hG hcl hcu hb hd spectator hspec ds
  dsimp only
  intro l hl x y s t P Q c e hx hy hc he hs gs
  have hh := hbound E C hG hcl hcu hb hd l hl
    (giantState (sourceState C.sources _ x s) P Q) c (spectatorList spectator ds)
    (Template.assignedSlots_matches _ _ _) (assignedSlots_source_mass_ne_zero _ _ _ hx) hc hs
  have hg := hbound E C hG hcl hcu hb hd l hl
    (giantState (sourceState C.sources _ y t) P Q) e (spectatorList spectator ds)
    (Template.assignedSlots_matches _ _ _) (assignedSlots_source_mass_ne_zero _ _ _ hy) he gs
  have hprime : ∀ q ∈ spectatorList spectator ds, Nat.Prime q := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact spectator.prime (ds i).val (ds i).property
  have hp := pairModulus_pos _ _ hs gs (fun q hq => (hprime q hq).pos)
  have hcrt := crtModulus_pos _ _ hs gs hprime (k+2)
  have hcmp := comparisonModulus_pos _ _ hs gs hprime (k+2)
  have hout : ∀ q ∈ spectatorList spectator ds, (q : ℝ) ≤ actualFactorCap Bs BD Bz k L := by
    intro q hq
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hq
    exact spectator_le_actualFactorCap Bs BD Bz k hL
      (spectator.prime (ds i).val (ds i).property).pos (hspec (ds i))
  have hcap := hlog l hl _ _ (spectatorList spectator ds) hh hg
    (initial_spectator_count_le k L spectator ds) hout hp hcrt
  exact ⟨hcmp,hcap,comparisonModulus_le_double_exp _ _ _ _ L hcmp hcap⟩

end Ostmann.Arithmetic.HistoryGiantIndependentModulus

end

end OAI
