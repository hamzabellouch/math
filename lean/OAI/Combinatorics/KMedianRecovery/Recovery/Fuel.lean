import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.BidPoly
import OAI.Combinatorics.KMedianRecovery.Recovery.Min

namespace OAI

namespace MetricKMedianRecovery.BitMachine.BinaryPhaseRun
open WordOperations BinaryArithmetic WordList EffectiveOpenability RationalPhase BinaryPhaseUpdate
noncomputable def fuel : List Bool → List Bool := Count.run ∘ BinaryPhaseAdvance.sf 8
noncomputable def fuel_computes : PolyComputes fuel := (BinaryPhaseAdvance.sf_computes 8).comp Count.run_computes
lemma fuel_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : fuel (stateBits distance F v lam s)=List.replicate F.card true := by
  simp only [fuel,BinaryPhaseAdvance.sf,Function.comp_apply,stateBits,extractPrefix_pairBits,
    BinaryPhaseFirst.context,BinaryOpeningPayment.field_encode,List.getElem?_cons_zero,List.getElem?_cons_succ,
    Option.getD_some,BinaryOpeningActivity.indices,Count.run_encode,List.length_map,subtypeList,List.length_ofFn]
noncomputable def completed (x : List Bool) : List Bool := BinaryPhaseFinish.run (pairBits (fuel x,x))
noncomputable def completed_computes : PolyComputes completed := (fuel_computes.pair id_computes).comp BinaryPhaseFinish.run_computes
lemma completed_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : completed (stateBits distance F v lam s)=
      stateBits distance F v lam (finish distance F v lam F.card s).1 := by
  rw [completed,fuel_pack,BinaryPhaseFinish.run_pack]
noncomputable def step : List Bool → List Bool := BinaryPhaseAdvance.run ∘ completed
noncomputable def step_computes : PolyComputes step := completed_computes.comp BinaryPhaseAdvance.run_computes
lemma step_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (s : State m d) : step (stateBits distance F v lam s)=
      stateBits distance F v lam (advance distance v (finish distance F v lam F.card s).1) := by
  rw [step,Function.comp_apply,completed_pack,BinaryPhaseAdvance.run_pack]
lemma iterate_pack {m d : ℕ} (distance : Fin m → Fin d → ℚ) (F : Finset (Fin m))
    (v lam : ℚ) (q : ℕ) (s : State m d) :
    step^[q] (stateBits distance F v lam s)=stateBits distance F v lam (RationalPhase.run distance F v lam q s).1 := by
  induction q generalizing s with
  | zero=>rfl
  | succ q ih=>rw [Function.iterate_succ_apply,step_pack,ih]; rfl
end MetricKMedianRecovery.BitMachine.BinaryPhaseRun
namespace MetricKMedianRecovery.RationalHeight
lemma Height.min {q r : ℚ} {a : ℕ} (hq : Height q a) (hr : Height r a) :
    Height (min q r) a := by
  rcases le_total q r with h|h
  · simpa only [min_eq_left h] using hq
  · simpa only [min_eq_right h] using hr
end MetricKMedianRecovery.RationalHeight

end OAI
