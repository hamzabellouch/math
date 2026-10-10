import OAI.NumberTheory.Ostmann.Characters.TemplateCompositePivotSupportFamilyValue

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
open SymbolicHistory TemplateSupportRemoval Preliminaries
attribute [local instance] Classical.propDecidable

theorem prime_transferSupport_value_eq_family {k Q : ℕ}
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (j : ℕ) (hj : j ≤ k) (s : ℤ) (width : Role → ℕ)
    (p : (schedule k j).Constituent width → PrimeUpTo Q)
    (e : Expressions (ι:=(schedule k j).Constituent width) k j)
    (he : evalExpressions (fun i => ((p i).val:ℤ)) e =
      constituentSampleState (schedule k j) width p)
    (t : HistoryReconstruction.Tree j) (i : (schedule k j).Constituent width) (z : ℂ) :
    (if Pairwise (fun u v => (p u).val.Coprime (p v).val) then
      if TransferSupport k B V extra j s (evalExpressions (fun u => ((p u).val:ℤ)) e) t
        then z else 0 else 0) =
      familyCoprimeSupportedValue (outsidePivotFamily k i.1 j (SampleOrigins.root k j) s e t)
        (decide (Pairwise (fun u v => (p u).val.Coprime (p v).val)) &&
          decide (outsidePrimeRemainder k (fun u => width ((schedule k j).role u))
            (fun u => ((p u).val:ℤ)) B V extra j (SampleOrigins.root k j) s
            (evalExpressions (fun u => ((p u).val:ℤ)) e) t i))
        (p i).val (fun q => q.integerEval (fun u => ((p u).val:ℤ))) z := by
  classical
  by_cases hp : Pairwise (fun u v => (p u).val.Coprime (p v).val)
  · have hpair : Pairwise (fun u v => IsCoprime
        (evalExpressions (fun u => ((p u).val:ℤ)) e u)
        (evalExpressions (fun u => ((p u).val:ℤ)) e v)) := by
      rw [he]
      exact ((constituent_prime_support_iff (schedule k j) width p).mp hp).1
    have hs := transferSupport_iff_sampled B V extra j hj s
      (evalExpressions (fun u => ((p u).val:ℤ)) e) t hpair
    have hs' : TransferSupport k B V extra j s
        (evalExpressions (fun u => ((p u).val:ℤ)) e) t ↔
        SampledTransferSupport k (constituentSampleState (schedule k j) width p)
          B V extra j (SampleOrigins.root k j) s
          (evalExpressions (fun u => ((p u).val:ℤ)) e) t :=
      hs.trans (by rw [← he])
    rw [ite_eq_left hp,hs']
    rw [show constituentSampleState (schedule k j) width p =
      (fun r => ∏ b : Fin (width ((schedule k j).role r)), ((p ⟨r,b⟩).val:ℤ)) from rfl]
    simpa only [hp,decide_true,Bool.true_and,Bool.true_eq,ite_true,constituentSampleState] using
      sampledTransfer_value_eq_family k (fun u => width ((schedule k j).role u))
        (fun u => ((p u).val:ℤ)) B V extra j (SampleOrigins.root k j) s e t i
        (p i).val rfl true z
  · simp [hp,familyCoprimeSupportedValue]

end Ostmann.Characters.Template

end

end OAI
