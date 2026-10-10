import OAI.NumberTheory.Ostmann.Characters.TemplateCompositePivotSupportOrigins

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

@[reducible] def SampledTransferSupport {ι : Type*} (k : ℕ) (ξ : ι → ℤ)
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop) :
    (j : ℕ) → SampleOrigins k j ι → ℤ → State k j → HistoryReconstruction.Tree j → Prop
  | 0,_,s,x,t => CurrentRootSupport k 0 s x ∧ extra 0 s x t
  | j+1,o,s,x,t => CurrentRootSupport k (j+1) s x ∧
      NodeSupported k j x s t.1.1 t.1.2 (B j x) (V j x) ∧
      IntegerNodeSupport k j s t.1.1 t.1.2 x ∧ extra (j+1) s x t ∧
      (∀ i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i},
        IsCoprime (reconstructedPivot k j x s t.1.1 t.1.2) (ξ (o.outside i))) ∧
      SampledTransferSupport k ξ B V extra j (o.child true) t.1.1
        (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      SampledTransferSupport k ξ B V extra j (o.child false) t.1.2
        (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

theorem reducedTransferSupport_iff_sampled {ι : Type*} (k : ℕ) (ξ : ι → ℤ)
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (j : ℕ) (o : SampleOrigins k j ι) (s : ℤ) (x : State k j)
    (t : HistoryReconstruction.Tree j) (hm : o.Matches ξ x) :
    ReducedTransferSupport k B V extra j s x t ↔
      SampledTransferSupport k ξ B V extra j o s x t := by
  induction j generalizing s with
  | zero => rfl
  | succ j ih =>
    constructor
    · intro h
      refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,?_,?_,?_⟩
      · intro i
        rw [← hm.outside i]
        exact h.2.2.2.2.1 i
      · exact (ih _ _ _ _ (hm.child true _)).mp h.2.2.2.2.2.1
      · exact (ih _ _ _ _ (hm.child false _)).mp h.2.2.2.2.2.2
    · intro h
      refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,?_,?_,?_⟩
      · intro i
        rw [hm.outside i]
        exact h.2.2.2.2.1 i
      · exact (ih _ _ _ _ (hm.child true _)).mpr h.2.2.2.2.2.1
      · exact (ih _ _ _ _ (hm.child false _)).mpr h.2.2.2.2.2.2

theorem transferSupport_iff_sampled {k : ℕ}
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (j : ℕ) (hj : j ≤ k) (s : ℤ) (x : State k j) (t : HistoryReconstruction.Tree j)
    (hpair : Pairwise (fun i h => IsCoprime (x i) (x h))) :
    TransferSupport k B V extra j s x t ↔
      SampledTransferSupport k x B V extra j (SampleOrigins.root k j) s x t :=
  (transferSupport_iff_reduced B V extra j hj s x t hpair).trans
    (reducedTransferSupport_iff_sampled k x B V extra j _ s x t
      (SampleOrigins.root_matches k j x))

end Ostmann.Characters.Template

end

end OAI
