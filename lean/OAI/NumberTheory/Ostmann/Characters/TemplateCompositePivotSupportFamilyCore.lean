import OAI.NumberTheory.Ostmann.Characters.TemplateCompositePivotSupportFamily

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable
variable {κ : Type*}

@[reducible] def TransferCoreSupport (k : ℕ)
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop) :
    (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop
  | 0,s,x,t => CurrentRootSupport k 0 s x ∧ extra 0 s x t
  | j+1,s,x,t => CurrentRootSupport k (j+1) s x ∧
      NodeSupported k j x s t.1.1 t.1.2 (B j x) (V j x) ∧
      IntegerNodeSupport k j s t.1.1 t.1.2 x ∧ extra (j+1) s x t ∧
      TransferCoreSupport k B V extra j t.1.1
        (childState k j true x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.1 ∧
      TransferCoreSupport k B V extra j t.1.2
        (childState k j false x (reconstructedPivot k j x s t.1.1 t.1.2)) t.2.2

theorem TransferCoreSupport.supported {k : ℕ} {B V extra} (j : ℕ) {s x t}
    (h : TransferCoreSupport k B V extra j s x t) : Supported k B V j s x t := by
  induction j generalizing s with
  | zero => trivial
  | succ j ih => exact ⟨h.2.1,ih h.2.2.2.2.1,ih h.2.2.2.2.2⟩

theorem outside_product_coprime_iff {k j : ℕ} (width : κ → ℕ)
    (a : (Σ i : κ, Fin (width i)) → ℤ) (o : SampleOrigins k (j+1) κ) (P : ℤ) :
    (∀ i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i},
      IsCoprime P (∏ b : Fin (width (o.outside i)), a ⟨o.outside i,b⟩)) ↔
    (∀ q : Σ i : κ, Fin (width i),
      ∀ i : {i : (schedule k j).Slot // (schedule k j).IsOutside j i},
        o.outside i = q.1 → IsCoprime (a q) P) := by
  constructor
  · intro h q i hi
    rcases q with ⟨r,b⟩
    have hh := h i
    change o.outside i = r at hi
    rw [hi] at hh
    exact (IsCoprime.prod_right_iff.mp hh b (Finset.mem_univ _)).symm
  · intro h i
    apply IsCoprime.prod_right
    intro b hb
    exact (h ⟨o.outside i,b⟩ i rfl).symm

theorem sampledTransferSupport_iff_core_selected (k : ℕ) (width : κ → ℕ)
    (a : (Σ i : κ, Fin (width i)) → ℤ)
    (B V : (j : ℕ) → State k (j+1) → ℤ)
    (extra : (j : ℕ) → ℤ → State k j → HistoryReconstruction.Tree j → Prop)
    (j : ℕ) (o : SampleOrigins k j κ) (s : ℤ) (x : State k j)
    (t : HistoryReconstruction.Tree j) :
    SampledTransferSupport k (fun i => ∏ b, a ⟨i,b⟩) B V extra j o s x t ↔
      TransferCoreSupport k B V extra j s x t ∧
        ∀ q : Σ i : κ, Fin (width i), SelectedOutsideCoprime k q.1 (a q) j o s x t := by
  induction j generalizing s with
  | zero => simp [SampledTransferSupport,TransferCoreSupport,SelectedOutsideCoprime]
  | succ j ih =>
    simp only [SampledTransferSupport,TransferCoreSupport,SelectedOutsideCoprime,
      ih,outside_product_coprime_iff,forall_and]
    tauto

end Ostmann.Characters.Template

end

end OAI
