import OAI.NumberTheory.Ostmann.Characters.AnchorInteraction
import OAI.NumberTheory.Ostmann.Characters.TemplateGraphCodes

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem graph_word_retiredAnchor (k n : ℕ) (hn : n≤k) (big : Bool)
    (w : Word k n) (j : Fin n) (t : Bool) :
    graph k n w.val (retiredAnchors k n hn big j t).val=(rowSign k n w.val:ℤ) := by
  apply graph_regular k n hn w.val ⟨w.property.1,Or.inl w.property.2⟩
  intro he
  exact (retiredAnchors k n hn big j t).property.1 (he.symm ▸ w.property.1)

theorem actual_code_fiber_le_two (k n : ℕ) (c : Fin n → ℤˣ×ℤˣ) :
    Fintype.card {w : Word k n // AnchorCodes.code (fun _ => 1) (pathSigns k n w)=c} ≤ 2 := by
  classical
  calc
    _ ≤ Fintype.card ℤˣ := Fintype.card_le_of_injective
      (fun w : {w : Word k n // AnchorCodes.code (fun _ => 1) (pathSigns k n w)=c} =>
        rowSign k n w.val.val) (by
          intro w z h
          apply Subtype.ext
          apply actual_code_final_injective k n
          exact Prod.ext (w.property.trans z.property.symm) h)
    _ = 2 := Fintype.card_units_int

theorem actual_code_slots_le (k n m : ℕ) (c : Fin n → ℤˣ×ℤˣ) :
    Fintype.card ({w : Word k n // AnchorCodes.code (fun _ => 1) (pathSigns k n w)=c} × Fin m) ≤ 2*m := by
  rw [Fintype.card_prod,Fintype.card_fin]
  exact Nat.mul_le_mul_right m (actual_code_fiber_le_two k n c)

theorem exists_changed_anchor_entry (k n : ℕ) (hn : n≤k) (big : Bool)
    {w z : Word k n} (hwz : w≠z) (hs : rowSign k n w.val=rowSign k n z.val) :
    ∃j:Fin n,∃t:Bool,
      graph k n (retiredAnchors k n hn big j t).val w.val ≠
        graph k n (retiredAnchors k n hn big j t).val z.val := by
  classical
  by_contra h
  push Not at h
  apply hwz
  apply actual_anchor_entries_injective k n hn big
  refine Prod.ext ?_ hs
  funext j
  exact Prod.ext (h j true) (h j false)

end Ostmann.Characters.Template

end

end OAI
