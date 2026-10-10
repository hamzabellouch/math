import OAI.NumberTheory.Ostmann.Characters.TemplateGraphAnchors

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem anchor_pair_normalization (α ε : ℤˣ) (t : Bool) :
    (if t then (ε:ℤ) else (α:ℤ)) =
      ((copyUnit t*ε:ℤˣ):ℤ)*((AnchorCodes.pair α ε (copyUnit t*ε)).1:ℤ) ∧
    (if t then -(α:ℤ) else -(ε:ℤ)) =
      ((copyUnit t*ε:ℤˣ):ℤ)*((AnchorCodes.pair α ε (copyUnit t*ε)).2:ℤ) := by
  rcases Int.units_eq_one_or α with rfl | rfl <;>
  rcases Int.units_eq_one_or ε with rfl | rfl <;>
  cases t <;> norm_num [copyUnit,AnchorCodes.pair]

theorem graph_fresh_anchor_pair (k n : ℕ) (hn : n<k) (big : Bool) (w : Word k (n+1)) :
    let old := ((wordEquiv (schedule k n) n) w).1
    let pair := AnchorCodes.pair 1 (rowSign k n old.val) (rowSign k (n+1) w.val)
    graph k (n+1) (freshAnchor k n hn big true).val w.val =
      (rowSign k (n+1) w.val:ℤ)*(pair.1:ℤ) ∧
    graph k (n+1) (freshAnchor k n hn big false).val w.val =
      (rowSign k (n+1) w.val:ℤ)*(pair.2:ℤ) := by
  rcases w with ⟨w,hw⟩
  cases w with
  | inr q => exact False.elim (q.property.2 (word_copied _ _ _ hw.1 hw.2))
  | inl q =>
    let old : Word k n := ⟨q.1.val,q.1.property.1,hw.2⟩
    have hreg : (schedule k n).IsRegular n old.val := ⟨old.property.1,Or.inl old.property.2⟩
    have han := (anchorSlot k n hn big).property
    have hword := futureAnchor_regular_entry k n hn.le n le_rfl big _ han.1 han.2 old.val hreg
    have hpiv := futureAnchor_regular_entry k n hn.le n le_rfl big _ han.1 han.2
      (pivotSlot k n hn).val ⟨(pivotSlot k n hn).property.1,
        Or.inr ⟨n,le_rfl,(pivotSlot k n hn).property.2⟩⟩
    rw [pivotSlot_rowSign] at hpiv
    have hne : anchorCopied k n hn big ≠ q.1 := by
      intro he
      have hv := congrArg Subtype.val he
      have hr : (schedule k n).role (anchorSlot k n hn big).val=.word := hv ▸ hw.2
      have hh := han.2.symm.trans hr
      contradiction
    dsimp only [anchorCopied] at hne
    have hp := anchor_pair_normalization 1 (rowSign k n old.val) q.2
    rw [graph_succ k n hn]
    cases ht:q.2 <;>
      simpa only [freshAnchor,graphStep,transferGraph,oldIndex,Bool.true_eq_false,
        Bool.false_eq_true,ite_true,ite_false,hne,copySign,one_mul,neg_one_mul,
        rowSign,Units.val_mul,copyUnit_coe,wordEquiv,Equiv.coe_fn_mk,old,ht,anchorCopied,hword,hpiv,
        Units.val_one] using hp

end Ostmann.Characters.Template

end

end OAI
