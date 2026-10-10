import OAI.NumberTheory.Ostmann.Characters.TemplateGraphPairs

namespace OAI

noncomputable section
namespace Ostmann.Characters.Template
attribute [local instance] Classical.propDecidable

theorem graph_anchor_code (k : ℕ) : ∀n,(hn:n≤k) → ∀big,∀w:Word k n,∀j:Fin n,
    graph k n (retiredAnchors k n hn big j true).val w.val =
      (rowSign k n w.val:ℤ)*((AnchorCodes.code (fun _ => 1) (pathSigns k n w) j).1:ℤ) ∧
    graph k n (retiredAnchors k n hn big j false).val w.val =
      (rowSign k n w.val:ℤ)*((AnchorCodes.code (fun _ => 1) (pathSigns k n w) j).2:ℤ) := by
  intro n
  induction n with
  | zero => intro hn big w j; exact Fin.elim0 j
  | succ n ih =>
    intro hn big w j
    refine Fin.lastCases ?_ (fun j => ?_) j
    · have hpair := graph_fresh_anchor_pair k n hn big w
      simpa only [retiredAnchors,Fin.lastCases_last,AnchorCodes.code,pathSigns_castSucc,
        pathSigns_last,Fin.succ_last] using hpair
    · rcases w with ⟨w,hw⟩
      cases w with
      | inr q => exact False.elim (q.property.2 (word_copied _ _ _ hw.1 hw.2))
      | inl q =>
        let old : Word k n := ⟨q.1.val,q.1.property.1,hw.2⟩
        have hh := ih (by omega) big old j
        rw [graph_succ k n hn]
        simpa only [retiredAnchors,Fin.lastCases_castSucc,carryRetired,graphStep,transferGraph,
          oldIndex,rowSign,Units.val_mul,copyUnit_coe,AnchorCodes.code,pathSigns_castSucc,
          ←Fin.castSucc_succ,wordEquiv,Equiv.coe_fn_mk,old,mul_assoc] using
          And.intro (congrArg (fun x : ℤ => copySign q.2*x) hh.1)
            (congrArg (fun x : ℤ => copySign q.2*x) hh.2)

theorem actual_anchor_entries_injective (k n : ℕ) (hn:n≤k) (big : Bool) :
    Function.Injective (fun w : Word k n =>
      ((fun j:Fin n =>
        (graph k n (retiredAnchors k n hn big j true).val w.val,
          graph k n (retiredAnchors k n hn big j false).val w.val)),
        rowSign k n w.val)) := by
  intro w z h
  apply actual_code_final_injective k n
  have he := congrArg Prod.snd h
  dsimp only at he
  refine Prod.ext ?_ he
  funext j
  have hh := congrFun (congrArg Prod.fst h) j
  have hw := graph_anchor_code k n hn big w j
  have hz := graph_anchor_code k n hn big z j
  apply Prod.ext <;> apply Units.ext
  · have hf := congrArg Prod.fst hh
    dsimp only at hf ⊢
    rw [hw.1,hz.1,he] at hf
    exact mul_left_cancel₀ (rowSign k n z.val).ne_zero hf
  · have hf := congrArg Prod.snd hh
    dsimp only at hf ⊢
    rw [hw.2,hz.2,he] at hf
    exact mul_left_cancel₀ (rowSign k n z.val).ne_zero hf

end Ostmann.Characters.Template

end

end OAI
