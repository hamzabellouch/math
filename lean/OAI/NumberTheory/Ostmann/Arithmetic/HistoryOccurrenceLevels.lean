import OAI.NumberTheory.Ostmann.Arithmetic.HistoryOccurrenceVariables

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryOccurrenceVariables
open Construction

def internalLevel : {l : ℕ} → (h : History l) → InternalKey h → ℕ
  | _, .leaf _ => fun i => Empty.elim i
  | l+1, .node _ _ _ _ _ left right =>
      Sum.elim (fun _ => l+1) (Sum.elim (internalLevel left) (internalLevel right))

def keyLevel {l : ℕ} (h : History l) : Key h → ℕ :=
  Sum.elim (fun _ => l+1) (Sum.elim (fun _ => l+1) (internalLevel h))

theorem internalLevel_pos_le {l : ℕ} (h : History l) (i : InternalKey h) :
    0 < internalLevel h i ∧ internalLevel h i ≤ l := by
  induction h with
  | leaf a => exact Empty.elim i
  | @node l a p u hp hm left right ihl ihr =>
    rcases i with i | i | i
    · simp [internalLevel]
    · have hi := ihl i
      simp only [internalLevel,Sum.elim_inr,Sum.elim_inl]
      omega
    · have hi := ihr i
      simp only [internalLevel,Sum.elim_inr]
      omega

theorem internalSlot_role {l : ℕ} {V : ℕ → ℕ} {outside : List ℕ}
    (h : History l) (hs : h.Supported V outside) (i : InternalKey h) :
    (internalSlot h i).role = .compensation (internalLevel h i) := by
  induction h with
  | leaf a => exact Empty.elim i
  | @node l a p u hp hm left right ihl ihr =>
    rcases i with i | i | i
    · exact History.supported_compensation_roles hs _ (List.get_mem _ _)
    · exact ihl (History.supported_left hs) i
    · exact ihr (History.supported_right hs) i

end Ostmann.Arithmetic.HistoryOccurrenceVariables

end

end OAI
