import OAI.Analysis.MarkovType.SubdivisionAverage
import OAI.Analysis.MarkovType.SubdivisionProfileDefs

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity.Subdivision

variable (p : Seminorm ℝ C00)
variable (hspread : ∀ {m : ℕ} (ι : Fin m → ℕ), StrictMono ι →
  ∀ a : Fin m → ℝ, p (C00.place ι a) = p (C00.ofArray a))

include hspread in
theorem list_block_mono (left right : List ℝ) {J M : ℕ}
    (hJ : 0 < J) (hJM : J ≤ M) (c : ℝ) :
    p (ofList (left ++ (List.replicate M (c / (M : ℝ)) ++ right))) ≤
      p (ofList (left ++ (List.replicate J (c / (J : ℝ)) ++ right))) := by
  induction left using List.ofFnRec with
  | h l left =>
      induction right using List.ofFnRec with
      | h r right =>
          have h := block_mono p hspread left right hJ hJM c
          simpa only [blockVector, ← ofList_ofFn, blockArray,
            List.ofFn_fin_append, List.ofFn_const] using h

def ProfileLE (a b : ℝ × ℕ) : Prop := a.1 = b.1 ∧ 0 < a.2 ∧ a.2 ≤ b.2

include hspread in
theorem pieces_mono_in_context {small large : List (ℝ × ℕ)}
    (h : List.Forall₂ ProfileLE small large) (left right : List ℝ) :
    p (ofList (left ++ (pieces large ++ right))) ≤
      p (ofList (left ++ (pieces small ++ right))) := by
  induction h generalizing left right with
  | nil => exact le_rfl
  | @cons a b small large hab htail ih =>
      rcases a with ⟨c, J⟩
      rcases b with ⟨d, M⟩
      rcases hab with ⟨hcd, hJ, hJM⟩
      change c = d at hcd
      subst d
      have htail' := ih (left ++ List.replicate M (c / (M : ℝ))) right
      simp only [List.append_assoc] at htail'
      have hhead := list_block_mono p hspread left (pieces small ++ right) hJ hJM c
      simpa only [pieces_cons, List.append_assoc] using htail'.trans hhead

private theorem profiles_related : ∀ {m : ℕ} (a : Fin m → ℝ)
    (J M : Fin m → ℕ), (∀ i, 0 < J i) → (∀ i, J i ≤ M i) →
    List.Forall₂ ProfileLE (List.ofFn fun i => (a i, J i))
      (List.ofFn fun i => (a i, M i))
  | 0, a, J, M, _, _ => by simp only [List.ofFn_zero]; exact .nil
  | m + 1, a, J, M, hJ, hJM => by
      rw [List.ofFn_succ, List.ofFn_succ]
      exact .cons ⟨rfl, hJ 0, hJM 0⟩
        (profiles_related (fun i => a i.succ) (fun i => J i.succ)
          (fun i => M i.succ) (fun i => hJ i.succ) (fun i => hJM i.succ))

include hspread in

theorem finiteSubdivision_mono {m : ℕ} (a : Fin m → ℝ) (J M : Fin m → ℕ)
    (hJ : ∀ i, 0 < J i) (hJM : ∀ i, J i ≤ M i) :
    p (finiteSubdivision a M) ≤ p (finiteSubdivision a J) := by
  have h := pieces_mono_in_context p hspread (profiles_related a J M hJ hJM) [] []
  simpa only [List.nil_append, List.append_nil, finiteSubdivision] using h

end MarkovSuperreflexivity.Subdivision

end

end OAI
