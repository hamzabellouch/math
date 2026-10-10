import Mathlib
import OAI.Analysis.MatrixSigning.Complexity.PolynomialFamilies
import OAI.Analysis.MatrixSigning.Realization.DependentBranchRealization

namespace OAI

namespace CurrentKS.Realization
open CleanRoutine KS.W23

variable {ι α β : Type*} {L : ι → ℕ} {ea : α → Word} {eb : β → Word}
lemma isPoly_dite {P : ι → Prop} [DecidablePred P] {f : (i : ι) → P i → ℕ}
    {g : (i : ι) → ¬P i → ℕ}
    (hf : IsPoly (fun i : {i // P i} => L i.val) (fun i => f i.val i.property))
    (hg : IsPoly (fun i : {i // ¬P i} => L i.val) (fun i => g i.val i.property)) :
    IsPoly L (fun i => if h : P i then f i h else g i h) := by
  obtain ⟨p,hp⟩ := hf;obtain ⟨q,hq⟩ := hg
  refine ⟨p+q,?_⟩
  intro i
  by_cases h : P i
  · simp only [dite_eq_left h]
    exact (hp ⟨i,h⟩).trans (Nat.le_add_right _ _)
  · simp only [dite_eq_right h]
    exact (hq ⟨i,h⟩).trans (Nat.le_add_left _ _)

lemma RunsPoly.ite_on {P : α → Bool} {F G : α → β} {b : Realizes ea boolCode P}
    {r : Realizes ea eb F} {s : Realizes ea eb G} {a : ι → α}
    (hb : RunsPoly L b a)
    (hc : IsPoly L (fun i => if P (a i) then r.cost (a i) else s.cost (a i))) :
    RunsPoly L (b.ite r s) a := by
  unfold Realizes.ite
  have ht := hb.both (RunsPoly.of_poly (identity ea) a hb.input)
  apply ht.then
  refine ⟨ht.output,?_⟩
  have h := ((isPoly_const L 5).add hc).add (isPoly_const L 1)
  simp only [Nat.add_assoc] at h ⊢
  exact h

lemma RunsPoly.dite_on {P : α → Prop} [DecidablePred P]
    {F : {a // P a} → β} {G : {a // ¬P a} → β}
    {b : Realizes ea boolCode (fun a => decide (P a))}
    {r : Realizes (fun a : {a // P a} => ea a.val) eb F}
    {s : Realizes (fun a : {a // ¬P a} => ea a.val) eb G} {a : ι → α}
    (hb : RunsPoly L b a)
    (hc : IsPoly L (fun i => if h : P (a i) then r.cost ⟨a i,h⟩ else s.cost ⟨a i,h⟩)) :
    RunsPoly L (b.dite r s) a := by
  unfold Realizes.dite
  have ht := (hb.both (RunsPoly.of_poly (identity ea) a hb.input)).changeOutput
    (fun x => prodCode boolCode ea (decide (P x),x)) id (fun _ => rfl)
  apply ht.then
  refine ⟨ht.output,?_⟩
  have h := ((isPoly_const L 5).add hc).add (isPoly_const L 1)
  simp only [Nat.add_assoc] at h ⊢
  exact h
lemma RunsPoly.dite_families {P : α → Prop} [DecidablePred P]
    {F : {a // P a} → β} {G : {a // ¬P a} → β}
    {b : Realizes ea boolCode (fun a => decide (P a))}
    {r : Realizes (fun a : {a // P a} => ea a.val) eb F}
    {s : Realizes (fun a : {a // ¬P a} => ea a.val) eb G} {a : ι → α}
    (hb : RunsPoly L b a)
    (hr : RunsPoly (fun i : {i // P (a i)} => L i.val) r (fun i => ⟨a i.val,i.property⟩))
    (hs : RunsPoly (fun i : {i // ¬P (a i)} => L i.val) s (fun i => ⟨a i.val,i.property⟩)) :
    RunsPoly L (b.dite r s) a := hb.dite_on (isPoly_dite hr.cost hs.cost)
end CurrentKS.Realization

end OAI
