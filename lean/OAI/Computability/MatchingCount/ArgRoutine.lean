import OAI.Computability.MatchingCount.RawData

namespace OAI

section

namespace BinaryMatching.StackCode
open Polynomial

lemma argAux_code {α : Type} [Coding α] (r : α → α → Prop) [DecidableRel r]
    (z : Option α×α) :
    (encode (List.argAux r z.1 z.2)).length≤(encode z.1).length+2*(encode z.2).length+1 := by
  rcases z with ⟨o,a⟩
  cases o with
  | none => simp [List.argAux,code_option_none,code_option_some]
  | some b =>
    simp only [List.argAux]
    split_ifs <;> simp only [code_option_some] <;> omega

namespace Poly
variable {α β : Type} [Coding α] [Coding β]

@[fun_prop] theorem argAux [Inhabited α] (r : α → α → Prop) [DecidableRel r]
    (hr : Poly (fun z : α×α => decide (r z.1 z.2))) :
    Poly (fun z : Option α×α => List.argAux r z.1 z.2) := by
  have h : Poly (fun z : Option α×α => if z.1.isSome then
      if decide (r z.2 (z.1.getD default)) then Option.some z.2 else z.1 else Option.some z.2) := by
    apply cond
    · fun_prop
    · fun_prop
    · apply cond
      · exact comp _ (fun z : Option α×α => (z.2,z.1.getD default)) hr (by fun_prop)
      · fun_prop
      · fun_prop
  exact h.congr (fun z => by cases z.1 <;> simp [List.argAux])

theorem listArgAux [Inhabited α] (r : α → α → Prop) [DecidableRel r]
    (hr : Poly (fun z : α×α => decide (r z.1 z.2))) :
    Poly (fun l : List α => l.foldl (List.argAux r) none) := by
  have hf := listFoldAdd (fun z : Option α×α => List.argAux r z.1 z.2)
    (argAux r hr) 1 (by intro z; simpa only [one_mul,Nat.add_assoc] using argAux_code r z)
  exact comp _ (fun l : List α => (l,(none:Option α))) hf (by fun_prop)

@[fun_prop] theorem listArgmin [Inhabited α] [Preorder β] [DecidableLT β]
    (hb : Poly (fun z : β×β => decide (z.1<z.2))) (f : α → β) (hf : Poly f) :
    Poly (List.argmin f) := by
  apply listArgAux (fun a b => f a<f b)
  exact comp _ (fun z : α×α => (f z.1,f z.2)) hb (by fun_prop)

@[fun_prop] theorem listArgmax [Inhabited α] [Preorder β] [DecidableLT β]
    (hb : Poly (fun z : β×β => decide (z.1<z.2))) (f : α → β) (hf : Poly f) :
    Poly (List.argmax f) := by
  apply listArgAux (fun a b => f b<f a)
  exact comp _ (fun z : α×α => (f z.2,f z.1)) hb (by fun_prop)

end Poly

lemma argmin_map_exact {α β γ : Type} [Preorder γ] [DecidableLT γ]
    (l : List α) (f : α → β) (g : β → γ) :
    (l.map f).argmin g=(l.argmin (g ∘ f)).map f := by
  induction l using List.reverseRecOn with
  | nil => rfl
  | append_singleton l a ih =>
    simp only [List.map_append,List.map_singleton,List.argmin_concat,ih]
    cases h : l.argmin (g ∘ f) with
    | none => rfl
    | some b => simp only [Option.map_some,Function.comp_apply]; split_ifs <;> rfl

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem listArgminParam [Inhabited α] [Inhabited γ]
    [Preorder β] [DecidableLT β]
    (hb : Poly (fun z : β×β => decide (z.1<z.2))) (f : γ×α → β) (hf : Poly f) :
    Poly (fun z : γ×List α => z.2.argmin (fun a => f (z.1,a))) := by
  have hm : Poly (fun z : γ×List α => z.2.map (fun a => (z.1,a))) :=
    listMapParam (fun z : γ×α => z) identity
  have h : Poly (fun z : γ×List α => ((z.2.map fun a => (z.1,a)).argmin f).map Prod.snd) := by
    apply comp _ _ (optionMap Prod.snd (by fun_prop))
    exact comp _ _ (listArgmin hb f hf) hm
  exact h.congr (fun z => by
    rw [argmin_map_exact]
    simp [Option.map_map,Function.comp_def])

@[fun_prop] theorem listArgmaxParam [Inhabited α] [Inhabited γ]
    [Preorder β] [DecidableLT β]
    (hb : Poly (fun z : β×β => decide (z.1<z.2))) (f : γ×α → β) (hf : Poly f) :
    Poly (fun z : γ×List α => z.2.argmax (fun a => f (z.1,a))) := by
  let : Coding βᵒᵈ := inferInstanceAs (Coding β)
  apply @listArgminParam α βᵒᵈ γ _ _ _ _ _ _ _ _ f hf
  exact comp (fun z : β×β => decide (z.1<z.2)) (fun z : β×β => (z.2,z.1)) hb (by fun_prop)

end Poly
end BinaryMatching.StackCode
end

end OAI
