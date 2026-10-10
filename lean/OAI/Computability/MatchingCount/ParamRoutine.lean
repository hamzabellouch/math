import OAI.Computability.MatchingCount.DenseOracle

namespace OAI

section

namespace BinaryMatching.StackCode
namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]

@[fun_prop] theorem mapWith [Inhabited α] [Inhabited β]
    (l : α → List β) (f : α×β → γ) (hl : Poly l) (hf : Poly f) :
    Poly (fun a => (l a).map (fun b => f (a,b))) :=
  comp _ (fun a => (a,l a)) (listMapParam f hf) (by fun_prop)

@[fun_prop] theorem flatMapWith [Inhabited α] [Inhabited β]
    (l : α → List β) (f : α×β → List γ) (hl : Poly l) (hf : Poly f) :
    Poly (fun a => (l a).flatMap (fun b => f (a,b))) := by
  have h : Poly (fun a => ((l a).map (fun b => f (a,b))).flatten) :=
    comp _ _ (listFlatten (α := γ)) (mapWith l f hl hf)
  exact h.congr (fun a => rfl)

@[fun_prop] theorem listHeadOption : Poly (List.head? : List α → Option α) := by
  exact (listCases none (fun z : α×List α => Option.some z.1) (by fun_prop)).congr
    (fun l => by cases l <;> rfl)

@[fun_prop] theorem listFilterParam [Inhabited α] [Inhabited β]
    (f : α×β → Bool) (hf : Poly f) :
    Poly (fun z : α×List β => z.2.filter (fun b => f (z.1,b))) := by
  have h : Poly (fun z : α×List β => ((z.2.map fun b => (z.1,b)).filter f).map Prod.snd) := by
    exact comp _ _ (listMap Prod.snd (by fun_prop))
      (comp _ _ (listFilter f hf) (listMapParam (fun z : α×β => z) identity))
  exact h.congr (fun z => by simp [List.filter_map,Function.comp_def])

@[fun_prop] theorem filterWith [Inhabited α] [Inhabited β]
    (l : α → List β) (f : α×β → Bool) (hl : Poly l) (hf : Poly f) :
    Poly (fun a => (l a).filter (fun b => f (a,b))) :=
  comp _ (fun a => (a,l a)) (listFilterParam f hf) (by fun_prop)

@[fun_prop] theorem listFind [Inhabited α] (p : α → Bool) (hp : Poly p) :
    Poly (List.find? p) := by
  have h : Poly (fun l : List α => (l.filter p).head?) := by fun_prop
  exact h.congr (fun l => by
    induction l with
    | nil => rfl
    | cons a l ih => cases h : p a <;> simp [h,ih])

@[fun_prop] theorem listFindParam [Inhabited α] [Inhabited β]
    (p : α×β → Bool) (hp : Poly p) :
    Poly (fun z : α×List β => z.2.find? (fun b => p (z.1,b))) := by
  have h : Poly (fun z : α×List β => (z.2.filter (fun b => p (z.1,b))).head?) :=
    comp _ _ listHeadOption (listFilterParam p hp)
  exact h.congr (fun z => by
    have hh : ∀ l : List β,(l.filter (fun b => p (z.1,b))).head?=l.find? (fun b => p (z.1,b)) := by
      intro l
      induction l with
      | nil => rfl
      | cons a l ih => cases h : p (z.1,a) <;> simp [h,ih]
    exact hh _)

@[fun_prop] theorem findWith [Inhabited α] [Inhabited β]
    (l : α → List β) (p : α×β → Bool) (hl : Poly l) (hp : Poly p) :
    Poly (fun a => (l a).find? (fun b => p (a,b))) :=
  comp _ (fun a => (a,l a)) (listFindParam p hp) (by fun_prop)

end Poly
end BinaryMatching.StackCode
end

end OAI
