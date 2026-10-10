import OAI.MathematicalPhysics.NavierStokes.BalancedTransport.NumericPrograms

namespace OAI

noncomputable section
namespace BalancedTransport.Effectivity.ComputableRules
attribute [fun_prop] Computable
variable {α β γ : Type*} [Primcodable α] [Primcodable β] [Primcodable γ]

@[fun_prop] lemma identity : Computable (fun x : α => x) := Computable.id

@[fun_prop] lemma constant (b : β) : Computable (fun _ : α => b) := Computable.const b

@[fun_prop] lemma compose (f : β → γ) (g : α → β) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => f (g x)) := hf.comp hg

@[fun_prop] lemma fst (f : α → β × γ) (hf : Computable f) :
    Computable (fun x => (f x).1) := Computable.fst.comp hf

@[fun_prop] lemma snd (f : α → β × γ) (hf : Computable f) :
    Computable (fun x => (f x).2) := Computable.snd.comp hf

@[fun_prop] lemma pair (f : α → β) (g : α → γ) (hf : Computable f) (hg : Computable g) :
    Computable (fun x => (f x, g x)) := hf.pair hg

@[fun_prop] lemma addNat : Computable (fun p : ℕ × ℕ => p.1 + p.2) := Primrec.nat_add.to_comp

@[fun_prop] lemma mulNat : Computable (fun p : ℕ × ℕ => p.1 * p.2) := Primrec.nat_mul.to_comp

@[fun_prop] lemma subNat : Computable (fun p : ℕ × ℕ => p.1 - p.2) := Primrec.nat_sub.to_comp

@[fun_prop] lemma succNat : Computable Nat.succ := Computable.succ

@[fun_prop] lemma constAddRat : Computable (fun p : ℚ × ℚ => p.1 + p.2) := computable_rat_add

@[fun_prop] lemma constMulRat : Computable (fun p : ℚ × ℚ => p.1 * p.2) := computable_rat_mul

@[fun_prop] lemma negRat : Computable (fun q : ℚ => -q) := computable_rat_neg

@[fun_prop] lemma invRat : Computable (fun q : ℚ => q⁻¹) := computable_rat_inv

@[fun_prop] lemma absNat : Computable Int.natAbs := primrec_int_natAbs.to_comp

@[fun_prop] lemma ratNum : Computable Rat.num := computable_rat_num

@[fun_prop] lemma consList : Computable (fun p : β × List β => p.1 :: p.2) := Primrec.list_cons.to_comp

@[fun_prop] lemma appendList : Computable (fun p : List β × List β => p.1 ++ p.2) := Primrec.list_append.to_comp

@[fun_prop] lemma lengthList : Computable (fun p : List β => p.length) := Computable.list_length

@[fun_prop] lemma getDList (b : β) : Computable (fun p : List β × ℕ => p.1.getD p.2 b) :=
  (Primrec.list_getD b).to_comp

@[fun_prop] lemma valFin {n : ℕ} : Computable (fun i : Fin n => i.val) := Primrec.fin_val.to_comp

@[fun_prop] lemma appFin {n : ℕ} : Computable (fun p : (Fin n → β) × Fin n => p.1 p.2) := Computable.fin_app

@[fun_prop] lemma ofFnList {n : ℕ} (f : α → Fin n → β) (hf : ∀ i, Computable (fun a => f a i)) :
    Computable (fun a => List.ofFn (f a)) := Computable.list_ofFn hf

lemma mapList [Inhabited β] {f : α → List β} {g : α → β → γ} (hf : Computable f)
    (hg : Computable (fun p : α × β => g p.1 p.2)) :
    Computable (fun a => (f a).map (g a)) := by
  have h := computable_foldl hf (Computable.const ([] : List γ))
    (h := fun a p => p.1 ++ [g a p.2]) (by change Computable (fun p : α × (List γ × β) => _); fun_prop)
  apply h.of_eq
  intro a
  have hh : ∀ (l : List β) (s : List γ), l.foldl (fun s b => s ++ [g a b]) s = s ++ l.map (g a) := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih => intro s; simp only [List.foldl_cons, List.map_cons, ih, List.append_assoc, List.singleton_append]
  simpa using hh (f a) []

lemma flatMapList [Inhabited β] {f : α → List β} {g : α → β → List γ} (hf : Computable f)
    (hg : Computable (fun p : α × β => g p.1 p.2)) :
    Computable (fun a => (f a).flatMap (g a)) := by
  have h := computable_foldl hf (Computable.const ([] : List γ))
    (h := fun a p => p.1 ++ g a p.2) (by change Computable (fun p : α × (List γ × β) => _); fun_prop)
  apply h.of_eq
  intro a
  have hh : ∀ (l : List β) (s : List γ), l.foldl (fun s b => s ++ g a b) s = s ++ l.flatMap (g a) := by
    intro l
    induction l with
    | nil => simp
    | cons b l ih => intro s; simp only [List.foldl_cons, List.flatMap_cons, ih, List.append_assoc]
  simpa using hh (f a) []

end BalancedTransport.Effectivity.ComputableRules
end

end OAI
