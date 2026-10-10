import OAI.Computability.Scheduling.PolynomialLoops

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9 u10 u11 u12 u13 u14 u15 u16

section
namespace ThreeMachine.StackCompiler

@[simp] theorem volume_block {n : ℕ} (b : Algorithm.Block (Fin n)) :
    volume b = volume b.length+volume b.time+1 := by
  change volume (b.length,b.time) = _
  rw [volume_pair]

theorem block_length_le_volume {n : ℕ} (b : Algorithm.Block (Fin n)) : b.length ≤ volume b := by
  rw [volume_block,volume_nat]; omega

theorem block_time_volume_le {n : ℕ} (b : Algorithm.Block (Fin n)) : volume b.time ≤ volume b := by
  rw [volume_block]; omega

namespace Poly
variable {J : Type u1} {s n : J → ℕ} {d e : ℕ}
theorem blockLength (b : ∀ j, Algorithm.Block (Fin (n j)))
    (h : Poly s (fun j => volume (b j)) d) : Poly s (fun j => (b j).length) d :=
  of_le (fun j => block_length_le_volume (b j)) h

theorem blockTime (b : ∀ j, Algorithm.Block (Fin (n j)))
    (h : Poly s (fun j => volume (b j)) d) : Poly s (fun j => volume (b j).time) d :=
  of_le (fun j => block_time_volume_le (b j)) h

theorem volumeBlock (b : ∀ j, Algorithm.Block (Fin (n j)))
    (hl : Poly s (fun j => (b j).length) d)
    (ht : Poly s (fun j => volume (b j).time) e) : Poly s (fun j => volume (b j)) (Max.max d e) := by
  simp only [volume_block,volume_nat]
  poly_bound

variable {α : J → Type u2} {β : J → Type u3} [∀ j, Coding (α j)] [∀ j, Coding (β j)]
theorem volumeFst (p : ∀ j, α j × β j) (h : Poly s (fun j => volume (p j)) d) :
    Poly s (fun j => volume (p j).1) d := of_le (fun j => by rw [volume_prod]; omega) h

theorem volumeSnd (p : ∀ j, α j × β j) (h : Poly s (fun j => volume (p j)) d) :
    Poly s (fun j => volume (p j).2) d := of_le (fun j => by rw [volume_prod]; omega) h

omit [∀ j, Coding (β j)] in
theorem volumeOption (o : ∀ j, Option (α j)) {v : J → ℕ}
    (h : Poly s v d) (hv : ∀ j, ∀ a ∈ o j, volume a ≤ v j) : Poly s (fun j => volume (o j)) d := by
  apply of_le (fun j => volume_option_le (o j) (v j) (hv j))
  poly_bound

omit [∀ j, Coding (β j)] in
theorem volumeOptionSome (a : ∀ j, α j) (h : Poly s (fun j => volume (a j)) d) :
    Poly s (fun j => volume (some (a j))) d := by simp only [volume_some]; poly_bound

omit [∀ j, Coding (β j)] in
theorem volumeOptionNone (s : J → ℕ) : Poly s (fun j => volume (none : Option (α j))) 0 := by
  simp only [volume_none]; exact const s 1

end Poly
end ThreeMachine.StackCompiler
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {I : Type u4} {J : Type u5} {s : J → ℕ}
variable {α : I → Type u6} {β : I → Type u7} {γ : I → Type u8} [∀ i, Coding (α i)] [∀ i, Coding (β i)] [∀ i, Coding (γ i)]
variable (idx : J → I) (xs : ∀ j, List (α (idx j))) (e : ∀ j, γ (idx j))

theorem flatMapTime {f : ∀ i, α i × γ i → List (β i)} (R : Uniform f) {l t vx ve v : ℕ}
    (hl : Poly s (fun j => (xs j).length) l)
    (ht : Poly (fun p : Pool idx xs => s p.1)
      (fun p => R.time (idx p.1) (p.2.1,e p.1)) t)
    (hx : Poly s (fun j => volume (xs j)) vx)
    (he : Poly s (fun j => volume (e j)) ve)
    (hv : Poly (fun p : Pool idx xs => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => R.flatMap.time (idx j) (xs j,e j))
      (l+v+Max.max t (Max.max vx (Max.max ve (l+v)))) := by
  have hm := volumeMap idx xs e (β := fun i => List (β i)) hl hv
  have hfV : Poly s (fun j => volume ((xs j).flatMap (fun a => f (idx j) (a,e j)))) (l+v) := by
    have hv (j : J) : volume ((xs j).flatMap (fun a => f (idx j) (a,e j))) ≤
        volume ((xs j).map (fun a => f (idx j) (a,e j))) := by
      rw [volume_flatten,← List.flatMap_def]
      omega
    exact of_le hv hm
  have hf := lengthVolume _ hfV
  obtain ⟨C,hC⟩ := ht
  have hT := powerBase s C t
  apply of_le (fun j => Uniform.time_flatMap R (idx j) (xs j) (e j)
    (C*(s j+2)^t) (fun a ha => hC ⟨j,⟨a,ha⟩⟩))
  poly_bound

variable (o : ∀ j, Option (α (idx j)))

theorem optionMapTime {f : ∀ i, α i × γ i → β i} (R : Uniform f) {t vo ve v : ℕ}
    (ht : Poly (fun p : Pool idx (fun j => (o j).toList) => s p.1)
      (fun p => R.time (idx p.1) (p.2.1,e p.1)) t)
    (ho : Poly s (fun j => volume (o j)) vo)
    (he : Poly s (fun j => volume (e j)) ve)
    (hv : Poly (fun p : Pool idx (fun j => (o j).toList) => s p.1)
      (fun p => volume (f (idx p.1) (p.2.1,e p.1))) v) :
    Poly s (fun j => R.optionMap.time (idx j) (o j,e j)) (Max.max t (Max.max vo (Max.max ve v))) := by
  obtain ⟨C,hC⟩ := ht
  obtain ⟨D,hD⟩ := hv
  have hT := powerBase s C t
  have hV := powerBase s D v
  apply of_le (fun j => Uniform.time_optionMap R (idx j) (o j) (e j)
    (C*(s j+2)^t) (D*(s j+2)^v) (fun a ha => hC ⟨j,⟨a,by simpa using ha⟩⟩)
      (fun a ha => hD ⟨j,⟨a,by simpa using ha⟩⟩))
  poly_bound

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u9} {s : J → ℕ} {d e : ℕ} {α : J → Type u10} {β : J → Type u11}
variable [∀ j, Coding (α j)] [∀ j, Coding (β j)]

omit [∀ j, Coding (α j)] [∀ j, Coding (β j)] in
theorem lengthOption (o : ∀ j, Option (α j)) : Poly s (fun j => (o j).toList.length) 0 :=
  of_le (fun j => by cases o j <;> simp) (const s 1)

omit [∀ j, Coding (β j)] in
theorem volumeIte (p : J → Prop) [∀ j, Decidable (p j)] (a b : ∀ j, α j)
    (ha : Poly s (fun j => volume (a j)) d) (hb : Poly s (fun j => volume (b j)) e) :
    Poly s (fun j => volume (if p j then a j else b j)) (Max.max d e) := by
  convert iteNat p ha hb using 1
  funext j; split <;> rfl

omit [∀ j, Coding (α j)] in
theorem volumeOptionMap (f : ∀ j, α j → β j) (o : ∀ j, Option (α j))
    (h : Poly (fun p : ListPool (fun j => (o j).toList) => s p.1)
      (fun p => volume (f p.1 p.2.1)) d) : Poly s (fun j => volume ((o j).map (f j))) d := by
  obtain ⟨C,hC⟩ := h
  apply volumeOption _ (powerBase s C d)
  intro j b hb
  cases ho : o j with
  | none => simp [ho] at hb
  | some a =>
    have he : f j a = b := by simpa [ho] using hb
    subst b
    exact hC ⟨j,⟨a,by simp [ho]⟩⟩

end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u12} {s : J → ℕ} {d : ℕ} {K V : J → Type}
variable [∀ j, Coding (K j)] [∀ j, Coding (V j)] [∀ j, DecidableEq (K j)]
theorem volumeLookup (xs : ∀ j, List (K j × V j)) (k : ∀ j, K j)
    (h : Poly s (fun j => volume (xs j)) d) :
    Poly s (fun j => volume (Algorithm.lookup (xs j) (k j))) d := by
  apply volumeOption _ h
  intro j v hv
  have h := volume_mem_le (Algorithm.lookup_mem hv)
  rw [volume_prod] at h
  dsimp only at h
  omega
end ThreeMachine.StackCompiler.Poly

namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u13} {s : J → ℕ} {d : ℕ} {α : J → Type u14} [∀ j, Coding (α j)]
theorem volumeOptionToList (o : ∀ j, Option (α j))
    (h : Poly s (fun j => volume (o j)) d) :
    Poly s (fun j => volume (o j).toList) d := by
  simpa only [volume_optionToList] using h
end ThreeMachine.StackCompiler.Poly
end

section
namespace ThreeMachine.StackCompiler.Poly
variable {J : Type u15} {s : J → ℕ} {d e : ℕ} {α : J → Type u16}
theorem lengthCons (a : ∀ j, α j) (xs : ∀ j, List (α j))
    (h : Poly s (fun j => (xs j).length) d) :
    Poly s (fun j => (a j :: xs j).length) d := by
  simp only [List.length_cons]; poly_bound

theorem lengthTail (xs : ∀ j, List (α j))
    (h : Poly s (fun j => (xs j).length) d) :
    Poly s (fun j => (xs j).tail.length) d :=
  of_le (fun j => by simp only [List.length_tail]; omega) h

theorem lengthTake (k : J → ℕ) (xs : ∀ j, List (α j))
    (h : Poly s (fun j => (xs j).length) d) :
    Poly s (fun j => ((xs j).take (k j)).length) d :=
  of_le (fun j => (List.take_sublist (k j) (xs j)).length_le) h

theorem lengthDrop (k : J → ℕ) (xs : ∀ j, List (α j))
    (h : Poly s (fun j => (xs j).length) d) :
    Poly s (fun j => ((xs j).drop (k j)).length) d :=
  of_le (fun j => (List.drop_sublist (k j) (xs j)).length_le) h

theorem lengthReverse (xs : ∀ j, List (α j))
    (h : Poly s (fun j => (xs j).length) d) :
    Poly s (fun j => (xs j).reverse.length) d := by simpa only [List.length_reverse] using h

theorem lengthAppend (xs ys : ∀ j, List (α j))
    (hx : Poly s (fun j => (xs j).length) d) (hy : Poly s (fun j => (ys j).length) e) :
    Poly s (fun j => (xs j ++ ys j).length) (Max.max d e) := by
  simpa only [List.length_append] using hx.add hy

theorem lengthRange (k : J → ℕ) (h : Poly s k d) :
    Poly s (fun j => (List.range (k j)).length) d := by simpa only [List.length_range] using h

theorem lengthReplicate (k : J → ℕ) (a : ∀ j, α j) (h : Poly s k d) :
    Poly s (fun j => (List.replicate (k j) (a j)).length) d := by simpa only [List.length_replicate] using h
end ThreeMachine.StackCompiler.Poly
end

end OAI
