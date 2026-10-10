import OAI.Combinatorics.TreeEdit.CyclicWords

namespace OAI

namespace TreeEdit

universe u v

variable {α : Type u} {x y z : List α}

attribute [local instance] Classical.propDecidable

namespace EditStep

protected lemma map {β : Type*} (f : α → β) (h : EditStep x y) :
    EditStep (x.map f) (y.map f) := by
  cases h with
  | insert p q a => simpa using EditStep.insert (p.map f) (q.map f) (f a)
  | delete p q a => simpa using EditStep.delete (p.map f) (q.map f) (f a)
  | substitute p q a b => simpa using EditStep.substitute (p.map f) (q.map f) (f a) (f b)

end EditStep

namespace EditScript

protected lemma map {β : Type*} (f : α → β) {n : ℕ} (h : EditScript x y n) :
    EditScript (x.map f) (y.map f) n := by
  induction h with
  | nil => exact .nil _
  | cons h _ ih => exact .cons (h.map f) ih

end EditScript

lemma ed_map {β : Type*} (f : α → β) (x y : List α) : ed (x.map f) (y.map f) ≤ ed x y :=
  ed_le_of_script ((ed_script x y).map f)

lemma ed_flatten_ofFn {n : ℕ} (x y : Fin n → List α) :
    ed (List.ofFn x).flatten (List.ofFn y).flatten ≤ ∑ i, ed (x i) (y i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.ofFn_succ, List.flatten_cons, Fin.sum_univ_succ]
    exact (ed_append _ _ _ _).trans (Nat.add_le_add_left (ih _ _) _)

namespace Words

variable {β : Type v} {n : ℕ}

lemma ofFn_get (x : Word β n) : List.ofFn (get x) = x.val := by
  rcases x with ⟨x, rfl⟩
  exact List.ofFn_get x

lemma cycles_val {m T B : ℕ} {β : Fin m → Type*}
    (x : Fin T → ∀ i, Word (β i) B) :
    (cycles x).val = (List.ofFn fun a =>
      (List.ofFn fun i => ((x a i).val.map (Sigma.mk i))).flatten).flatten := by
  change List.ofFn _ = _
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext a
  rw [List.ofFn_mul]
  congr 1
  apply congrArg List.ofFn
  funext i
  rw [← ofFn_get (x a i), List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hmB : 0 < m * B := Nat.mul_pos hm hB
  have hi : i.val * B + j.val < m * B := by nlinarith [i.isLt, j.isLt]
  have hd₁ : (a.val * (m * B) + (i.val * B + j.val)) / (m * B) = a.val := by
    rw [Nat.mul_comm a.val, Nat.mul_add_div hmB, Nat.div_eq_of_lt hi, add_zero]
  have hr₁ : (a.val * (m * B) + (i.val * B + j.val)) % (m * B) = i.val * B + j.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt hi]
  have hd₂ : (i.val * B + j.val) / B = i.val := by
    rw [Nat.mul_comm i.val, Nat.mul_add_div hB, Nat.div_eq_of_lt j.isLt, add_zero]
  have hr₂ : (i.val * B + j.val) % B = j.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  let r : Fin (T * (m * B)) := ⟨a.val * (m * B) + (i.val * B + j.val), by
    nlinarith [a.isLt]⟩
  have hra : r.divNat = a := Fin.ext hd₁
  have hri : r.modNat.divNat = i := by
    apply Fin.ext
    change (a.val * (m * B) + (i.val * B + j.val)) % (m * B) / B = i.val
    rw [hr₁, hd₂]
  have hrj : r.modNat.modNat = j := by
    apply Fin.ext
    change (a.val * (m * B) + (i.val * B + j.val)) % (m * B) % B = j.val
    rw [hr₁, hr₂]
  change Sigma.mk r.modNat.divNat (get (x r.divNat r.modNat.divNat) r.modNat.modNat) =
    Sigma.mk i (get (x a i) j)
  rw [hra, hri, hrj]

lemma ed_cycles {m T B : ℕ} {β : Fin m → Type*}
    (x y : Fin T → ∀ i, Word (β i) B) :
    ed (cycles x).val (cycles y).val ≤ ∑ a : Fin T, ∑ i : Fin m,
      ed (x a i).val (y a i).val := by
  rw [cycles_val, cycles_val]
  apply (ed_flatten_ofFn _ _).trans
  apply Finset.sum_le_sum
  intro a _
  apply (ed_flatten_ofFn _ _).trans
  exact Finset.sum_le_sum fun i _ => ed_map (Sigma.mk i) _ _

end Words

lemma sublist_ofFn_embedding {n N : ℕ} (f : Fin N → α) (e : Fin n ↪o Fin N) :
    (List.ofFn (fun i => f (e i))).Sublist (List.ofFn f) := by
  apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
  refine ⟨((Fin.castOrderIso List.length_ofFn).toOrderEmbedding.comp e).comp
    (Fin.castOrderIso List.length_ofFn.symm).toOrderEmbedding, ?_⟩
  intro i
  simp [List.get_eq_getElem, Fin.cast]

lemma length_flatten_ofFn {n C : ℕ} (x : Fin n → List α) (hx : ∀ i, (x i).length = C) :
    (List.ofFn x).flatten.length = n * C := by
  simp [List.length_flatten, List.map_ofFn, Function.comp_def, hx]

lemma ed_shifted_flatten {T C s : ℕ} (hs : s ≤ T) (x y : Fin T → List α)
    (hx : ∀ i, (x i).length = C) (hy : ∀ i, (y i).length = C)
    (he : ∀ a : Fin (T - s), x ⟨a.val + s, by have := a.isLt; omega⟩ =
      y ⟨a.val, by have := a.isLt; omega⟩) :
    ed (List.ofFn x).flatten (List.ofFn y).flatten ≤ 2 * s * C := by
  let f : Fin (T - s) ↪o Fin T := OrderEmbedding.ofStrictMono
    (fun a => ⟨a.val + s, by have := a.isLt; omega⟩) (by intro a b hab; simpa using hab)
  let g : Fin (T - s) ↪o Fin T := OrderEmbedding.ofStrictMono
    (fun a => ⟨a.val, by have := a.isLt; omega⟩) (by intro a b hab; exact hab)
  have hl := (sublist_ofFn_embedding x f).flatten
  have hr := (sublist_ofFn_embedding y g).flatten
  have he' : (fun a => x (f a)) = (fun a => y (g a)) := funext he
  rw [← he'] at hr
  have hlen := length_flatten_ofFn (fun a => x (f a)) (fun a => hx (f a))
  have hh := length_le_lcs hl hr
  rw [hlen] at hh
  have hc := ed_le_twice_deficit (x := (List.ofFn x).flatten) (y := (List.ofFn y).flatten)
    ((length_flatten_ofFn x hx).trans (length_flatten_ofFn y hy).symm)
  simp only [deficit, length_flatten_ofFn x hx] at hc
  have hmul : (T - s) * C + s * C = T * C := by rw [← Nat.add_mul, Nat.sub_add_cancel hs]
  have hdef : T * C - lcs (List.ofFn x).flatten (List.ofFn y).flatten ≤ s * C := by omega
  calc
    _ ≤ 2 * (T * C - lcs (List.ofFn x).flatten (List.ofFn y).flatten) := hc
    _ ≤ 2 * (s * C) := Nat.mul_le_mul_left 2 hdef
    _ = 2 * s * C := by ring

namespace Words

variable {β : Type v} {n : ℕ}

lemma ed_cycles_shift {m T B s : ℕ} {β : Fin m → Type*} (hs : s ≤ T)
    (x y : Fin T → ∀ i, Word (β i) B)
    (he : ∀ a : Fin (T - s), ∀ i,
      x ⟨a.val + s, by have := a.isLt; omega⟩ i =
      y ⟨a.val, by have := a.isLt; omega⟩ i) :
    ed (cycles x).val (cycles y).val ≤ 2 * s * (m * B) := by
  rw [cycles_val, cycles_val]
  apply ed_shifted_flatten hs
  · intro a; exact length_flatten_ofFn _ (fun i => by simp [(x a i).property])
  · intro a; exact length_flatten_ofFn _ (fun i => by simp [(y a i).property])
  · intro a
    congr 1
    apply congrArg List.ofFn
    funext i
    rw [he a i]

end Words

end TreeEdit

end OAI
