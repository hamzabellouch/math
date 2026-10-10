import OAI.Combinatorics.EditDistance.RowAlignment

namespace OAI

/-!
# Payload restrictions and fresh-marker row separation
-/

namespace EditDistortion

lemma sublist_ofFn_comp {A : Type*} {m n : ℕ} (x : Fin n → A) (f : Fin m ↪o Fin n) :
    (List.ofFn (fun i => x (f i))).Sublist (List.ofFn x) := by
  apply List.sublist_iff_exists_fin_orderEmbedding_get_eq.mpr
  refine ⟨((Fin.castOrderIso (List.length_ofFn (f := fun i => x (f i)))).toOrderEmbedding.trans f).trans
    (Fin.castOrderIso (List.length_ofFn (f := x)).symm).toOrderEmbedding, ?_⟩
  intro i
  simp only [List.get_ofFn]
  rfl

lemma indel_le_of_matching {A : Type*} {m n k : ℕ} (x : Fin m → A) (y : Fin n → A)
    (f : Fin k ↪o Fin m) (g : Fin k ↪o Fin n) (heq : ∀ i, x (f i) = y (g i)) :
    indel (List.ofFn x) (List.ofFn y) ≤ m + n - 2 * k := by
  have hx := sublist_ofFn_comp x f
  have hy := sublist_ofFn_comp y g
  have hz : (fun i => x (f i)) = (fun i => y (g i)) := funext heq
  rw [← hz] at hy
  simpa only [List.length_ofFn] using indel_le_matching_loss hx hy

end EditDistortion

namespace EditRows

lemma payload_mod {B i x : ℕ} (hB : 0 < B) (hx : x ∈ payload B i) :
    x % (2 * B) < B := by
  have hd := payload_index hB hx
  have hx := mem_payload.mp hx
  have hm := Nat.mod_add_div x (2 * B)
  rw [hd] at hm
  omega

def rowValue {A : Type*} {L B : ℕ} (P : Fin L → Fin B → A)
    (x : Fin (2 * B * L)) : Option A :=
  if h : x.val % (2 * B) < B then
    some (P ⟨x.val / (2 * B), (Nat.div_lt_iff_lt_mul (by omega)).mpr
      (by simpa only [Nat.mul_comm] using x.isLt)⟩ ⟨x.val % (2 * B), h⟩)
  else none

def rowWord {A : Type*} {L B : ℕ} (P : Fin L → Fin B → A) : List (Option A) :=
  List.ofFn (rowValue P)

@[simp] lemma rowWord_length {A : Type*} {L B : ℕ} (P : Fin L → Fin B → A) :
    (rowWord P).length = 2 * B * L := by simp [rowWord]

lemma rowValue_ne_none {A : Type*} {L B : ℕ} (P : Fin L → Fin B → A)
    (x : Fin (2 * B * L)) : rowValue P x ≠ none ↔ x.val % (2 * B) < B := by
  unfold rowValue
  split_ifs <;> simp_all

def payloadOffset {B i x : ℕ} (h : x ∈ payload B i) : Fin B :=
  ⟨x - 2 * B * i, by have h := mem_payload.mp h; omega⟩

lemma rowValue_payload {A : Type*} {L B : ℕ} (hB : 0 < B) (P : Fin L → Fin B → A)
    (i : Fin L) (x : Fin (2 * B * L)) (hx : x.val ∈ payload B i) :
    rowValue P x = some (P i (payloadOffset hx)) := by
  have hd := payload_index hB hx
  have hm := payload_mod hB hx
  rw [rowValue, dite_eq_left hm]
  congr 2
  · exact Fin.ext hd
  · apply Fin.ext
    change x.val % (2 * B) = x.val - 2 * B * i.val
    have hh := Nat.mod_add_div x.val (2 * B)
    rw [hd] at hh
    omega

end EditRows

namespace EditRows

lemma local_matching_bound {A : Type*} {k L B : ℕ} {t : ℝ}
    (P Q : Fin L → Fin B → A) (hB : 0 < B)
    (f g : Fin k → Fin (2 * B * L))
    (hf : StrictMono (fun a => (f a).val)) (hg : StrictMono (fun a => (g a).val))
    (heq : ∀ a, rowValue P (f a) = rowValue Q (g a))
    (ht : t ≤ B)
    (hsep : ∀ i j : Fin L, 2 * t ≤
      (EditDistortion.indel (List.ofFn (P i)) (List.ofFn (Q j)) : ℝ))
    (i : Fin L) (j : ℕ) :
    t + (((rowMatches (fun a => (f a).val) B i).filter
      (fun a => (g a).val ∈ payload B j)).card : ℝ) ≤ B := by
  classical
  let K := (rowMatches (fun a => (f a).val) B i).filter
    (fun a => (g a).val ∈ payload B j)
  change t + (K.card : ℝ) ≤ B
  by_cases hj : j < L
  · let e : Fin K.card ↪o Fin k := K.orderEmbOfFin rfl
    have hp : ∀ r : Fin K.card,
        (f (e r)).val ∈ payload B i ∧ (g (e r)).val ∈ payload B j := by
      intro r
      have h := K.orderEmbOfFin_mem rfl r
      exact ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp h).1).2,
        (Finset.mem_filter.mp h).2⟩
    let ff : Fin K.card → Fin B := fun r => payloadOffset (hp r).1
    let gg : Fin K.card → Fin B := fun r => payloadOffset (hp r).2
    have hff : StrictMono ff := by
      intro r s hrs
      have h := hf (e.strictMono hrs)
      change (f (e r)).val < (f (e s)).val at h
      have hr := mem_payload.mp (hp r).1
      have hs := mem_payload.mp (hp s).1
      change (f (e r)).val - 2 * B * i.val < (f (e s)).val - 2 * B * i.val
      omega
    have hgg : StrictMono gg := by
      intro r s hrs
      have h := hg (e.strictMono hrs)
      change (g (e r)).val < (g (e s)).val at h
      have hr := mem_payload.mp (hp r).2
      have hs := mem_payload.mp (hp s).2
      change (g (e r)).val - 2 * B * j < (g (e s)).val - 2 * B * j
      omega
    have he : ∀ r, P i (ff r) = Q ⟨j, hj⟩ (gg r) := by
      intro r
      have h := heq (e r)
      rw [rowValue_payload hB P i (f (e r)) (hp r).1,
        rowValue_payload hB Q ⟨j, hj⟩ (g (e r)) (hp r).2] at h
      exact Option.some.inj h
    have hcost := EditDistortion.indel_le_of_matching (P i) (Q ⟨j, hj⟩)
      (OrderEmbedding.ofStrictMono ff hff) (OrderEmbedding.ofStrictMono gg hgg) he
    have hk : K.card ≤ B := by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective ff hff.injective
    have hcost' : (EditDistortion.indel (List.ofFn (P i)) (List.ofFn (Q ⟨j, hj⟩)) : ℝ) ≤
        ((B + B - 2 * K.card : ℕ) : ℝ) := by exact_mod_cast hcost
    rw [Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_mul] at hcost'
    norm_num at hcost'
    have hsep' := hsep i ⟨j, hj⟩
    linarith
  · have hnil : K = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro a ha
      have h := mem_payload.mp (Finset.mem_filter.mp ha).2
      have hg' := (g a).isLt
      have hh : 2 * B * L ≤ 2 * B * j := Nat.mul_le_mul_left _ (by omega)
      omega
    simpa only [hnil, Finset.card_empty, Nat.cast_zero, add_zero] using ht

theorem indel_row_separation {A : Type*} {L B : ℕ} {t : ℝ}
    (P Q : Fin L → Fin B → A) (hB : 0 < B) (ht : t ≤ B)
    (hsep : ∀ i j : Fin L, 2 * t ≤
      (EditDistortion.indel (List.ofFn (P i)) (List.ofFn (Q j)) : ℝ)) :
    (L : ℝ) * t ≤ (EditDistortion.indel (rowWord P) (rowWord Q) : ℝ) := by
  classical
  obtain ⟨z, hx, hy, hcost⟩ := EditDistortion.indel_matching (rowWord P) (rowWord Q)
  obtain ⟨f₀, hf₀⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hx
  obtain ⟨g₀, hg₀⟩ := List.sublist_iff_exists_fin_orderEmbedding_get_eq.mp hy
  let f : Fin z.length ↪o Fin (2 * B * L) :=
    f₀.trans (Fin.castOrderIso (rowWord_length P)).toOrderEmbedding
  let g : Fin z.length ↪o Fin (2 * B * L) :=
    g₀.trans (Fin.castOrderIso (rowWord_length Q)).toOrderEmbedding
  have hf : StrictMono (fun a => (f a).val) := fun _ _ h => f.strictMono h
  have hg : StrictMono (fun a => (g a).val) := fun _ _ h => g.strictMono h
  have heq : ∀ a, rowValue P (f a) = rowValue Q (g a) := by
    intro a
    have h := (hf₀ a).symm.trans (hg₀ a)
    simpa only [rowWord, List.get_ofFn] using! h
  have hclean : ∀ a : Fin z.length, ∀ i : ℕ,
      (f a).val ∈ payload B i → (g a).val % (2 * B) < B := by
    intro a i ha
    apply (rowValue_ne_none Q (g a)).mp
    rw [← heq a]
    exact (rowValue_ne_none P (f a)).mpr (payload_mod hB ha)
  have hbound := matching_loss_real hf hg hB (fun a => (f a).isLt)
    (fun a => (g a).isLt) hclean ht (local_matching_bound P Q hB f g hf hg heq ht hsep)
  have hk : z.length ≤ 2 * B * L := by simpa only [rowWord_length] using hx.length_le
  have he : 2 * (2 * B * L - z.length) =
      (rowWord P).length + (rowWord Q).length - 2 * z.length := by
    rw [rowWord_length, rowWord_length]
    omega
  rw [hcost, ← he, Nat.cast_mul, Nat.cast_ofNat]
  exact hbound

end EditRows

end OAI
