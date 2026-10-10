import OAI.Combinatorics.EditDistance.BlockAlignment

namespace OAI

/-!
# Fixed-length binary embeddings with unrestricted edit distance
-/

namespace EditDistortion
variable {A B : Type*}

lemma Script.flatMap {n w : ℕ} {x y : List A} (h : Script false n x y)
    (c : A → List B) (hc : ∀ a, (c a).length = w) :
    Script false (w*n) (x.flatMap c) (y.flatMap c) := by
  induction h with
  | nil x => simpa using Script.nil (substitutions := false) (x.flatMap c)
  | @cons n x y z first rest ih =>
    have he : Script false w (x.flatMap c) (y.flatMap c) := by
      cases first with
      | insert p q a =>
        have h := ((Script.to_nil (s := false) (c a)).symm.append_left (p.flatMap c)).append_right (q.flatMap c)
        simpa only [hc,List.append_nil,List.flatMap_append,List.flatMap_cons,List.append_assoc] using h
      | delete p q a =>
        have h := ((Script.to_nil (s := false) (c a)).append_left (p.flatMap c)).append_right (q.flatMap c)
        simpa only [hc,List.append_nil,List.flatMap_append,List.flatMap_cons,List.append_assoc] using h
      | substitute hf => cases hf
    simpa only [Nat.mul_add,Nat.mul_one,Nat.add_comm] using he.trans ih

lemma indel_flatMap_le (c : A → List B) (w : ℕ) (hc : ∀ a, (c a).length = w) (x y : List A) :
    indel (x.flatMap c) (y.flatMap c) ≤ w * indel x y :=
  cost_le ((cost_spec (s := false) x y).flatMap c hc)

lemma indel_replicate_le (a : A) (r s : ℕ) :
    indel (List.replicate r a) (List.replicate s a) ≤ (r-s)+(s-r) := by
  by_cases h : r ≤ s
  · have hs : (List.replicate r a).Sublist (List.replicate s a) := (List.replicate_sublist_replicate a).mpr h
    have he := (Script.of_sublist hs).symm
    have hcost := cost_le he
    simpa only [cost,indel,List.length_replicate,Nat.sub_eq_zero_of_le h,Nat.zero_add] using hcost
  · have hs : (List.replicate s a).Sublist (List.replicate r a) := (List.replicate_sublist_replicate a).mpr (by omega)
    have hcost := cost_le (Script.of_sublist hs)
    simpa only [cost,indel,List.length_replicate,Nat.sub_eq_zero_of_le (show s ≤ r by omega),Nat.add_zero] using hcost

end EditDistortion

namespace EditCode
open EditDistortion
variable {A : Type*} {t : ℕ}

theorem indel_code_upper (label : A → Fin t → Bool) (x y : List A) :
    indel (encode label x) (encode label y) ≤ width t * indel x y :=
  indel_flatMap_le (block label) (width t) (block_length label) x y

def fixed (label : A → Fin t → Bool) (D : ℕ) (x : List A) : List Bool :=
  padded label x (width t * (D-x.length))

@[simp] lemma fixed_length (label : A → Fin t → Bool) (D : ℕ) (x : List A) (hx : x.length ≤ D) :
    (fixed label D x).length = width t * D := by
  simp only [fixed,padded_length,←Nat.mul_add,Nat.add_sub_of_le hx]

theorem indel_fixed_upper (label : A → Fin t → Bool) (D : ℕ) (x y : List A)
    (hx : x.length ≤ D) (hy : y.length ≤ D) :
    indel (fixed label D x) (fixed label D y) ≤ 2 * width t * indel x y := by
  have h := cost_append_le (s := false) (encode label x) (encode label y)
    (List.replicate (width t*(D-x.length)) false) (List.replicate (width t*(D-y.length)) false)
  have hr := indel_replicate_le false (width t*(D-x.length)) (width t*(D-y.length))
  have hc := indel_code_upper label x y
  have hl := cost_length_bounds (s := false) x y
  change x.length ≤ y.length + indel x y ∧ y.length ≤ x.length + indel x y at hl
  have hd : width t*(D-x.length)-width t*(D-y.length) +
      (width t*(D-y.length)-width t*(D-x.length)) ≤ width t*indel x y := by
    rw [←Nat.mul_sub_left_distrib,←Nat.mul_sub_left_distrib,←Nat.mul_add]
    apply Nat.mul_le_mul_left
    omega
  change indel (fixed label D x) (fixed label D y) ≤
    indel (encode label x) (encode label y) +
      indel (List.replicate (width t*(D-x.length)) false) (List.replicate (width t*(D-y.length)) false) at h
  nlinarith

end EditCode

namespace EditCode
variable (A : Type*) [Fintype A]

noncomputable def labels : A ↪ (Fin (Nat.clog 2 (Fintype.card A)) → Bool) :=
  Classical.choice (Function.Embedding.nonempty_of_card_le (by
    simpa only [Fintype.card_fun,Fintype.card_fin,Fintype.card_bool] using
      Nat.le_pow_clog (by norm_num : 1 < 2) (Fintype.card A)))

end EditCode

end OAI
