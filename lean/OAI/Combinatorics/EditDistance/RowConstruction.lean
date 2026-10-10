import OAI.Combinatorics.EditDistance.RowSeparation

namespace OAI

/-!
# Row concatenation and cyclic phase shifts
-/

namespace EditRows

lemma rowValue_offset {A : Type*} {L B : ℕ} (hB : 0 < B)
    (P : Fin L → Fin B → A) (i : Fin L) (j : Fin (2 * B)) :
    rowValue P ⟨2 * B * i.val + j.val, by nlinarith [i.isLt, j.isLt]⟩ =
      if h : j.val < B then some (P i ⟨j.val, h⟩) else none := by
  have hdiv : (2 * B * i.val + j.val) / (2 * B) = i.val := by
    simp [Nat.mul_add_div (by omega : 0 < 2 * B), Nat.div_eq_of_lt j.isLt]
  have hmod : (2 * B * i.val + j.val) % (2 * B) = j.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  unfold rowValue
  simp only [hmod, hdiv]

lemma chunk_ofFn {A : Type*} {B : ℕ} (P : Fin B → A) :
    (List.ofFn (fun j : Fin (2 * B) =>
      if h : j.val < B then some (P ⟨j.val, h⟩) else none)) =
      (List.ofFn P).map some ++ List.replicate B none := by
  rw [show 2 * B = B + B by omega]
  rw [List.ofFn_add]
  congr 1
  · rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    simp [i.isLt]
  · have he : (fun i : Fin B => if h : (Fin.natAdd B i).val < B then
        some (P ⟨(Fin.natAdd B i).val, h⟩) else none) = (fun _ => (none : Option A)) := by
      funext i
      simp
    simp only [he, List.ofFn_const]

lemma rowWord_flatten {A : Type*} {L B : ℕ} (hB : 0 < B) (P : Fin L → Fin B → A) :
    rowWord P = (List.ofFn (fun i : Fin L =>
      (List.ofFn (P i)).map some ++ List.replicate B none)).flatten := by
  rw [rowWord, List.ofFn_mul']
  congr 1
  apply congrArg List.ofFn
  funext i
  simp_rw [rowValue_offset hB]
  exact chunk_ofFn (P i)

lemma indel_flatten_le {A : Type*} (x y : List (List A)) (hlen : x.length = y.length) :
    EditDistortion.indel x.flatten y.flatten ≤
      ((x.zip y).map (fun z => EditDistortion.indel z.1 z.2)).sum := by
  induction x generalizing y with
  | nil =>
      have hy : y = [] := List.length_eq_zero_iff.mp hlen.symm
      subst y
      exact le_of_eq (EditDistortion.cost_refl (s := false) [])
  | cons a x ih =>
      cases y with
      | nil => simp at hlen
      | cons b y =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at hlen
          have hh := EditDistortion.cost_append_le (s := false) a b x.flatten y.flatten
          exact hh.trans (by simpa only [List.zip_cons_cons, List.map_cons, List.sum_cons] using! Nat.add_le_add_left (ih y hlen) (EditDistortion.indel a b))

lemma zip_ofFn {A C : Type*} {n : ℕ} (f : Fin n → A) (g : Fin n → C) :
    (List.ofFn f).zip (List.ofFn g) = List.ofFn (fun i => (f i, g i)) := by
  simp only [List.ofFn_eq_map, List.zip_map']

lemma indel_rowWord_le {A : Type*} {L B : ℕ} (hB : 0 < B)
    (P Q : Fin L → Fin B → A) :
    EditDistortion.indel (rowWord P) (rowWord Q) ≤
      ∑ i, EditDistortion.indel (List.ofFn (P i)) (List.ofFn (Q i)) := by
  classical
  rw [rowWord_flatten hB P, rowWord_flatten hB Q]
  have h := indel_flatten_le
    (List.ofFn (fun i : Fin L => (List.ofFn (P i)).map some ++ List.replicate B none))
    (List.ofFn (fun i : Fin L => (List.ofFn (Q i)).map some ++ List.replicate B none)) (by simp)
  apply h.trans
  rw [zip_ofFn, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_le_sum
  intro i _
  have ha := EditDistortion.cost_append_le (s := false)
    ((List.ofFn (P i)).map some) ((List.ofFn (Q i)).map some)
    (List.replicate B none) (List.replicate B none)
  have hb := EditDistortion.cost_map_le (s := false) some (List.ofFn (P i)) (List.ofFn (Q i))
  simpa only [EditDistortion.cost_refl, Nat.add_zero] using! ha.trans (Nat.add_le_add_right hb _)

end EditRows

namespace EditRows

lemma indel_shift_flatten {A : Type*} {n R : ℕ} (P Q : Fin (n+1) → List A)
    (hfront : (P 0).length ≤ R) (hback : (Q (Fin.last n)).length ≤ R)
    (halign : ∀ i : Fin n, Q i.castSucc = P i.succ) :
    EditDistortion.indel (List.ofFn P).flatten (List.ofFn Q).flatten ≤ 2 * R := by
  have hp : (List.ofFn P).flatten = P 0 ++ (List.ofFn (fun i : Fin n => P i.succ)).flatten := by
    rw [List.ofFn_succ, List.flatten_cons]
  have hq : (List.ofFn Q).flatten =
      (List.ofFn (fun i : Fin n => Q i.castSucc)).flatten ++ Q (Fin.last n) := by
    rw [List.ofFn_succ', List.concat_eq_append, List.flatten_append]
    simp
  rw [hp, hq]
  simp_rw [halign]
  let m := (List.ofFn (fun i : Fin n => P i.succ)).flatten
  have h₁ : EditDistortion.Script false (P 0).length (P 0 ++ m) m := by
    simpa using (EditDistortion.Script.to_nil (s := false) (P 0)).append_right m
  have h₂ : EditDistortion.Script false (Q (Fin.last n)).length m (m ++ Q (Fin.last n)) := by
    simpa using (EditDistortion.Script.to_nil (s := false) (Q (Fin.last n))).symm.append_left m
  exact (EditDistortion.cost_le (h₁.trans h₂)).trans (by omega)

lemma indel_row_shift {A : Type*} {L B : ℕ} (hL : 0 < L) (hB : 0 < B)
    (P Q : Fin L → Fin B → A)
    (halign : ∀ (i j : Fin L), j.val = i.val + 1 → Q i = P j) :
    EditDistortion.indel (rowWord P) (rowWord Q) ≤ 4 * B := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hL)
  rw [rowWord_flatten hB P, rowWord_flatten hB Q]
  have h := indel_shift_flatten (R := 2 * B)
    (fun i => (List.ofFn (P i)).map some ++ List.replicate B none)
    (fun i => (List.ofFn (Q i)).map some ++ List.replicate B none)
    (by simp; omega) (by simp; omega) (fun i => by rw [halign i.castSucc i.succ (by simp)])
  convert h using 1
  omega

end EditRows

end OAI
