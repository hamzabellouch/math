import OAI.Combinatorics.ParityLifts.BinaryArithmetic

namespace OAI

namespace ParityWL.Complexity

def chunkWidth (t : ℕ) (F : BitFormula) : ℕ := (F.length+t-1)/t

def bitGroup (t : ℕ) (F : BitFormula) (i : Fin t) : BitFormula :=
  (F.drop (i.val*chunkWidth t F)).take (chunkWidth t F)

lemma length_le_width_mul (t m : ℕ) (ht : 0<t) : m≤((m+t-1)/t)*t := by
  have hmod := Nat.mod_lt (m+t-1) ht
  have hdiv := Nat.div_add_mod (m+t-1) t
  rw [Nat.mul_comm t] at hdiv
  omega

lemma bitGroup_subset (t : ℕ) (F : BitFormula) (i : Fin t) : bitGroup t F i ⊆ F :=
  List.Subset.trans (List.take_subset _ _) (List.drop_subset _ _)

lemma mem_bitGroup_cover (t : ℕ) (ht : 0<t) (F : BitFormula) (C : BitClause) (hC : C∈F) :
    ∃ i, C∈bitGroup t F i := by
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hC
  let q := chunkWidth t F
  have hm : F.length≤q*t := length_le_width_mul t F.length ht
  have hq : 0<q := by nlinarith [j.isLt]
  have hjt : j.val/q<t := (Nat.div_lt_iff_lt_mul hq).mpr (by simpa only [Nat.mul_comm] using j.isLt.trans_le hm)
  let i : Fin t := ⟨j.val/q,hjt⟩
  have hrem := Nat.mod_lt j.val hq
  have hind : i.val*q+j.val%q=j.val := by
    dsimp [i]
    have h := Nat.div_add_mod j.val q
    simpa only [Nat.mul_comm q] using h
  have hget : (bitGroup t F i)[j.val%q]? = some C := by
    unfold bitGroup
    rw [List.getElem?_take, ite_eq_left hrem, List.getElem?_drop, hind]
    rw [List.getElem?_eq_getElem j.isLt]
    exact congrArg some hj
  exact ⟨i, List.mem_of_getElem? hget⟩

lemma bitGroup_sat (t : ℕ) (ht : 0<t) (F : BitFormula) (a : Name → Bool) :
    (∀ i, bitSat a (bitGroup t F i)) ↔ bitSat a F := by
  constructor
  · intro h C hC
    obtain ⟨i,hi⟩ := mem_bitGroup_cover t ht F C hC
    exact h i C hi
  · intro h i C hC
    exact h C (bitGroup_subset t F i hC)

lemma names_length_le (F : BitFormula) (hw : ∀ C∈F, C.length≤3) :
    (names F).length≤3*F.length := by
  induction F with
  | nil => simp [names]
  | cons C F ih =>
    have hc := hw C (by simp)
    have hh := ih (fun D hD => hw D (by simp [hD]))
    simp only [names,List.flatMap_cons,List.length_append,List.length_map,List.length_cons] at *
    omega

lemma group_names_length (t : ℕ) (F : BitFormula) (hw : ∀ C∈F, C.length≤3) (i : Fin t) :
    (names (bitGroup t F i)).length≤3*chunkWidth t F := by
  apply (names_length_le _ (fun C hC => hw C (bitGroup_subset t F i hC))).trans
  apply Nat.mul_le_mul_left
  exact List.length_take_le ..

noncomputable def PolyProgram.chunkWidth (t : ℕ) (ht : 0<t) :
    PolyProgram BitFormula ℕ (Complexity.chunkWidth t) :=
  (PolyProgram.length BitClause).comp (PolyProgram.width t ht)

noncomputable def PolyProgram.bitGroup (t : ℕ) (ht : 0<t) :
    PolyProgram (Fin t × BitFormula) BitFormula (fun x => Complexity.bitGroup t x.2 x.1) := by
  let I := (PolyProgram.fst (Fin t) BitFormula).comp (PolyProgram.finite (fun i : Fin t => i.val))
  let F := PolyProgram.snd (Fin t) BitFormula
  let q := F.comp (PolyProgram.chunkWidth t ht)
  let n := (I.pair q).comp PolyProgram.natMul
  exact (q.pair ((n.pair F).comp (PolyProgram.drop BitClause))).comp (PolyProgram.take BitClause)

noncomputable def PolyProgram.bitGroups (t : ℕ) (ht : 0<t) :
    PolyProgram BitFormula (Fin t → BitFormula) (Complexity.bitGroup t) :=
  (PolyProgram.bitGroup t ht).tabulate

end ParityWL.Complexity

end OAI
