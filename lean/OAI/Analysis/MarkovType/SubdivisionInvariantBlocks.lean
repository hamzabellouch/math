import OAI.Analysis.MarkovType.SubdivisionLimit
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

namespace Subdivision

theorem blockVector_eq_ofList {l r : ℕ} (left : Fin l → ℝ) (right : Fin r → ℝ)
    (J : ℕ) (c : ℝ) :
    blockVector left right J c =
      ofList (List.ofFn left ++ (List.replicate J (c / (J : ℝ)) ++ List.ofFn right)) := by
  rw [blockVector, ← ofList_ofFn]
  simp only [blockArray, List.ofFn_fin_append, List.ofFn_const]

theorem pieces_append (a b : List (ℝ × ℕ)) : pieces (a ++ b) = pieces a ++ pieces b := by
  simp only [pieces, List.flatMap_append]

theorem pieces_unit (a : List ℝ) : pieces (a.map fun c => (c, 1)) = a := by
  induction a with
  | nil => rfl
  | cons c a ih =>
      simp only [List.map_cons, pieces_cons, Nat.cast_one, div_one,
        List.replicate_one, List.singleton_append, ih]

end Subdivision

namespace SpreadingModel

open Subdivision

variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem averaged_pieces (S : SpreadingModel Y) (blocks : List (ℝ × ℕ))
    (hpos : ∀ b ∈ blocks, 0 < b.2) :
    S.averagedSeminorm (ofList (pieces blocks)) =
      S.averagedSeminorm (ofList (blocks.map Prod.fst)) := by
  induction blocks using List.ofFnRec with
  | h m blocks =>
      let J : ℕ → ℕ := fun i => if h : i < m then (blocks ⟨i, h⟩).2 else 1
      have hJ (i : ℕ) : 0 < J i := by
        dsimp [J]
        split_ifs with hi
        · apply hpos
          exact List.mem_ofFn.mpr ⟨⟨i, hi⟩, rfl⟩
        · exact Nat.one_pos
      have hJval (i : Fin m) : J i.val = (blocks i).2 := by
        simp only [J, dite_eq_left i.isLt]
      have h := S.averaged_subdivide J hJ (C00.ofArray fun i => (blocks i).1)
      rw [C00.subdivide_ofArray_eq_finiteSubdivision] at h
      simpa only [finiteSubdivision, hJval, List.map_ofFn, Function.comp_def,
        ofList_ofFn] using h

theorem averaged_block (S : SpreadingModel Y) (left right : List ℝ)
    (J : ℕ) (hJ : 0 < J) (c : ℝ) :
    S.averagedSeminorm (ofList (left ++ (List.replicate J (c / (J : ℝ)) ++ right))) =
      S.averagedSeminorm (ofList (left ++ ([c] ++ right))) := by
  let blocks := (left.map fun a => (a, 1)) ++ (c, J) :: (right.map fun a => (a, 1))
  have hp : ∀ b ∈ blocks, 0 < b.2 := by
    intro b hb
    dsimp only [blocks] at hb
    rcases List.mem_append.mp hb with hb | hb
    · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
      exact Nat.one_pos
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact hJ
      · obtain ⟨a, _, rfl⟩ := List.mem_map.mp hb
        exact Nat.one_pos
  have h := S.averaged_pieces blocks hp
  simpa only [blocks, pieces_append, pieces_unit, pieces_cons, List.map_append,
    List.map_cons, List.map_map, Function.comp_def, List.map_id, List.map_id',
    List.singleton_append] using h

theorem averaged_insert_zero (S : SpreadingModel Y) (left right : List ℝ) :
    S.averagedSeminorm (ofList (left ++ ([0] ++ right))) =
      S.averagedSeminorm (ofList (left ++ right)) := by
  induction left using List.ofFnRec with
  | h l left =>
      induction right using List.ofFnRec with
      | h r right =>
          have hs : sample left right 0 0 (0 : Fin 1) = blockVector left right 1 0 := by
            rw [sample_eq, blockVector_eq]
            simp
          have h := sample_norm S.averagedSeminorm S.averaged_spreading
            left right 0 0 (0 : Fin 1)
          rw [hs] at h
          simpa only [blockVector_eq_ofList, zero_div, List.replicate_one,
            List.replicate_zero, List.nil_append] using h

theorem averaged_split_positive_nats (S : SpreadingModel Y) (left right : List ℝ)
    {j k : ℕ} (hj : 0 < j) (hk : 0 < k) (s : ℝ) :
    S.averagedSeminorm
        (ofList (left ++ ([(j : ℝ) / ((j + k : ℕ) : ℝ) * s,
          (k : ℝ) / ((j + k : ℕ) : ℝ) * s] ++ right))) =
      S.averagedSeminorm (ofList (left ++ ([s] ++ right))) := by
  let a : ℝ := (j : ℝ) / ((j + k : ℕ) : ℝ) * s
  let b : ℝ := (k : ℝ) / ((j + k : ℕ) : ℝ) * s
  have hjr : (j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hj)
  have hkr : (k : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  have haj : a / (j : ℝ) = s / ((j + k : ℕ) : ℝ) := by
    dsimp [a]
    field_simp
  have hbk : b / (k : ℝ) = s / ((j + k : ℕ) : ℝ) := by
    dsimp [b]
    field_simp
  change S.averagedSeminorm (ofList (left ++ ([a, b] ++ right))) = _
  calc
    _ = S.averagedSeminorm
        (ofList (left ++ (List.replicate j (a / (j : ℝ)) ++ ([b] ++ right)))) := by
      exact (S.averaged_block left ([b] ++ right) j hj a).symm
    _ = S.averagedSeminorm
        (ofList (left ++ (List.replicate j (a / (j : ℝ)) ++
          (List.replicate k (b / (k : ℝ)) ++ right)))) := by
      simpa only [List.append_assoc] using
        (S.averaged_block (left ++ List.replicate j (a / (j : ℝ))) right k hk b).symm
    _ = S.averagedSeminorm
        (ofList (left ++ (List.replicate (j + k) (s / ((j + k : ℕ) : ℝ)) ++ right))) := by
      simp only [haj, hbk, List.replicate_add, List.append_assoc]
    _ = _ := S.averaged_block left right (j + k) (by omega) s

theorem averaged_split_natFraction (S : SpreadingModel Y) (left right : List ℝ)
    {n j : ℕ} (hn : 0 < n) (hjn : j ≤ n) (s : ℝ) :
    S.averagedSeminorm
        (ofList (left ++ ([(j : ℝ) / (n : ℝ) * s,
          (1 - (j : ℝ) / (n : ℝ)) * s] ++ right))) =
      S.averagedSeminorm (ofList (left ++ ([s] ++ right))) := by
  have hnr : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  by_cases hj0 : j = 0
  · subst j
    simpa using S.averaged_insert_zero left ([s] ++ right)
  by_cases hjn' : j = n
  · subst j
    simpa only [div_self hnr, one_mul, sub_self, zero_mul, List.append_assoc,
      List.cons_append, List.nil_append] using S.averaged_insert_zero (left ++ [s]) right
  have hj : 0 < j := Nat.pos_of_ne_zero hj0
  have hk : 0 < n - j := by omega
  have he : j + (n - j) = n := by omega
  have h := S.averaged_split_positive_nats left right hj hk s
  rw [he] at h
  have heq : ((n - j : ℕ) : ℝ) / (n : ℝ) * s =
      (1 - (j : ℝ) / (n : ℝ)) * s := by
    rw [Nat.cast_sub hjn]
    field_simp
  rwa [heq] at h

end SpreadingModel

end MarkovSuperreflexivity

end

end OAI
