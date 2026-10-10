import OAI.Combinatorics.ContingencyTables.Sampling.GreedyPublicProgram

namespace OAI

/-! # The public matrix encoding uniquely identifies a fixed-shape table -/

namespace ContingencyTables.Algorithms
open MatchingFPRAS MatchingFPRAS.LiteralParse Turing

lemma encodeMatrix_flat {m n : ℕ} (X : Fin m → Fin n → ℕ) :
    encodeMatrix X=((List.ofFn fun i => List.ofFn (X i)).flatten).flatMap encodeNat := by
  rw [←GreedyFeasibleTable.printMatrix_ofFn]
  simp only [GreedyFeasibleTable.printMatrix,List.flatten_eq_flatMap,List.flatMap_assoc,id_eq]

lemma matrix_flat_injective (m n : ℕ) (X Y : Fin m → Fin n → ℕ)
    (h : (List.ofFn (fun i => List.ofFn (X i))).flatten=
      (List.ofFn (fun i => List.ofFn (Y i))).flatten) : X=Y := by
  have hr : List.ofFn (fun i => List.ofFn (X i))=List.ofFn (fun i => List.ofFn (Y i)) :=
    List.eq_iff_flatten_eq.mpr ⟨h,by
      simp only [List.map_ofFn]
      congr 1
      funext i
      exact (List.length_ofFn).trans (List.length_ofFn.symm)⟩
  have hf := List.ofFn_injective hr
  funext i
  exact List.ofFn_injective (congrFun hf i)

lemma encodeMatrix_injective {m n : ℕ} :
    Function.Injective (encodeMatrix (m := m) (n := n)) := by
  intro X Y h
  have hp := congrArg parse h
  rw [encodeMatrix_flat,encodeMatrix_flat,GreedyFeasibleTable.parse_natWords,
    GreedyFeasibleTable.parse_natWords] at hp
  exact matrix_flat_injective m n X Y hp

lemma parse_blank_extension (as : List Symbol) (n : ℕ) :
    parse (as++List.replicate n (0:Symbol))=parse as := by
  have hz : (List.replicate n (0:Symbol)).foldr (fun a ns => numStep (a,ns)) []=[] := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.replicate_succ,List.foldr_cons,ih]
      rfl
  unfold parse
  rw [List.foldr_append,hz]

/-- Parsing natural-number fields is unchanged by trailing tape blanks. -/
def blankNumbers (tape : ListBlank Symbol) : List ℕ :=
  tape.liftOn parse (by
    rintro as _ ⟨n,rfl⟩
    exact (parse_blank_extension as n).symm)

lemma blankMatrix_injective {m n : ℕ} (X Y : Fin m → Fin n → ℕ)
    (h : ListBlank.mk (encodeMatrix X)=ListBlank.mk (encodeMatrix Y)) : X=Y := by
  have hp := congrArg blankNumbers h
  change parse (encodeMatrix X)=parse (encodeMatrix Y) at hp
  rw [encodeMatrix_flat,encodeMatrix_flat,GreedyFeasibleTable.parse_natWords,
    GreedyFeasibleTable.parse_natWords] at hp
  exact matrix_flat_injective m n X Y hp

end ContingencyTables.Algorithms

end OAI
