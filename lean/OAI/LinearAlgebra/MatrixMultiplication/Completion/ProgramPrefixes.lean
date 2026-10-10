import OAI.LinearAlgebra.MatrixMultiplication.Completion.Labels

namespace OAI

/-! Readable tensor completion and its finite arithmetic realization. -/

noncomputable section

namespace MatrixMultiplication.CompletionLabels.TopologicalFlatten

open MatrixMultiplication.Foundation RecursiveCompletion

universe u v w z

theorem labelRecordOf_eq_iff {A : Type u} {Label : ℕ → Type v}
    (labels : ∀ n, A → Label n) (n : ℕ) (a b : A) :
    labelRecordOf labels n a = labelRecordOf labels n b ↔
      ∀ k, k < n → labels k a = labels k b := by
  constructor
  · intro h k hk
    exact label_eq_of_record_eq labels h hk
  · intro h
    revert h
    induction n with
    | zero => intro h; rfl
    | succ n ih =>
        intro h
        apply Prod.ext
        · exact ih (fun k hk => h k (Nat.lt_succ_of_lt hk))
        · exact h n (Nat.lt_succ_self n)

namespace Program

variable {A : Type u} {Coord : Color → Type v}
  {Context OtherContext : Type z} {Code : Type w} {d e : ℕ}

theorem append_record_eq_iff
    (p : Program A Coord Context Code d) (q : Program A Coord OtherContext Code e)
    (sameView : ∀ side a, p.view side a = q.view side a)
    (derive : Context → (Fin d → Code) → OtherContext)
    (derive_correct : ∀ a, derive (p.context a) (fun j => p.labels j.val a) = q.context a)
    (k : ℕ) (a b : A) :
    labelRecordOf (p.append q sameView derive derive_correct).labels (d + k) a =
        labelRecordOf (p.append q sameView derive derive_correct).labels (d + k) b ↔
      labelRecordOf p.labels d a = labelRecordOf p.labels d b ∧
        labelRecordOf q.labels k a = labelRecordOf q.labels k b := by
  simp only [labelRecordOf_eq_iff]
  constructor
  · intro h
    constructor
    · intro n hn
      have heq := h n (by omega)
      simpa only [append_labels_left p q sameView derive derive_correct n hn] using heq
    · intro n hn
      have heq := h (d + n) (by omega)
      simpa only [append_labels_right] using heq
  · rintro ⟨hp, hq⟩ n hn
    by_cases hd : n < d
    · simpa only [append_labels_left p q sameView derive derive_correct n hd] using hp n hd
    · have hdn : d + (n - d) = n := Nat.add_sub_of_le (Nat.le_of_not_gt hd)
      have heq := hq (n - d) (by omega)
      have ha := append_labels_right p q sameView derive derive_correct (n - d) a
      have hb := append_labels_right p q sameView derive derive_correct (n - d) b
      rw [hdn] at ha hb
      exact ha.trans (heq.trans hb.symm)

theorem recode_record_eq_iff {NewCode : Type*}
    (p : Program A Coord Context Code d) (encode : Code → NewCode)
    (decode : NewCode → Code) (roundtrip : Function.LeftInverse decode encode)
    (k : ℕ) (a b : A) :
    labelRecordOf (p.recode encode decode roundtrip).labels k a =
        labelRecordOf (p.recode encode decode roundtrip).labels k b ↔
      labelRecordOf p.labels k a = labelRecordOf p.labels k b := by
  simp only [labelRecordOf_eq_iff]
  constructor
  · intro h n hn
    exact roundtrip.injective (h n hn)
  · intro h n hn
    exact congrArg encode (h n hn)

theorem pow_record_eq_iff [Inhabited Code]
    (p : Program A Coord Context Code d) (m : ℕ) (i : Fin m)
    (k : ℕ) (hk : k ≤ d) (a b : Fin m → A) :
    labelRecordOf (p.pow m).labels (i.val * d + k) a =
        labelRecordOf (p.pow m).labels (i.val * d + k) b ↔
      (∀ j : Fin m, j.val < i.val →
        labelRecordOf p.labels d (a j) = labelRecordOf p.labels d (b j)) ∧
      labelRecordOf p.labels k (a i) = labelRecordOf p.labels k (b i) := by
  simp only [labelRecordOf_eq_iff]
  constructor
  · intro h
    constructor
    · intro j hj n hn
      have hindex : j.val * d + n < i.val * d + k := by
        calc
          j.val * d + n < j.val * d + d := Nat.add_lt_add_left hn _
          _ = (j.val + 1) * d := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ i.val * d := Nat.mul_le_mul_right d (Nat.succ_le_of_lt hj)
          _ ≤ i.val * d + k := Nat.le_add_right _ _
      have heq := h (j.val * d + n) hindex
      simpa only [pow_labels p m a j n hn, pow_labels p m b j n hn] using heq
    · intro n hn
      have hnd : n < d := lt_of_lt_of_le hn hk
      have heq := h (i.val * d + n) (Nat.add_lt_add_left hn _)
      simpa only [pow_labels p m a i n hnd, pow_labels p m b i n hnd] using heq
  · rintro ⟨hp, hc⟩ n hn
    have hd : 0 < d := by
      by_contra h
      have hz : d = 0 := by omega
      simp [hz] at hk hn
      omega
    have hq : n / d ≤ i.val := by
      have hbound : n < (i.val + 1) * d := by
        rw [Nat.add_mul, Nat.one_mul]
        exact lt_of_lt_of_le hn (Nat.add_le_add_left hk _)
      exact Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd).2 hbound)
    let j : Fin m := ⟨n / d, lt_of_le_of_lt hq i.isLt⟩
    have hrem : n % d < d := Nat.mod_lt n hd
    have hsplit : j.val * d + n % d = n := by
      simpa only [j, Nat.mul_comm] using Nat.div_add_mod n d
    have heq : p.labels (n % d) (a j) = p.labels (n % d) (b j) := by
      by_cases hj : j.val < i.val
      · exact hp j hj (n % d) hrem
      · have hji : j = i := Fin.ext (by dsimp [j] at hj ⊢; omega)
        have hcur : n % d < k := by
          rw [hji] at hsplit
          omega
        simpa only [hji] using hc (n % d) hcur
    rw [← hsplit, pow_labels p m a j (n % d) hrem, pow_labels p m b j (n % d) hrem]
    exact heq

end Program
end MatrixMultiplication.CompletionLabels.TopologicalFlatten

namespace MatrixMultiplication.CompletionLabels

open MatrixMultiplication.Foundation RecursiveCompletion TopologicalFlatten

attribute [local instance] Classical.propDecidable Classical.decEq

universe uCoord
variable {X Y Z : Type uCoord}

theorem completionLocalProgram_label_root {Code : Type*} [Inhabited Code] {depth : ℕ}
    (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (n : ℕ) (hn : n < 3) (a : Leaf (complete S center m)) :
    (completionLocalProgram S center m p context_eq view_eq).labels n a =
      encodePattern (if leafColor (complete S center m) a = rootColor n then
        some (pattern S center m a) else none) := by
  change (if n < 3 then encodePattern ((patternProgram S center m).labels n a)
    else (inheritedProgram S center m p view_eq).labels (n - 3) a) = _
  rw [ite_eq_left hn]
  rfl

theorem completionLocalProgram_pair_root {Code : Type*} [Inhabited Code] {depth : ℕ}
    (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (n : ℕ) (hn : n < 3) :
    (completionLocalProgram S center m p context_eq view_eq).pair n =
      ownerPair center (rootColor n) := by
  change (if n < 3 then ownerPair center (rootColor n) else p.pair ((n - 3) % depth)) = _
  rw [ite_eq_left hn]

theorem completionLocalProgram_label_slot {Code : Type*} [Inhabited Code] {depth : ℕ}
    (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (i : Fin m) (k : ℕ) (hk : k < depth) (a : Leaf (complete S center m)) :
    (completionLocalProgram S center m p context_eq view_eq).labels (3 + (i.val * depth + k)) a =
      encodeOld (p.labels k (slot S center m a i)) := by
  change (if 3 + (i.val * depth + k) < 3 then
    encodePattern ((patternProgram S center m).labels (3 + (i.val * depth + k)) a)
    else (inheritedProgram S center m p view_eq).labels
      (3 + (i.val * depth + k) - 3) a) = _
  have hsub : 3 + (i.val * depth + k) - 3 = i.val * depth + k := by omega
  rw [ite_eq_right (by omega), hsub]
  change ((p.recode encodeOld decodeOld oldCode_roundtrip).pow m).labels
    (i.val * depth + k) (slot S center m a) = _
  rw [Program.pow_labels _ m _ i k hk]
  rfl

theorem completionLocalProgram_pair_slot {Code : Type*} [Inhabited Code] {depth : ℕ}
    (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (i : Fin m) (k : ℕ) (hk : k < depth) :
    (completionLocalProgram S center m p context_eq view_eq).pair (3 + (i.val * depth + k)) =
      p.pair k := by
  change (if 3 + (i.val * depth + k) < 3 then _
    else p.pair ((3 + (i.val * depth + k) - 3) % depth)) = _
  rw [ite_eq_right (by omega)]
  have hsub : 3 + (i.val * depth + k) - 3 = i.val * depth + k := by omega
  rw [hsub, Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hk]

theorem patternProgram_record_eq_iff (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (a b : Leaf (complete S center m)) :
    labelRecordOf (patternProgram S center m).labels 3 a =
        labelRecordOf (patternProgram S center m).labels 3 b ↔
      leafColor (complete S center m) a = leafColor (complete S center m) b ∧
        pattern S center m a = pattern S center m b := by
  constructor
  · intro h
    have heq := label_eq_of_record_eq (patternProgram S center m).labels h
      (rootIndex (leafColor (complete S center m) a)).isLt
    change (if leafColor (complete S center m) a =
        rootColor (rootIndex (leafColor (complete S center m) a)).val
      then some (pattern S center m a) else none) =
      (if leafColor (complete S center m) b =
        rootColor (rootIndex (leafColor (complete S center m) a)).val
      then some (pattern S center m b) else none) at heq
    rw [rootColor_rootIndex, ite_eq_left rfl] at heq
    by_cases hb : leafColor (complete S center m) b = leafColor (complete S center m) a
    · rw [ite_eq_left hb] at heq
      exact ⟨hb.symm, Option.some.inj heq⟩
    · rw [ite_eq_right hb] at heq
      cases heq
  · rintro ⟨hc, hp⟩
    apply (labelRecordOf_eq_iff _ _ _ _).mpr
    intro n hn
    change (if leafColor (complete S center m) a = rootColor n then
      some (pattern S center m a) else none) =
      (if leafColor (complete S center m) b = rootColor n then
      some (pattern S center m b) else none)
    rw [hc, hp]

theorem completionProgram_record_eq_iff {Code : Type*} [Inhabited Code] {depth : ℕ}
    (S : FlaggedTensor X Y Z) (center : Color) (m : ℕ)
    (p : Program (Leaf S) (Coordinate X Y Z) Color Code depth)
    (context_eq : ∀ a, p.context a = leafColor S a)
    (view_eq : ∀ side a, p.view side a = coordinate a.val side)
    (i : Fin m) (k : ℕ) (hk : k ≤ depth)
    (a b : Leaf (complete S center m)) :
    labelRecordOf (completionLocalProgram S center m p context_eq view_eq).labels
        (3 + (i.val * depth + k)) a =
      labelRecordOf (completionLocalProgram S center m p context_eq view_eq).labels
        (3 + (i.val * depth + k)) b ↔
      (leafColor (complete S center m) a = leafColor (complete S center m) b ∧
        pattern S center m a = pattern S center m b) ∧
      ((∀ j : Fin m, j.val < i.val →
        labelRecordOf p.labels depth (slot S center m a j) =
          labelRecordOf p.labels depth (slot S center m b j)) ∧
        labelRecordOf p.labels k (slot S center m a i) =
          labelRecordOf p.labels k (slot S center m b i)) := by
  change labelRecordOf (completionProgram S center m p context_eq view_eq).labels
      (3 + (i.val * depth + k)) a =
    labelRecordOf (completionProgram S center m p context_eq view_eq).labels
      (3 + (i.val * depth + k)) b ↔ _
  trans
    (labelRecordOf ((patternProgram S center m).recode (encodePattern (Code := Code))
        decodePatternCode patternCode_roundtrip).labels 3 a =
      labelRecordOf ((patternProgram S center m).recode (encodePattern (Code := Code))
        decodePatternCode patternCode_roundtrip).labels 3 b ∧
      labelRecordOf (inheritedProgram S center m p view_eq).labels (i.val * depth + k) a =
        labelRecordOf (inheritedProgram S center m p view_eq).labels (i.val * depth + k) b)
  · exact Program.append_record_eq_iff _ _ _ _ _ (i.val * depth + k) a b
  rw [Program.recode_record_eq_iff, patternProgram_record_eq_iff]
  have htail :
      (labelRecordOf (inheritedProgram S center m p view_eq).labels (i.val * depth + k) a =
        labelRecordOf (inheritedProgram S center m p view_eq).labels (i.val * depth + k) b) ↔
      (labelRecordOf ((p.recode (encodeOld (m := m)) decodeOld oldCode_roundtrip).pow m).labels
        (i.val * depth + k) (slot S center m a) =
        labelRecordOf ((p.recode (encodeOld (m := m)) decodeOld oldCode_roundtrip).pow m).labels
          (i.val * depth + k) (slot S center m b)) := by
    simp only [labelRecordOf_eq_iff]
    rfl
  rw [htail, Program.pow_record_eq_iff _ m i k hk]
  simp only [Program.recode_record_eq_iff]

end MatrixMultiplication.CompletionLabels

end

end OAI
