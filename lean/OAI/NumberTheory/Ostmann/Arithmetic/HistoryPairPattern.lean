import OAI.NumberTheory.Ostmann.Arithmetic.HistoryRepeatedRenamingPattern

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistoryPairPattern
open Construction HistoryOccurrenceVariables HistoryRepeatedRenaming HistorySymbolicScope
open Characters.RationalHistory

def PairKey {l : ℕ} (h k : History l) :=
  {j : Bool ⊕ (ℕ × ℤ) // j ∈
    Finset.univ.image (patternKey h) ∪ Finset.univ.image (patternKey k)}

instance pairKeyDecidableEq {l : ℕ} (h k : History l) : DecidableEq (PairKey h k) :=
  inferInstanceAs (DecidableEq {j : Bool ⊕ (ℕ × ℤ) // j ∈
    Finset.univ.image (patternKey h) ∪ Finset.univ.image (patternKey k)})

instance pairKeyFintype {l : ℕ} (h k : History l) : Fintype (PairKey h k) :=
  inferInstanceAs (Fintype {j : Bool ⊕ (ℕ × ℤ) // j ∈
    Finset.univ.image (patternKey h) ∪ Finset.univ.image (patternKey k)})

def leftEmbedding {l : ℕ} (h k : History l) : PatternKey h ↪ PairKey h k where
  toFun j := ⟨j.val,Finset.mem_union_left _ j.property⟩
  inj' := by
    intro i j he
    apply Subtype.ext
    exact congrArg (fun z : PairKey h k => z.val) he

def rightEmbedding {l : ℕ} (h k : History l) : PatternKey k ↪ PairKey h k where
  toFun j := ⟨j.val,Finset.mem_union_right _ j.property⟩
  inj' := by
    intro i j he
    apply Subtype.ext
    exact congrArg (fun z : PairKey h k => z.val) he

def leftMap {l : ℕ} (h k : History l) (i : Key h) : PairKey h k :=
  leftEmbedding h k (patternMap h i)

def rightMap {l : ℕ} (h k : History l) (i : Key k) : PairKey h k :=
  rightEmbedding h k (patternMap k i)

def unionMap {l : ℕ} (h k : History l) : Key h ⊕ Key k → PairKey h k :=
  Sum.elim (leftMap h k) (rightMap h k)

theorem unionMap_surjective {l : ℕ} (h k : History l) : Function.Surjective (unionMap h k) := by
  intro j
  rcases Finset.mem_union.mp j.property with hj | hj
  · obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp hj
    exact ⟨Sum.inl i,Subtype.ext hij⟩
  · obtain ⟨i,hi,hij⟩ := Finset.mem_image.mp hj
    exact ⟨Sum.inr i,Subtype.ext hij⟩

def pairSample {l : ℕ} (h k : History l) (j : PairKey h k) : ℤ := patternSample h j.val

def pairRationalSample {l : ℕ} (h k : History l) (j : PairKey h k) : ℚ := pairSample h k j

def pairLevel {l : ℕ} (h k : History l) (j : PairKey h k) : ℕ := patternLevel l j.val

@[simp] theorem leftMap_sample {l : ℕ} (h k : History l) (i : Key h) :
    pairSample h k (leftMap h k i) = integerSample h i := patternKey_sample h i

def RootGiantsAgree {l : ℕ} (h k : History l) : Prop :=
  h.root.giantPlus=k.root.giantPlus ∧ h.root.giantMinus=k.root.giantMinus

theorem RootGiantsAgree.of_root_eq {l : ℕ} {h k : History l} (hh : h.root=k.root) :
    RootGiantsAgree h k :=
  ⟨congrArg State.giantPlus hh,congrArg State.giantMinus hh⟩

@[simp] theorem rightMap_sample {l : ℕ} (h k : History l) (hroot : RootGiantsAgree h k) (i : Key k) :
    pairSample h k (rightMap h k i) = integerSample k i := by
  rcases i with b | i
  · cases b
    · exact congrArg (fun n : ℕ => (n : ℤ)) hroot.1
    · exact congrArg (fun n : ℕ => (n : ℤ)) hroot.2
  · rfl

@[simp] theorem leftEmbedding_sample {l : ℕ} (h k : History l) (i : PatternKey h) :
    pairSample h k (leftEmbedding h k i) = patternSample h i.val := rfl

@[simp] theorem rightEmbedding_sample {l : ℕ} (h k : History l) (hroot : RootGiantsAgree h k)
    (i : PatternKey k) : pairSample h k (rightEmbedding h k i) = patternSample k i.val := by
  obtain ⟨j,rfl⟩ := patternMap_surjective k i
  exact (rightMap_sample h k hroot j).trans (patternMap_sample k j).symm

@[simp] theorem leftMap_level {l : ℕ} (h k : History l) (i : Key h) :
    pairLevel h k (leftMap h k i) = keyLevel h i := patternKey_level h i

@[simp] theorem rightMap_level {l : ℕ} (h k : History l) (i : Key k) :
    pairLevel h k (rightMap h k i) = keyLevel k i := patternKey_level k i

@[simp] theorem leftEmbedding_level {l : ℕ} (h k : History l) (i : PatternKey h) :
    pairLevel h k (leftEmbedding h k i) = patternLevel l i.val := rfl

@[simp] theorem rightEmbedding_level {l : ℕ} (h k : History l) (i : PatternKey k) :
    pairLevel h k (rightEmbedding h k i) = patternLevel l i.val := rfl

theorem shared_giant {l : ℕ} (h k : History l) (b : Bool) :
    leftMap h k (Sum.inl b) = rightMap h k (Sum.inl b) := rfl

theorem cross_small_eq_iff {l : ℕ} (h k : History l)
    (i : Fin h.root.small.length ⊕ InternalKey h) (j : Fin k.root.small.length ⊕ InternalKey k) :
    leftMap h k (Sum.inr i) = rightMap h k (Sum.inr j) ↔
      keyLevel h (Sum.inr i) = keyLevel k (Sum.inr j) ∧
      integerSample h (Sum.inr i) = integerSample k (Sum.inr j) := by
  change (⟨patternKey h (Sum.inr i),_⟩ : PairKey h k) = ⟨patternKey k (Sum.inr j),_⟩ ↔ _
  simp only [Subtype.ext_iff,patternKey,Sum.inr.injEq,Prod.mk.injEq]

theorem left_giant_ne_right_small {l : ℕ} (h k : History l) (b : Bool)
    (j : Fin k.root.small.length ⊕ InternalKey k) :
    leftMap h k (Sum.inl b) ≠ rightMap h k (Sum.inr j) := by
  intro he
  have hh := congrArg Subtype.val he
  cases hh

theorem leftSmall_ne_right_giant {l : ℕ} (h k : History l) (b : Bool)
    (i : Fin h.root.small.length ⊕ InternalKey h) :
    leftMap h k (Sum.inr i) ≠ rightMap h k (Sum.inl b) := by
  intro he
  have hh := congrArg Subtype.val he
  cases hh

theorem leftEmbedding_injective {l : ℕ} (h k : History l) :
    Function.Injective (leftEmbedding h k) := (leftEmbedding h k).injective

theorem rightEmbedding_injective {l : ℕ} (h k : History l) :
    Function.Injective (rightEmbedding h k) := (rightEmbedding h k).injective

theorem leftMap_sample_comp {l : ℕ} (h k : History l) :
    pairSample h k ∘ leftMap h k = integerSample h := by
  funext i
  exact leftMap_sample h k i

theorem rightMap_sample_comp {l : ℕ} (h k : History l) (hroot : RootGiantsAgree h k) :
    pairSample h k ∘ rightMap h k = integerSample k := by
  funext i
  exact rightMap_sample h k hroot i

theorem leftMap_rational_comp {l : ℕ} (h k : History l) :
    pairRationalSample h k ∘ leftMap h k = rationalSample h := by
  funext i
  exact congrArg (fun z : ℤ => (z : ℚ)) (leftMap_sample h k i)

theorem rightMap_rational_comp {l : ℕ} (h k : History l) (hroot : RootGiantsAgree h k) :
    pairRationalSample h k ∘ rightMap h k = rationalSample k := by
  funext i
  exact congrArg (fun z : ℤ => (z : ℚ)) (rightMap_sample h k hroot i)

theorem leftMap_cast_comp {R : Type*} [Ring R] {l : ℕ} (h k : History l) :
    (fun j => (pairSample h k j : R)) ∘ leftMap h k = fun i => (integerSample h i : R) := by
  funext i
  exact congrArg (fun z : ℤ => (z : R)) (leftMap_sample h k i)

theorem rightMap_cast_comp {R : Type*} [Ring R] {l : ℕ} (h k : History l)
    (hroot : RootGiantsAgree h k) :
    (fun j => (pairSample h k j : R)) ∘ rightMap h k = fun i => (integerSample k i : R) := by
  funext i
  exact congrArg (fun z : ℤ => (z : R)) (rightMap_sample h k hroot i)

theorem left_integerEval {l : ℕ} (h k : History l) (e : Expr (Key h)) :
    (e.rename (leftMap h k)).integerEval (pairSample h k) = e.integerEval (integerSample h) := by
  rw [Expr.integerEval_rename,leftMap_sample_comp]

theorem right_integerEval {l : ℕ} (h k : History l) (hroot : RootGiantsAgree h k) (e : Expr (Key k)) :
    (e.rename (rightMap h k)).integerEval (pairSample h k) = e.integerEval (integerSample k) := by
  rw [Expr.integerEval_rename,rightMap_sample_comp h k hroot]

theorem left_rationalEval {l : ℕ} (h k : History l) (e : Expr (Key h)) :
    (e.rename (leftMap h k)).rationalEval (pairRationalSample h k) = e.rationalEval (rationalSample h) := by
  rw [Expr.rationalEval_rename,leftMap_rational_comp]

theorem right_rationalEval {l : ℕ} (h k : History l) (hroot : RootGiantsAgree h k) (e : Expr (Key k)) :
    (e.rename (rightMap h k)).rationalEval (pairRationalSample h k) = e.rationalEval (rationalSample k) := by
  rw [Expr.rationalEval_rename,rightMap_rational_comp h k hroot]

theorem left_fieldEval {K : Type*} [Field K] {l : ℕ} (h k : History l) (e : Expr (Key h)) :
    (e.rename (leftMap h k)).fieldEval (fun j => (pairSample h k j : K)) =
      e.fieldEval (fun i => (integerSample h i : K)) := by
  rw [Expr.fieldEval_rename,leftMap_cast_comp]

theorem right_fieldEval {K : Type*} [Field K] {l : ℕ} (h k : History l)
    (hroot : RootGiantsAgree h k) (e : Expr (Key k)) :
    (e.rename (rightMap h k)).fieldEval (fun j => (pairSample h k j : K)) =
      e.fieldEval (fun i => (integerSample k i : K)) := by
  rw [Expr.fieldEval_rename,rightMap_cast_comp h k hroot]

theorem left_regularAt {l : ℕ} (h k : History l) (e : Expr (Key h)) :
    (e.rename (leftMap h k)).RegularAt (pairRationalSample h k) ↔ e.RegularAt (rationalSample h) := by
  rw [Expr.regularAt_rename,leftMap_rational_comp]

theorem right_regularAt {l : ℕ} (h k : History l) (hroot : RootGiantsAgree h k) (e : Expr (Key k)) :
    (e.rename (rightMap h k)).RegularAt (pairRationalSample h k) ↔ e.RegularAt (rationalSample k) := by
  rw [Expr.regularAt_rename,rightMap_rational_comp h k hroot]

theorem left_fieldRegularAt {K : Type*} [Field K] {l : ℕ} (h k : History l) (e : Expr (Key h)) :
    (e.rename (leftMap h k)).FieldRegularAt (fun j => (pairSample h k j : K)) ↔
      e.FieldRegularAt (fun i => (integerSample h i : K)) := by
  rw [Expr.fieldRegularAt_rename,leftMap_cast_comp]

theorem right_fieldRegularAt {K : Type*} [Field K] {l : ℕ} (h k : History l)
    (hroot : RootGiantsAgree h k) (e : Expr (Key k)) :
    (e.rename (rightMap h k)).FieldRegularAt (fun j => (pairSample h k j : K)) ↔
      e.FieldRegularAt (fun i => (integerSample k i : K)) := by
  rw [Expr.fieldRegularAt_rename,rightMap_cast_comp h k hroot]

theorem left_above {l : ℕ} (h k : History l) (e : Expr (Key h)) (t : ℕ) :
    Above (pairLevel h k) t (e.rename (leftMap h k)) ↔ Above (keyLevel h) t e :=
  above_rename e (leftMap h k) (keyLevel h) (pairLevel h k) (leftMap_level h k) t

theorem right_above {l : ℕ} (h k : History l) (e : Expr (Key k)) (t : ℕ) :
    Above (pairLevel h k) t (e.rename (rightMap h k)) ↔ Above (keyLevel k) t e :=
  above_rename e (rightMap h k) (keyLevel k) (pairLevel h k) (rightMap_level h k) t

theorem leftEmbedding_above {l : ℕ} (h k : History l) (e : Expr (PatternKey h)) (t : ℕ) :
    Above (pairLevel h k) t (e.rename (leftEmbedding h k)) ↔
      Above (fun j : PatternKey h => patternLevel l j.val) t e :=
  above_rename e (leftEmbedding h k) _ _ (leftEmbedding_level h k) t

theorem rightEmbedding_above {l : ℕ} (h k : History l) (e : Expr (PatternKey k)) (t : ℕ) :
    Above (pairLevel h k) t (e.rename (rightEmbedding h k)) ↔
      Above (fun j : PatternKey k => patternLevel l j.val) t e :=
  above_rename e (rightEmbedding h k) _ _ (rightEmbedding_level h k) t

end Ostmann.Arithmetic.HistoryPairPattern

end

end OAI
