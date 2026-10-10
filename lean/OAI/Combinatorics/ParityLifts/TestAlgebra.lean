import OAI.Combinatorics.ParityLifts.Rerooting

namespace OAI

namespace ParityWL

open scoped BigOperators

section AtomicTests

open scoped Classical

variable {k t : ℕ}

def EqRootRel (i j a b : Fin k) : Prop := a = i ∧ b = j

def EqRoot (i j : Fin k) := Quot (EqRootRel i j)

noncomputable instance eqRootFintype (i j : Fin k) : Fintype (EqRoot i j) :=
  Fintype.ofSurjective (Quot.mk (EqRootRel i j))
    (fun q => Quot.inductionOn q (fun a => ⟨a, rfl⟩))

noncomputable def equalityTest (hkt : k ≤ t) (i j : Fin k) : RootedTest k t := by
  letI : Fintype (Quot (EqRootRel i j)) := eqRootFintype i j
  exact singleBagTest (A := EqRoot i j) (fun _ _ : EqRoot i j => False) ⟨fun _ _ h => h⟩
    (Quot.mk (EqRootRel i j)) (fun q => Quot.inductionOn q (fun a => ⟨a, rfl⟩))
    ((Fintype.card_le_of_surjective (fun a : Fin k => (Quot.mk (EqRootRel i j) a : EqRoot i j))
      (fun q => Quot.inductionOn q (fun a => ⟨a, rfl⟩))).trans (by simpa using hkt))

lemma equalityTest_count (hkt : k ≤ t) (i j : Fin k) {V : Type} [Fintype V]
    (G : SimpleGraph V) (x : Fin k → V) :
    (equalityTest hkt i j).count G x = if x i = x j then 1 else 0 := by
  by_cases h : x i = x j
  · rw [ite_eq_left h]
    let f : (equalityTest hkt i j).Maps G x :=
      ⟨⟨Quot.lift x (by rintro a b ⟨rfl, rfl⟩; exact h), fun _ _ h => h.elim⟩,
        fun _ => rfl⟩
    have : Unique ((equalityTest hkt i j).Maps G x) :=
      { default := f
        uniq := by
          intro g
          apply Subtype.ext
          apply Subtype.ext
          funext q
          induction q using Quot.inductionOn with
          | h a => exact g.2 a }
    simp only [RootedTest.count, Fintype.card_unique, Nat.cast_one]
  · rw [ite_eq_right h]
    have : IsEmpty ((equalityTest hkt i j).Maps G x) := ⟨by
      intro g
      apply h
      rw [← g.2 i, ← g.2 j]
      apply congrArg g.1.1
      exact Quot.sound ⟨rfl, rfl⟩⟩
    simp only [RootedTest.count, Fintype.card_eq_zero, Nat.cast_zero]

noncomputable def edgeTest (hkt : k ≤ t) (i j : Fin k) : RootedTest k t :=
  singleBagTest (fun a b : Fin k => (a = i ∧ b = j) ∨ (a = j ∧ b = i))
    ⟨by rintro a b (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        <;> simp only [true_and, true_or, or_true]⟩
    id Function.surjective_id (by simpa using hkt)

lemma edgeTest_count (hkt : k ≤ t) (i j : Fin k) {V : Type} [Fintype V]
    (G : SimpleGraph V) (x : Fin k → V) :
    (edgeTest hkt i j).count G x = if G.Adj (x i) (x j) then 1 else 0 := by
  by_cases h : G.Adj (x i) (x j)
  · rw [ite_eq_left h]
    let f : (edgeTest hkt i j).Maps G x := ⟨⟨x, by
      intro a b hab
      change (a = i ∧ b = j) ∨ (a = j ∧ b = i) at hab
      rcases hab with ⟨hai, hbj⟩ | ⟨haj, hbi⟩
      · rw [hai, hbj]; exact h
      · rw [haj, hbi]; exact h.symm⟩, fun _ => rfl⟩
    have : Unique ((edgeTest hkt i j).Maps G x) :=
      { default := f
        uniq := by
          intro g
          apply Subtype.ext
          apply Subtype.ext
          funext a
          exact g.2 a }
    simp only [RootedTest.count, Fintype.card_unique, Nat.cast_one]
  · rw [ite_eq_right h]
    have : IsEmpty ((edgeTest hkt i j).Maps G x) := ⟨by
      intro g
      apply h
      rw [← g.2 i, ← g.2 j]
      exact g.1.2 i j (.inl ⟨rfl, rfl⟩)⟩
    simp only [RootedTest.count, Fintype.card_eq_zero, Nat.cast_zero]

end AtomicTests

section TestAlgebra

open scoped Classical

abbrev TuplePair (V W : Type) (k : ℕ) := (Fin k → V) ⊕ (Fin k → W)

variable {V W : Type} [Fintype V] [Fintype W] (G : SimpleGraph V) (H : SimpleGraph W)

noncomputable def testEval {k t : ℕ} (F : RootedTest k t) : TuplePair V W k → ℚ :=
  Sum.elim (F.count G) (F.count H)

noncomputable def testSpan (k t : ℕ) : Submodule ℚ (TuplePair V W k → ℚ) :=
  Submodule.span ℚ (Set.range (fun F : RootedTest k t => testEval G H F))

lemma testEval_mem {k t : ℕ} (F : RootedTest k t) : testEval G H F ∈ testSpan G H k t :=
  Submodule.subset_span ⟨F, rfl⟩

lemma testSpan_one {k t : ℕ} (hkt : k ≤ t) : (1 : TuplePair V W k → ℚ) ∈ testSpan G H k t := by
  have he : testEval G H (isolatedTest k t hkt) = 1 := by
    funext a
    cases a with
    | inl x => exact isolatedTest_count k t hkt G x
    | inr x => exact isolatedTest_count k t hkt H x
  rw [← he]
  exact testEval_mem _ _ _

lemma testEval_mul_mem {k t : ℕ} (hkt : k ≤ t) (F L : RootedTest k t) :
    testEval G H F * testEval G H L ∈ testSpan G H k t := by
  let Fs : Fin 2 → RootedTest k t := ![F, L]
  let P := glueTest Fs (fun _ => id) hkt
  have he : testEval G H P = testEval G H F * testEval G H L := by
    funext a
    cases a with
    | inl x =>
      change P.count G x = F.count G x * L.count G x
      simp only [P, glueTest_count, Fin.prod_univ_two, Fs, Matrix.cons_val_zero,
        Matrix.cons_val_one, Function.comp_id]
    | inr x =>
      change P.count H x = F.count H x * L.count H x
      simp only [P, glueTest_count, Fin.prod_univ_two, Fs, Matrix.cons_val_zero,
        Matrix.cons_val_one, Function.comp_id]
  rw [← he]
  exact testEval_mem _ _ _

lemma testSpan_mul {k t : ℕ} (hkt : k ≤ t) {f g : TuplePair V W k → ℚ}
    (hf : f ∈ testSpan G H k t) (hg : g ∈ testSpan G H k t) : f * g ∈ testSpan G H k t := by
  refine Submodule.span_induction₂ (p := fun f g _ _ => f * g ∈ testSpan G H k t)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hf hg
  · rintro _ _ ⟨F, rfl⟩ ⟨L, rfl⟩
    exact testEval_mul_mem G H hkt F L
  · intro _ _
    simpa only [zero_mul] using (testSpan G H k t).zero_mem
  · intro _ _
    simpa only [mul_zero] using (testSpan G H k t).zero_mem
  · intro f g h _ _ _ hf hg
    simpa only [add_mul] using (testSpan G H k t).add_mem hf hg
  · intro f g h _ _ _ hf hg
    simpa only [mul_add] using (testSpan G H k t).add_mem hf hg
  · intro a f g _ _ hf
    simpa only [smul_mul_assoc] using (testSpan G H k t).smul_mem a hf
  · intro a f g _ _ hf
    simpa only [mul_smul_comm] using (testSpan G H k t).smul_mem a hf

noncomputable def testAlgebra (k t : ℕ) (hkt : k ≤ t) : Subalgebra ℚ (TuplePair V W k → ℚ) where
  carrier := testSpan G H k t
  mul_mem' := testSpan_mul G H hkt
  one_mem' := testSpan_one G H hkt
  add_mem' := (testSpan G H k t).add_mem
  zero_mem' := (testSpan G H k t).zero_mem
  algebraMap_mem' a := by
    rw [Algebra.algebraMap_eq_smul_one]
    exact (testSpan G H k t).smul_mem a (testSpan_one G H hkt)

end TestAlgebra

section TestOperations

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

def tupleReindex {k m : ℕ} (φ : Fin k → Fin m) : TuplePair V W m → TuplePair V W k :=
  Sum.map (fun x => x ∘ φ) (fun x => x ∘ φ)

noncomputable def reindexLinear {k m : ℕ} (φ : Fin k → Fin m) :
    (TuplePair V W k → ℚ) →ₗ[ℚ] (TuplePair V W m → ℚ) where
  toFun f := f ∘ tupleReindex φ
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

lemma testSpan_reindex {k m t : ℕ} (hm : m ≤ t) (φ : Fin k → Fin m)
    {f : TuplePair V W k → ℚ} (hf : f ∈ testSpan G H k t) :
    reindexLinear φ f ∈ testSpan G H m t := by
  have h : testSpan G H k t ≤ (testSpan G H m t).comap (reindexLinear φ) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨F, rfl⟩
    let P := glueTest (fun _ : Unit => F) (fun _ => φ) hm
    have he : reindexLinear φ (testEval G H F) = testEval G H P := by
      funext a
      cases a with
      | inl x =>
        change F.count G (x ∘ φ) = P.count G x
        simp only [P, glueTest_count, Fintype.prod_unique]
      | inr x =>
        change F.count H (x ∘ φ) = P.count H x
        simp only [P, glueTest_count, Fintype.prod_unique]
    change reindexLinear φ (testEval G H F) ∈ testSpan G H m t
    rw [he]
    exact testEval_mem _ _ _
  exact h hf

noncomputable def sumInsertLinear {k : ℕ} (i : Fin (k + 1)) :
    (TuplePair V W (k + 1) → ℚ) →ₗ[ℚ] (TuplePair V W k → ℚ) where
  toFun f := Sum.elim (fun x => ∑ y : V, f (.inl (i.insertNth y x)))
    (fun x => ∑ y : W, f (.inr (i.insertNth y x)))
  map_add' f g := by
    funext a
    cases a <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' a f := by
    funext x
    cases x <;> simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, Finset.smul_sum,
      RingHom.id_apply]

lemma testSpan_sumInsert {k t : ℕ} (hk : k < t) (i : Fin (k + 1))
    {f : TuplePair V W (k + 1) → ℚ} (hf : f ∈ testSpan G H (k + 1) t) :
    sumInsertLinear i f ∈ testSpan G H k t := by
  have h : testSpan G H (k + 1) t ≤ (testSpan G H k t).comap (sumInsertLinear i) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨F, rfl⟩
    have he : sumInsertLinear i (testEval G H F) = testEval G H (reRootTest F i.succAbove hk) := by
      funext a
      cases a with
      | inl x => exact (reRootTest_count F i hk G x).symm
      | inr x => exact (reRootTest_count F i hk H x).symm
    change sumInsertLinear i (testEval G H F) ∈ testSpan G H k t
    rw [he]
    exact testEval_mem _ _ _
  exact h hf

end TestOperations

end ParityWL

end OAI
