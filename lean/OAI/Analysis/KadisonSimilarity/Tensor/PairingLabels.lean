import OAI.Analysis.KadisonSimilarity.Tensor.InvariantCycles

namespace OAI

/-!
# Disjoint labels for the pairing test

The cycle classes of one perfect matching index disjoint label pools. This
isolates that matching while allowing the labels of same-side pairs to vary.
-/

noncomputable section
namespace KadisonSimilarity

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A perfect matching represented by its fixed-point-free involution. -/
abbrev PerfectMatching (ι : Type*) :=
  {π : Equiv.Perm ι // Function.Involutive π ∧ ∀ i, π i ≠ i}

instance perfectMatchingFintype : Fintype (PerfectMatching ι) := Fintype.ofFinite _

omit [DecidableEq ι] in
/-- A cycle of a matching has exactly its two paired vertices. -/
theorem sameCycle_perfectMatching_iff (P : PerfectMatching ι) (i j : ι) :
    P.1.SameCycle i j ↔ j = i ∨ j = P.1 i := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        rcases ih with h | h
        · exact Or.inr (congrArg P.1 h)
        · exact Or.inl ((congrArg P.1 h).trans (P.2.1 i))
  · rintro (rfl | rfl)
    · exact Equiv.Perm.SameCycle.rfl
    · exact ⟨1, by simp⟩

/-- On orthonormal labels, a pairing contraction is the product of equality
indicators along its pairs. Repeating an indicator has no effect. -/
def pairingLabelKernel {J : Type*} [DecidableEq J]
    (P : PerfectMatching ι) (labels : ι → J) : ℂ :=
  ∏ i, if labels i = labels (P.1 i) then 1 else 0

/-- Labels identifying exactly the pairs of `P` kill every other matching. -/
theorem pairingLabelKernel_isolate {J : Type*} [DecidableEq J]
    (P Q : PerfectMatching ι) (labels : ι → J)
    (hlabels : ∀ i j, labels i = labels j ↔ j = i ∨ j = P.1 i) :
    pairingLabelKernel Q labels = if Q = P then 1 else 0 := by
  classical
  by_cases hQP : Q = P
  · subst Q
    simp only [pairingLabelKernel, ite_true]
    apply Finset.prod_eq_one
    intro i _
    exact ite_eq_left ((hlabels i (P.1 i)).mpr (Or.inr rfl))
  · have hex : ∃ i, Q.1 i ≠ P.1 i := by
      by_contra! h
      exact hQP (Subtype.ext (Equiv.ext h))
    obtain ⟨i, hi⟩ := hex
    have hne : labels i ≠ labels (Q.1 i) := by
      intro h
      rcases (hlabels i (Q.1 i)).mp h with h | h
      · exact Q.2.2 i h
      · exact hi h
    simp only [hQP, ↓reduceIte, pairingLabelKernel]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hne)

variable {k l : ℕ}

/-- A pair is entirely in the source precisely when its cycle contains no test slot. -/
def IsSourcePairClass (P : PerfectMatching (Fin k ⊕ Fin l))
    (q : PermutationCycles P.1) : Prop :=
  ∀ j : Fin l, (⟦Sum.inr j⟧ : PermutationCycles P.1) ≠ q

/-- A pair is entirely in the test precisely when its cycle contains no source slot. -/
def IsTestPairClass (P : PerfectMatching (Fin k ⊕ Fin l))
    (q : PermutationCycles P.1) : Prop :=
  ∀ i : Fin k, (⟦Sum.inl i⟧ : PermutationCycles P.1) ≠ q

abbrev SourcePairClasses (P : PerfectMatching (Fin k ⊕ Fin l)) :=
  {q : PermutationCycles P.1 // IsSourcePairClass P q}

abbrev TestPairClasses (P : PerfectMatching (Fin k ⊕ Fin l)) :=
  {q : PermutationCycles P.1 // IsTestPairClass P q}

instance sourcePairClassDecidable (P : PerfectMatching (Fin k ⊕ Fin l))
    (q : PermutationCycles P.1) : Decidable (IsSourcePairClass P q) := Classical.propDecidable _

instance testPairClassDecidable (P : PerfectMatching (Fin k ⊕ Fin l))
    (q : PermutationCycles P.1) : Decidable (IsTestPairClass P q) := Classical.propDecidable _

instance sourcePairClassesFintype (P : PerfectMatching (Fin k ⊕ Fin l)) :
    Fintype (SourcePairClasses P) := Fintype.ofFinite _

instance testPairClassesFintype (P : PerfectMatching (Fin k ⊕ Fin l)) :
    Fintype (TestPairClasses P) := Fintype.ofFinite _

/-- The source tuple uses a variable label on each source-source pair and a
fixed label on each source-test pair. The cycle class separates the pools. -/
def sourcePairLabels (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (f : SourcePairClasses P → Fin M) (i : Fin k) : PermutationCycles P.1 × ℕ :=
  let q : PermutationCycles P.1 := ⟦Sum.inl i⟧
  (q, if h : IsSourcePairClass P q then (f ⟨q, h⟩).val else 0)

/-- The analogous tuple on the test side. -/
def testPairLabels (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (g : TestPairClasses P → Fin M) (j : Fin l) : PermutationCycles P.1 × ℕ :=
  let q : PermutationCycles P.1 := ⟦Sum.inr j⟧
  (q, if h : IsTestPairClass P q then (g ⟨q, h⟩).val else 0)

theorem sourcePairLabels_injective (P : PerfectMatching (Fin k ⊕ Fin l)) (M : ℕ) :
    Function.Injective (sourcePairLabels P (M := M)) := by
  intro f g hfg
  funext q
  rcases q with ⟨q, hq⟩
  obtain ⟨s, hs⟩ := Quotient.exists_rep q
  cases s with
  | inr j => exact False.elim (hq j hs)
  | inl i =>
      subst q
      have h := congrArg (fun z => (z i).2) hfg
      apply Fin.ext
      simpa [sourcePairLabels, hq] using h

theorem testPairLabels_injective (P : PerfectMatching (Fin k ⊕ Fin l)) (M : ℕ) :
    Function.Injective (testPairLabels P (M := M)) := by
  intro f g hfg
  funext q
  rcases q with ⟨q, hq⟩
  obtain ⟨s, hs⟩ := Quotient.exists_rep q
  cases s with
  | inl i => exact False.elim (hq i hs)
  | inr j =>
      subst q
      have h := congrArg (fun z => (z j).2) hfg
      apply Fin.ext
      simpa [testPairLabels, hq] using h

private def allPairLabels (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (f : SourcePairClasses P → Fin M) (g : TestPairClasses P → Fin M)
    (s : Fin k ⊕ Fin l) : PermutationCycles P.1 × ℕ :=
  let q : PermutationCycles P.1 := ⟦s⟧
  (q, if h : IsSourcePairClass P q then (f ⟨q, h⟩).val
    else if h : IsTestPairClass P q then (g ⟨q, h⟩).val else 0)

private theorem allPairLabels_source (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (f : SourcePairClasses P → Fin M) (g : TestPairClasses P → Fin M) (i : Fin k) :
    allPairLabels P f g (Sum.inl i) = sourcePairLabels P f i := by
  have hn : ¬ IsTestPairClass P (⟦Sum.inl i⟧ : PermutationCycles P.1) := fun h => h i rfl
  simp only [allPairLabels, sourcePairLabels, hn, ↓reduceDIte]

private theorem allPairLabels_test (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (f : SourcePairClasses P → Fin M) (g : TestPairClasses P → Fin M) (j : Fin l) :
    allPairLabels P f g (Sum.inr j) = testPairLabels P g j := by
  have hn : ¬ IsSourcePairClass P (⟦Sum.inr j⟧ : PermutationCycles P.1) := fun h => h j rfl
  simp only [allPairLabels, testPairLabels, hn, ↓reduceDIte]

/-- The combined source and test tuples identify exactly the chosen pairs. -/
theorem pairLabels_eq_iff (P : PerfectMatching (Fin k ⊕ Fin l)) {M : ℕ}
    (f : SourcePairClasses P → Fin M) (g : TestPairClasses P → Fin M)
    (s t : Fin k ⊕ Fin l) :
    Sum.elim (sourcePairLabels P f) (testPairLabels P g) s =
        Sum.elim (sourcePairLabels P f) (testPairLabels P g) t ↔
      t = s ∨ t = P.1 s := by
  have heq (s : Fin k ⊕ Fin l) :
      Sum.elim (sourcePairLabels P f) (testPairLabels P g) s = allPairLabels P f g s := by
    cases s with
    | inl i => exact (allPairLabels_source P f g i).symm
    | inr j => exact (allPairLabels_test P f g j).symm
  rw [heq s, heq t, ← sameCycle_perfectMatching_iff P s t]
  constructor
  · intro h
    exact Quotient.exact (congrArg Prod.fst h)
  · intro h
    have he : (⟦s⟧ : PermutationCycles P.1) = ⟦t⟧ := Quotient.sound h
    simp only [allPairLabels, he]

/-- A source-source pair supplies a source-only cycle class. -/
theorem sourcePairClass_of_source_pair (P : PerfectMatching (Fin k ⊕ Fin l))
    (i i' : Fin k) (hp : P.1 (Sum.inl i) = Sum.inl i') :
    IsSourcePairClass P (⟦Sum.inl i⟧ : PermutationCycles P.1) := by
  intro j hq
  have hc := (sameCycle_perfectMatching_iff P (Sum.inl i) (Sum.inr j)).mp
    (Quotient.exact hq.symm)
  rcases hc with h | h <;> simp [hp] at h

/-- The analogous implication for a test-test pair. -/
theorem testPairClass_of_test_pair (P : PerfectMatching (Fin k ⊕ Fin l))
    (j j' : Fin l) (hp : P.1 (Sum.inr j) = Sum.inr j') :
    IsTestPairClass P (⟦Sum.inr j⟧ : PermutationCycles P.1) := by
  intro i hq
  have hc := (sameCycle_perfectMatching_iff P (Sum.inr j) (Sum.inl i)).mp
    (Quotient.exact hq.symm)
  rcases hc with h | h <;> simp [hp] at h

/-- If there are no same-side cycle classes, every pair crosses the two sides. -/
theorem isCrossPairing_of_no_same_side (P : PerfectMatching (Fin k ⊕ Fin l))
    (hS : Fintype.card (SourcePairClasses P) = 0)
    (hT : Fintype.card (TestPairClasses P) = 0) : IsCrossPairing P.1 := by
  have : IsEmpty (SourcePairClasses P) := Fintype.card_eq_zero_iff.mp hS
  have : IsEmpty (TestPairClasses P) := Fintype.card_eq_zero_iff.mp hT
  constructor
  · intro i
    cases hp : P.1 (Sum.inl i) with
    | inr j => exact ⟨j, rfl⟩
    | inl i' => exact isEmptyElim (⟨_, sourcePairClass_of_source_pair P i i' hp⟩ : SourcePairClasses P)
  · intro j
    cases hp : P.1 (Sum.inr j) with
    | inl i => exact ⟨i, rfl⟩
    | inr j' => exact isEmptyElim (⟨_, testPairClass_of_test_pair P j j' hp⟩ : TestPairClasses P)

end KadisonSimilarity

end

end OAI
