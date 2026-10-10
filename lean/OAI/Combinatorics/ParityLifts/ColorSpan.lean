import OAI.Combinatorics.ParityLifts.Interpolation

namespace OAI

namespace ParityWL

open scoped BigOperators

section ColorSpan

open scoped Classical

variable {V W : Type} [Fintype V] [Fintype W]
variable (G : SimpleGraph V) (H : SimpleGraph W)

noncomputable def pairAtomic {k : ℕ} : TuplePair V W k → AtomicType k :=
  Sum.elim (atomicType G) (atomicType H)

noncomputable def pairJoint (k r : ℕ) : TuplePair V W k → JointColor k r :=
  Sum.elim (jointColor G k r) (jointColor H k r)

noncomputable def pairSeparate (k r : ℕ) : TuplePair V W k → SeparateColor k r :=
  Sum.elim (separateColor G k r) (separateColor H k r)

def boolIndicator (b : Bool) : ℚ := if b then 1 else 0

lemma boolIndicator_injective : Function.Injective boolIndicator := by
  intro a b h
  cases a <;> cases b <;> simp_all [boolIndicator]

lemma testEval_equality {k t : ℕ} (hkt : k ≤ t) (i j : Fin k) (a : TuplePair V W k) :
    testEval G H (equalityTest hkt i j) a = boolIndicator ((pairAtomic G H a i j).1) := by
  cases a <;> simp [testEval, equalityTest_count, pairAtomic, atomicType, boolIndicator]

lemma testEval_edge {k t : ℕ} (hkt : k ≤ t) (i j : Fin k) (a : TuplePair V W k) :
    testEval G H (edgeTest hkt i j) a = boolIndicator ((pairAtomic G H a i j).2) := by
  cases a <;> simp [testEval, edgeTest_count, pairAtomic, atomicType, boolIndicator]

lemma atomic_indicator_mem {k t : ℕ} (hkt : k ≤ t) (d : AtomicType k) :
    (fun x => if pairAtomic G H x = d then (1 : ℚ) else 0) ∈ testSpan G H k t := by
  refine color_indicator_mem_of_separation (testAlgebra G H k t hkt) (pairAtomic G H) ?_ d
  intro x y hxy
  by_contra! hn
  apply hxy
  funext i j
  apply Prod.ext
  · apply boolIndicator_injective
    rw [← testEval_equality G H hkt i j x, ← testEval_equality G H hkt i j y]
    apply hn _ (testEval_mem G H _)
    intro z w hzw
    rw [testEval_equality, testEval_equality, hzw]
  · apply boolIndicator_injective
    rw [← testEval_edge G H hkt i j x, ← testEval_edge G H hkt i j y]
    apply hn _ (testEval_mem G H _)
    intro z w hzw
    rw [testEval_edge, testEval_edge, hzw]

lemma joint_indicator_sum {k r : ℕ} (d : Fin k → JointColor k r) (a : TuplePair V W k) :
    jointReplacementSum (fun i x => if pairJoint G H k r x = d i then (1 : ℚ) else 0) a =
      (Multiset.count d (pairJoint G H k (r + 1) a).2 : ℚ) := by
  have hprod {D : Type} [DecidableEq D] (c d : Fin k → D) :
      (∏ i : Fin k, if c i = d i then (1 : ℚ) else 0) = if c = d then 1 else 0 := by
    rw [Finset.prod_boole]
    simp only [Finset.mem_univ, true_implies, funext_iff]
  cases a with
  | inl x =>
    change (∑ y : V, ∏ i : Fin k,
      if jointColor G k r (Function.update x i y) = d i then (1 : ℚ) else 0) = _
    change _ = (Multiset.count d (Finset.univ.val.map
      (fun y : V => fun i => jointColor G k r (Function.update x i y))) : ℚ)
    rw [count_map_as_sum]
    apply Finset.sum_congr rfl
    intro y _
    exact hprod _ _
  | inr x =>
    change (∑ y : W, ∏ i : Fin k,
      if jointColor H k r (Function.update x i y) = d i then (1 : ℚ) else 0) = _
    change _ = (Multiset.count d (Finset.univ.val.map
      (fun y : W => fun i => jointColor H k r (Function.update x i y))) : ℚ)
    rw [count_map_as_sum]
    apply Finset.sum_congr rfl
    intro y _
    exact hprod _ _

lemma separate_indicator_sum {k r : ℕ} (i : Fin k) (d : SeparateColor k r)
    (a : TuplePair V W k) :
    replacementSum i (fun x => if pairSeparate G H k r x = d then (1 : ℚ) else 0) a =
      (Multiset.count d ((pairSeparate G H k (r + 1) a).2 i) : ℚ) := by
  cases a with
  | inl x => exact (count_map_as_sum _ _).symm
  | inr x => exact (count_map_as_sum _ _).symm

lemma pairJoint_zero {k : ℕ} (a : TuplePair V W k) :
    pairJoint G H k 0 a = pairAtomic G H a := by
  cases a <;> rfl

lemma pairSeparate_zero {k : ℕ} (a : TuplePair V W k) :
    pairSeparate G H k 0 a = pairAtomic G H a := by
  cases a <;> rfl

lemma pairJoint_fst {k r : ℕ} (a : TuplePair V W k) :
    (pairJoint G H k (r + 1) a).1 = pairJoint G H k r a := by
  cases a <;> rfl

lemma pairSeparate_fst {k r : ℕ} (a : TuplePair V W k) :
    (pairSeparate G H k (r + 1) a).1 = pairSeparate G H k r a := by
  cases a <;> rfl

lemma joint_indicator_mem {k t : ℕ} (hkt : k + 1 ≤ t) (r : ℕ) (d : JointColor k r) :
    (fun x => if pairJoint G H k r x = d then (1 : ℚ) else 0) ∈ testSpan G H k t := by
  induction r with
  | zero =>
    convert atomic_indicator_mem G H (k := k) (t := t) (by omega) d using 1
    funext x
    split_ifs <;> simp_all [pairJoint_zero]
    contradiction
  | succ r ih =>
    refine color_indicator_mem_of_separation (testAlgebra G H k t (by omega))
      (pairJoint G H k (r+1)) ?_ d
    intro x y hxy
    by_contra! hn
    apply hxy
    apply Prod.ext
    · rw [pairJoint_fst, pairJoint_fst]
      have hf := ih (pairJoint G H k r x)
      have he := hn _ hf (by
        intro z w hzw
        have hz : pairJoint G H k r z = pairJoint G H k r w := by
          simpa only [pairJoint_fst, pairSeparate_fst] using congrArg Prod.fst hzw
        rw [hz])
      by_contra hne
      simp only [ite_eq_right (Ne.symm hne), ite_true, one_ne_zero] at he
    · apply Multiset.ext.mpr
      intro e
      have hf := testSpan_jointReplacementSum G H hkt (fun i => ih (e i))
      have he := hn _ hf (by
        intro z w hzw
        rw [joint_indicator_sum, joint_indicator_sum, hzw])
      rw [joint_indicator_sum, joint_indicator_sum] at he
      exact_mod_cast he

lemma separate_indicator_mem {k t : ℕ} (hkt : k ≤ t) (r : ℕ) (d : SeparateColor k r) :
    (fun x => if pairSeparate G H k r x = d then (1 : ℚ) else 0) ∈ testSpan G H k t := by
  induction r with
  | zero =>
    convert atomic_indicator_mem G H hkt d using 1
    funext x
    split_ifs <;> simp_all [pairSeparate_zero]
    contradiction
  | succ r ih =>
    refine color_indicator_mem_of_separation (testAlgebra G H k t hkt)
      (pairSeparate G H k (r+1)) ?_ d
    intro x y hxy
    by_contra! hn
    apply hxy
    apply Prod.ext
    · rw [pairSeparate_fst, pairSeparate_fst]
      have hf := ih (pairSeparate G H k r x)
      have he := hn _ hf (by
        intro z w hzw
        have hz : pairSeparate G H k r z = pairSeparate G H k r w := by
          simpa only [pairJoint_fst, pairSeparate_fst] using congrArg Prod.fst hzw
        rw [hz])
      by_contra hne
      simp only [ite_eq_right (Ne.symm hne), ite_true, one_ne_zero] at he
    · funext i
      apply Multiset.ext.mpr
      intro e
      have hf := testSpan_replacementSum G H hkt i (ih e)
      have he := hn _ hf (by
        intro z w hzw
        rw [separate_indicator_sum, separate_indicator_sum, hzw])
      rw [separate_indicator_sum, separate_indicator_sum] at he
      exact_mod_cast he

end ColorSpan

section SpanHistograms

open scoped Classical

variable {V W X Y D : Type} [Fintype V] [Fintype W] [Fintype X] [Fintype Y]
variable (G : SimpleGraph V) (H : SimpleGraph W) {k t : ℕ}
variable (l : X → TuplePair V W k) (r : Y → TuplePair V W k)

lemma sum_eq_of_mem_testSpan
    (hF : ∀ F : RootedTest k t, ∑ x, testEval G H F (l x) = ∑ y, testEval G H F (r y))
    {f : TuplePair V W k → ℚ} (hf : f ∈ testSpan G H k t) :
    ∑ x, f (l x) = ∑ y, f (r y) := by
  refine Submodule.span_induction (p := fun f _ => ∑ x, f (l x) = ∑ y, f (r y))
    ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨F, rfl⟩
    exact hF F
  · simp only [Pi.zero_apply, Finset.sum_const_zero]
  · intro f g _ _ ihf ihg
    simp only [Pi.add_apply, Finset.sum_add_distrib, ihf, ihg]
  · intro a f _ ih
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum, ih]

lemma histograms_eq_of_tests [DecidableEq D] (c : TuplePair V W k → D)
    (hc : ∀ d, (fun x => if c x = d then (1 : ℚ) else 0) ∈ testSpan G H k t)
    (hF : ∀ F : RootedTest k t, ∑ x, testEval G H F (l x) = ∑ y, testEval G H F (r y)) :
    Finset.univ.val.map (c ∘ l) = Finset.univ.val.map (c ∘ r) := by
  apply Multiset.ext.mpr
  intro d
  have he := sum_eq_of_mem_testSpan G H l r hF (hc d)
  apply Nat.cast_injective (R := ℚ)
  rw [count_map_as_sum, count_map_as_sum]
  exact he

end SpanHistograms

theorem no_choice_equivalent (k : ℕ) (hk : 4 ≤ k) (c : Convention)
    (C : ChoiceSystem (bagParameter c k)) (hn : ¬ C.Successful) :
    WLEquivalent (zeroLift C) (starLift C) c k := by
  classical
  intro r
  cases c with
  | joint =>
    exact histograms_eq_of_tests (zeroLift C) (starLift C) Sum.inl Sum.inr
      (pairJoint (zeroLift C) (starLift C) k r)
      (joint_indicator_mem _ _ (t := k+1) le_rfl r)
      (fun F => no_choice_equal_rooted_total F C (by omega) hn)
  | separate =>
    exact histograms_eq_of_tests (zeroLift C) (starLift C) Sum.inl Sum.inr
      (pairSeparate (zeroLift C) (starLift C) k r)
      (separate_indicator_mem _ _ (t := k) le_rfl r)
      (fun F => no_choice_equal_rooted_total F C (by omega) hn)

end ParityWL

end OAI
