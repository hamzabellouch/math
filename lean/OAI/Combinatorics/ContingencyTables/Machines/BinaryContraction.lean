import OAI.Combinatorics.ContingencyTables.Transport.QuadraticTransport
import OAI.Combinatorics.MatroidCounting.CommonBases

namespace OAI

/-!
# Fixed-degree binary cubic contraction

The full-matrix cubic contraction in paper 200-02,
Lemma `lem:binary-contraction`, follows from the generic spectral theorem
`CommonBasesFPRAS.cubic_signature` and its closed-limit lemma. A symmetric
cubic tensor is positive on distinct triples and zero on repetitions;
its coordinate slices have the quadratic signature; contraction by an
arbitrary nonnegative vector, in particular a pair indicator, preserves
that signature on the full remaining index set.

There is no assumption of positivity on unrelated subset cardinalities.
-/

namespace ContingencyTables.BinaryContraction

open scoped BigOperators Topology Classical
open LinearMap (BilinForm)
open CommonBasesFPRAS

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [Fintype I] [DecidableEq I] in
/-- Our signature convention and the existing library convention agree
for symmetric forms; only the orthogonality argument order differs. -/
lemma signature_iff (B : BilinForm ℝ (I → ℝ)) (hsymm : B.IsSymm) :
    OnePositiveDirection B ↔ CommonBasesFPRAS.OnePositive B := by
  constructor
  · intro h e he v hv
    exact h e he v (by rw [hsymm.eq e v]; exact hv)
  · intro h e he v hv
    exact h e he v (by rw [hsymm.eq v e]; exact hv)

lemma exists_third (hcard : 3 ≤ Fintype.card I) (j k : I) :
    ∃ i : I, i ≠ j ∧ i ≠ k := by
  by_contra hn
  have hsub : (Finset.univ : Finset I) ⊆ {j, k} := by
    intro i _
    by_cases hij : i = j
    · simp [hij]
    · have hik : i = k := by
        by_contra hik
        exact hn ⟨i, hij, hik⟩
      simp [hik]
  have hc := Finset.card_le_card hsub
  have hpair : ({j, k} : Finset I).card ≤ 2 := by
    by_cases h : j = k <;> simp [h]
  simp only [Finset.card_univ] at hc
  omega

omit [Fintype I] in
/-- Every tensor entry is nonnegative on the actual cubic domain. -/
lemma tensor_nonnegative (C : I → Matrix I I ℝ)
    (hzero : ∀ i j k, i = j ∨ i = k ∨ j = k → C i j k = 0)
    (hpos : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → 0 < C i j k)
    (i j k : I) : 0 ≤ C i j k := by
  by_cases hr : i = j ∨ i = k ∨ j = k
  · rw [hzero i j k hr]
  · exact (hpos i j k (fun h => hr (Or.inl h))
      (fun h => hr (Or.inr (Or.inl h))) (fun h => hr (Or.inr (Or.inr h)))).le

/-- Strictly positive directions give positive slice squares, including
when the ground set has exactly three elements. -/
lemma slice_square_positive (C : I → Matrix I I ℝ) (hcard : 3 ≤ Fintype.card I)
    (hzero : ∀ i j k, i = j ∨ i = k ∨ j = k → C i j k = 0)
    (hpos : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → 0 < C i j k)
    (x : I → ℝ) (hx : ∀ i, 0 < x i) (i : I) :
    0 < (C i).toBilin' x x := by
  obtain ⟨j, hji⟩ := Fintype.exists_ne_of_one_lt_card (by omega) i
  obtain ⟨k, hki, hkj⟩ := exists_third hcard i j
  rw [Matrix.toBilin'_apply]
  apply Finset.sum_pos'
  · intro a _
    apply Finset.sum_nonneg
    intro b _
    exact mul_nonneg (mul_nonneg (hx a).le (tensor_nonnegative C hzero hpos i a b)) (hx b).le
  · refine ⟨j, Finset.mem_univ _, ?_⟩
    apply Finset.sum_pos'
    · intro b _
      exact mul_nonneg (mul_nonneg (hx j).le (tensor_nonnegative C hzero hpos i j b)) (hx b).le
    · exact ⟨k, Finset.mem_univ _,
        mul_pos (mul_pos (hx j) (hpos i j k (Ne.symm hji) (Ne.symm hki) (Ne.symm hkj))) (hx k)⟩

/-- Strict-direction specialization of the existing generic spectral
argument, with every positivity condition proved from distinct triples. -/
theorem positive_cubic_contraction (C : I → Matrix I I ℝ)
    (hcard : 3 ≤ Fintype.card I)
    (hCs : ∀ i j k, C i j k = C i k j)
    (hCt : ∀ i j k, C i j k = C j i k)
    (hzero : ∀ i j k, i = j ∨ i = k ∨ j = k → C i j k = 0)
    (hpos : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → 0 < C i j k)
    (hsig : ∀ i, OnePositiveDirection (C i).toBilin')
    (x : I → ℝ) (hx : ∀ i, 0 < x i) :
    CommonBasesFPRAS.OnePositive (cubicContraction C x).toBilin' := by
  have : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  apply cubic_signature C hCs hCt
    (fun i => (signature_iff _ (matrix_bilin_symm _ (hCs i))).mp (hsig i)) x hx
  · exact slice_square_positive C hcard hzero hpos x hx
  · intro j k
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hx i).le (tensor_nonnegative C hzero hpos i j k)
  · intro j k hjk
    obtain ⟨i, hij, hik⟩ := exists_third hcard j k
    apply Finset.sum_pos'
    · intro a _
      exact mul_nonneg (hx a).le (tensor_nonnegative C hzero hpos a j k)
    · exact ⟨i, Finset.mem_univ _, mul_pos (hx i) (hpos i j k hij hik hjk)⟩

/-- Nonnegative contractions follow by the actual positive perturbation
and closed matrix limit from the paper. The contracted indices are retained. -/
theorem nonnegative_cubic_contraction (C : I → Matrix I I ℝ)
    (hcard : 3 ≤ Fintype.card I)
    (hCs : ∀ i j k, C i j k = C i k j)
    (hCt : ∀ i j k, C i j k = C j i k)
    (hzero : ∀ i j k, i = j ∨ i = k ∨ j = k → C i j k = 0)
    (hpos : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → 0 < C i j k)
    (hsig : ∀ i, OnePositiveDirection (C i).toBilin')
    (x : I → ℝ) (hx : ∀ i, 0 ≤ x i) :
    OnePositiveDirection (cubicContraction C x).toBilin' := by
  let F : ℝ → Matrix I I ℝ := fun t => cubicContraction C (fun i => x i + t)
  let l := nhdsWithin (0 : ℝ) (Set.Ioi 0)
  have : l.NeBot := nhdsWithin_Ioi_neBot (le_refl (0 : ℝ))
  have hF : CommonBasesFPRAS.OnePositive (F 0).toBilin' := by
    apply onePositive_of_tendsto (l := l) F (F 0)
    · intro i j
      have hc : Continuous (fun t => F t i j) := by
        dsimp [F, cubicContraction]
        apply continuous_finsetSum
        intro k _
        exact (continuous_const.add continuous_id).mul continuous_const
      exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    · intro t
      exact cubicContraction_symm C hCs _
    · have ht : ∀ᶠ t in l, 0 < t := self_mem_nhdsWithin
      filter_upwards [ht] with t ht
      exact positive_cubic_contraction C hcard hCs hCt hzero hpos hsig _
        (fun i => add_pos_of_nonneg_of_pos (hx i) ht)
  apply (signature_iff _ (matrix_bilin_symm _ (cubicContraction_symm C hCs x))).mpr
  simpa only [F, add_zero] using hF

/-- The pair-indicator contraction in Lemma binary-contraction is the sum
of the two coordinate slices on the full ground set. No principal restriction
has been taken yet. -/
theorem pair_cubic_contraction (C : I → Matrix I I ℝ)
    (hcard : 3 ≤ Fintype.card I)
    (hCs : ∀ i j k, C i j k = C i k j)
    (hCt : ∀ i j k, C i j k = C j i k)
    (hzero : ∀ i j k, i = j ∨ i = k ∨ j = k → C i j k = 0)
    (hpos : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → 0 < C i j k)
    (hsig : ∀ i, OnePositiveDirection (C i).toBilin') (p q : I) :
    OnePositiveDirection (C p + C q).toBilin' := by
  let x : I → ℝ := fun i => (if i = p then 1 else 0) + (if i = q then 1 else 0)
  have hx : ∀ i, 0 ≤ x i := by
    intro i
    dsimp [x]
    split_ifs <;> norm_num
  have heq : cubicContraction C x = C p + C q := by
    ext i j
    simp only [cubicContraction, x, add_mul, Finset.sum_add_distrib,
      ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
      Matrix.add_apply]
  rw [← heq]
  exact nonnegative_cubic_contraction C hcard hCs hCt hzero hpos hsig x hx


/-- Positivity is required only on the paper's valid subset degree. -/
def DegreePositive (f : Set I → ℝ) (k : ℕ) : Prop :=
  ∀ A, A.ncard = k → 0 < f A

/-- The paper's addition property: fix precisely `k-2` elements and test
only the remaining quadratic matrix. -/
def AdditionProperty (f : Set I → ℝ) (k : ℕ) : Prop :=
  ∀ A, A.ncard + 2 = k → CommonBasesFPRAS.OnePositive (faceHessian f A).toBilin'

/-- A coordinate slice of a valid-degree cubic tensor is a padded addition
matrix of the original weight. -/
lemma fixedDegree_slice (f : Set I → ℝ) (k : ℕ)
    (hsig : AdditionProperty f k) (A : Set I) (hA : A.ncard + 3 = k)
    (i : {i // i ∉ A}) : CommonBasesFPRAS.OnePositive (faceCubic f A i).toBilin' := by
  classical
  rw [faceCubic_pad]
  apply onePositive_padMatrix
  apply onePositive_reindex
  have hi : (insert i.val A).ncard + 2 = k := by
    rw [ncard_insert_eq A i.val i.property]
    omega
  convert hsig (insert i.val A) hi using 1
  congr 2 <;> exact Subsingleton.elim _ _

/-- The full-ground pair contraction for a weight positive only at its
specified subset degree. This is the actual cubic tensor used by the paper. -/
theorem fixedDegree_pair_contraction (f : Set I → ℝ) (k : ℕ)
    (hk : k ≤ Fintype.card I) (hpos : DegreePositive f k)
    (hsig : AdditionProperty f k) (A : Set I) (hA : A.ncard + 3 = k)
    (p q : {i // i ∉ A}) :
    OnePositiveDirection (faceCubic f A p + faceCubic f A q).toBilin' := by
  classical
  have hcard : 3 ≤ Fintype.card {i // i ∉ A} := by
    have := card_outside A
    omega
  apply pair_cubic_contraction (faceCubic f A) hcard
    (faceCubic_symm f A) (faceCubic_transpose f A)
  · intro i j l hr
    simp only [faceCubic, hr, ite_true]
  · intro i j l hij hil hjl
    simp only [faceCubic, hij, hil, hjl, false_or, ite_false]
    apply hpos
    rw [ncard_insert_union_pair A i j l hij hil hjl]
    exact hA
  · intro i
    apply (signature_iff _ (matrix_bilin_symm _ (faceCubic_symm f A i))).mpr
    exact fixedDegree_slice f k hsig A hA i

abbrev PairRest (p q : I) := {i : I // i ≠ p ∧ i ≠ q}

/-- Summing a labeled pair at occupancy one, on its actual remaining ground set. -/
noncomputable def pairSum (f : Set I → ℝ) (p q : I) (U : Set (PairRest p q)) : ℝ :=
  f (insert p (Subtype.val '' U)) + f (insert q (Subtype.val '' U))

/-- Every valid residual weight is the sum of two strictly positive weights. -/
lemma pairSum_positive (f : Set I → ℝ) (k : ℕ) (hpos : DegreePositive f k)
    (p q : I) (U : Set (PairRest p q)) (hU : U.ncard + 1 = k) :
    0 < pairSum f p q U := by
  classical
  have hp : p ∉ Subtype.val '' U := by
    rintro ⟨i, _, hi⟩
    exact i.property.1 hi
  have hq : q ∉ Subtype.val '' U := by
    rintro ⟨i, _, hi⟩
    exact i.property.2 hi
  have hc : (Subtype.val '' U).ncard = U.ncard :=
    Set.ncard_image_of_injective U Subtype.val_injective
  apply add_pos
  · apply hpos
    rw [ncard_insert_eq _ p hp, hc]
    exact hU
  · apply hpos
    rw [ncard_insert_eq _ q hq, hc]
    exact hU

/-- Occupancy-one pair summation preserves the valid-degree addition property.
The proof contracts on the full index set first and then takes the exact
principal submatrix after removing the pair. -/
theorem pairSum_addition (f : Set I → ℝ) (k : ℕ)
    (hk : k ≤ Fintype.card I) (hpos : DegreePositive f k)
    (hsig : AdditionProperty f k) (p q : I) :
    AdditionProperty (pairSum f p q) (k - 1) := by
  classical
  intro A hA
  let B : Set I := Subtype.val '' A
  have hB : B.ncard = A.ncard := Set.ncard_image_of_injective A Subtype.val_injective
  have hp : p ∉ B := by
    rintro ⟨i, _, hi⟩
    exact i.property.1 hi
  have hq : q ∉ B := by
    rintro ⟨i, _, hi⟩
    exact i.property.2 hi
  let p' : {i // i ∉ B} := ⟨p, hp⟩
  let q' : {i // i ∉ B} := ⟨q, hq⟩
  have hBdeg : B.ncard + 3 = k := by omega
  have hpair := fixedDegree_pair_contraction f k hk hpos hsig B hBdeg p' q'
  have hsymm : ∀ i j,
      (faceCubic f B p' + faceCubic f B q') i j =
        (faceCubic f B p' + faceCubic f B q') j i := by
    intro i j
    simp only [Matrix.add_apply, faceCubic_symm]
  have hpair' := (signature_iff _ (matrix_bilin_symm _ hsymm)).mp hpair
  let e : {i : PairRest p q // i ∉ A} → {i : I // i ∉ B} :=
    fun i => ⟨i.val.val, by
      rintro ⟨j, hj, hji⟩
      exact i.property ((Subtype.val_injective hji) ▸ hj)⟩
  have he : Function.Injective e := by
    intro i j hij
    have h : i.val.val = j.val.val := congrArg (fun z : {i : I // i ∉ B} => z.val) hij
    exact Subtype.ext (Subtype.ext h)
  have heq : (faceCubic f B p' + faceCubic f B q').submatrix e e =
      faceHessian (pairSum f p q) A := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.submatrix_apply, faceCubic, faceHessian]
    have hije : e i ≠ e j := fun h => hij (he h)
    have hpi : p' ≠ e i := fun h => i.val.property.1 (congrArg Subtype.val h).symm
    have hpj : p' ≠ e j := fun h => j.val.property.1 (congrArg Subtype.val h).symm
    have hqi : q' ≠ e i := fun h => i.val.property.2 (congrArg Subtype.val h).symm
    have hqj : q' ≠ e j := fun h => j.val.property.2 (congrArg Subtype.val h).symm
    simp only [Matrix.submatrix_apply, Matrix.add_apply, faceCubic,
      hpi, hpj, hqi, hqj, hije, false_or, ite_false, faceHessian, hij,
      pairSum, Set.image_union, Set.image_pair]
    rfl
  rw [← heq]
  exact onePositive_submatrix _ hpair' e


/-- The output positivity statement in its fixed-degree form. -/
theorem pairSum_degreePositive (f : Set I → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hpos : DegreePositive f k) (p q : I) : DegreePositive (pairSum f p q) (k - 1) := by
  intro U hU
  apply pairSum_positive f k hpos p q U
  omega

abbrev FixedRest (p : I) := {i : I // i ≠ p}

noncomputable def fixIncluded (f : Set I → ℝ) (p : I) (U : Set (FixedRest p)) : ℝ :=
  f (insert p (Subtype.val '' U))

noncomputable def fixExcluded (f : Set I → ℝ) (p : I) (U : Set (FixedRest p)) : ℝ :=
  f (Subtype.val '' U)

lemma fixIncluded_degreePositive (f : Set I → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hpos : DegreePositive f k) (p : I) : DegreePositive (fixIncluded f p) (k - 1) := by
  classical
  intro U hU
  apply hpos
  have hp : p ∉ Subtype.val '' U := by
    rintro ⟨i, _, hi⟩
    exact i.property hi
  rw [ncard_insert_eq _ p hp, Set.ncard_image_of_injective U Subtype.val_injective]
  omega

omit [Fintype I] [DecidableEq I] in
lemma fixExcluded_degreePositive (f : Set I → ℝ) (k : ℕ)
    (hpos : DegreePositive f k) (p : I) : DegreePositive (fixExcluded f p) k := by
  classical
  intro U hU
  apply hpos
  rw [Set.ncard_image_of_injective U Subtype.val_injective]
  exact hU

/-- Fixing an exclusion restricts each quadratic test to a principal submatrix. -/
theorem fixExcluded_addition (f : Set I → ℝ) (k : ℕ)
    (hsig : AdditionProperty f k) (p : I) : AdditionProperty (fixExcluded f p) k := by
  classical
  intro A hA
  let B : Set I := Subtype.val '' A
  have hB : B.ncard + 2 = k := by
    rw [Set.ncard_image_of_injective A Subtype.val_injective]
    exact hA
  let e : {i : FixedRest p // i ∉ A} → {i : I // i ∉ B} :=
    fun i => ⟨i.val.val, by
      rintro ⟨j, hj, hji⟩
      exact i.property ((Subtype.val_injective hji) ▸ hj)⟩
  have he : Function.Injective e := by
    intro i j hij
    have h : i.val.val = j.val.val := congrArg (fun z : {i : I // i ∉ B} => z.val) hij
    exact Subtype.ext (Subtype.ext h)
  have heq : (faceHessian f B).submatrix e e = faceHessian (fixExcluded f p) A := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.submatrix_apply, faceHessian]
    have hije : e i ≠ e j := fun h => hij (he h)
    simp only [Matrix.submatrix_apply, faceHessian, hij, hije, ite_false,
      fixExcluded, Set.image_union, Set.image_pair]
    rfl
  rw [← heq]
  exact onePositive_submatrix _ (hsig B hB) e

/-- Fixing an inclusion enlarges the fixed set in each quadratic test. -/
theorem fixIncluded_addition (f : Set I → ℝ) (k : ℕ)
    (hsig : AdditionProperty f k) (p : I) : AdditionProperty (fixIncluded f p) (k - 1) := by
  classical
  intro A hA
  let B : Set I := Subtype.val '' A
  have hp : p ∉ B := by
    rintro ⟨i, _, hi⟩
    exact i.property hi
  have hBcard : B.ncard = A.ncard := Set.ncard_image_of_injective A Subtype.val_injective
  have hB : (insert p B).ncard + 2 = k := by
    rw [ncard_insert_eq B p hp, hBcard]
    omega
  let e : {i : FixedRest p // i ∉ A} → {i : I // i ∉ insert p B} :=
    fun i => ⟨i.val.val, by
      rintro (hip | ⟨j, hj, hji⟩)
      · exact i.val.property hip
      · exact i.property ((Subtype.val_injective hji) ▸ hj)⟩
  have he : Function.Injective e := by
    intro i j hij
    have h : i.val.val = j.val.val :=
      congrArg (fun z : {i : I // i ∉ insert p B} => z.val) hij
    exact Subtype.ext (Subtype.ext h)
  have heq : (faceHessian f (insert p B)).submatrix e e =
      faceHessian (fixIncluded f p) A := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.submatrix_apply, faceHessian]
    have hije : e i ≠ e j := fun h => hij (he h)
    simp only [Matrix.submatrix_apply, faceHessian, hij, hije, ite_false,
      fixIncluded, Set.image_union, Set.image_pair]
    congr 1
    ext x
    simp [B, e]
    tauto
  rw [← heq]
  apply onePositive_submatrix _ ?_ e
  convert hsig (insert p B) hB using 1
  congr 2
  exact Subsingleton.elim _ _


noncomputable def complementWeight (f : Set I → ℝ) (U : Set I) : ℝ := f Uᶜ

def OmissionProperty (f : Set I → ℝ) (k : ℕ) : Prop :=
  AdditionProperty (complementWeight f) (Fintype.card I - k)

omit [DecidableEq I] in
lemma complement_degreePositive (f : Set I → ℝ) (k : ℕ) (hk : k ≤ Fintype.card I)
    (hpos : DegreePositive f k) : DegreePositive (complementWeight f) (Fintype.card I - k) := by
  classical
  intro U hU
  apply hpos
  have hc := U.ncard_add_ncard_compl
  simp only [Nat.card_eq_fintype_card] at hc
  omega

omit [Fintype I] [DecidableEq I] in
lemma pairRest_image_avoids (p q : I) (U : Set (PairRest p q)) :
    p ∉ Subtype.val '' U ∧ q ∉ Subtype.val '' U := by
  constructor
  · rintro ⟨i, _, hi⟩
    exact i.property.1 hi
  · rintro ⟨i, _, hi⟩
    exact i.property.2 hi

omit [Fintype I] in
/-- Complementation swaps which member of the pair is included. -/
lemma pair_complement_set (p q : I) (hpq : p ≠ q) (U : Set (PairRest p q)) :
    insert p (Subtype.val '' Uᶜ) = (insert q (Subtype.val '' U))ᶜ := by
  classical
  obtain ⟨hpU, hqU⟩ := pairRest_image_avoids p q U
  obtain ⟨hpUc, hqUc⟩ := pairRest_image_avoids p q Uᶜ
  ext x
  by_cases hxp : x = p
  · subst x
    simp [hpq, hpU]
  by_cases hxq : x = q
  · subst x
    simp [Ne.symm hpq, hqUc]
  let xi : PairRest p q := ⟨x, hxp, hxq⟩
  have hmem (V : Set (PairRest p q)) : x ∈ Subtype.val '' V ↔ xi ∈ V := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyi : y = xi := Subtype.ext hyx
      exact hyi ▸ hy
    · intro hx
      exact ⟨xi, hx, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_compl_iff, hxp, hxq, false_or, hmem]

omit [Fintype I] in
lemma pairSum_complement (f : Set I → ℝ) (p q : I) (hpq : p ≠ q) :
    complementWeight (pairSum f p q) = pairSum (complementWeight f) p q := by
  classical
  funext U
  have hq := congrArg (fun V : Set I => Vᶜ) (pair_complement_set p q hpq Uᶜ)
  simp only [compl_compl] at hq
  simp only [complementWeight, pairSum]
  rw [pair_complement_set p q hpq U, hq.symm, add_comm]

lemma card_pairRest (p q : I) (hpq : p ≠ q) :
    Fintype.card (PairRest p q) + 2 = Fintype.card I := by
  classical
  have hc := card_outside ({p, q} : Set I)
  simpa [PairRest, Set.ncard_pair hpq, not_or] using hc

/-- Complementation preserves occupancy one, so the proved addition closure
gives omission closure on every valid residual degree. -/
theorem pairSum_omission (f : Set I → ℝ) (k : ℕ)
    (hk : 1 ≤ k) (hkupper : k + 1 ≤ Fintype.card I)
    (hpos : DegreePositive f k) (hsig : OmissionProperty f k)
    (p q : I) (hpq : p ≠ q) : OmissionProperty (pairSum f p q) (k - 1) := by
  classical
  have hc := card_pairRest p q hpq
  have hp := complement_degreePositive f k (by omega) hpos
  have ha := pairSum_addition (complementWeight f) (Fintype.card I - k)
    (Nat.sub_le _ _) hp hsig p q
  change AdditionProperty (complementWeight (pairSum f p q))
    (Fintype.card (PairRest p q) - (k - 1))
  rw [pairSum_complement f p q hpq]
  convert ha using 1
  omega


omit [Fintype I] [DecidableEq I] in
lemma fixed_complement_set (p : I) (U : Set (FixedRest p)) :
    insert p (Subtype.val '' Uᶜ) = (Subtype.val '' U)ᶜ := by
  classical
  have hpU : p ∉ Subtype.val '' U := by
    rintro ⟨i, _, hi⟩
    exact i.property hi
  ext x
  by_cases hxp : x = p
  · subst x
    simp [hpU]
  let xi : FixedRest p := ⟨x, hxp⟩
  have hmem (V : Set (FixedRest p)) : x ∈ Subtype.val '' V ↔ xi ∈ V := by
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hyi : y = xi := Subtype.ext hyx
      exact hyi ▸ hy
    · intro hx
      exact ⟨xi, hx, rfl⟩
  simp only [Set.mem_insert_iff, Set.mem_compl_iff, hxp, false_or, hmem]

omit [Fintype I] [DecidableEq I] in
lemma fixIncluded_complement (f : Set I → ℝ) (p : I) :
    complementWeight (fixIncluded f p) = fixExcluded (complementWeight f) p := by
  funext U
  exact congrArg f (fixed_complement_set p U)

omit [Fintype I] [DecidableEq I] in
lemma fixExcluded_complement (f : Set I → ℝ) (p : I) :
    complementWeight (fixExcluded f p) = fixIncluded (complementWeight f) p := by
  classical
  funext U
  have h := congrArg (fun V : Set I => Vᶜ) (fixed_complement_set p Uᶜ)
  simp only [compl_compl] at h
  exact congrArg f h.symm

lemma card_fixedRest (p : I) : Fintype.card (FixedRest p) + 1 = Fintype.card I := by
  classical
  have hc := card_outside ({p} : Set I)
  simpa [FixedRest] using hc

/-- Complementation swaps a fixed inclusion with a fixed exclusion. -/
theorem fixIncluded_omission (f : Set I → ℝ) (k : ℕ) (hk : 1 ≤ k)
    (hsig : OmissionProperty f k) (p : I) : OmissionProperty (fixIncluded f p) (k - 1) := by
  classical
  have hc := card_fixedRest p
  have ha := fixExcluded_addition (complementWeight f) (Fintype.card I - k) hsig p
  change AdditionProperty (complementWeight (fixIncluded f p))
    (Fintype.card (FixedRest p) - (k - 1))
  rw [fixIncluded_complement]
  convert ha using 1
  omega

/-- Complementation swaps a fixed exclusion with a fixed inclusion. -/
theorem fixExcluded_omission (f : Set I → ℝ) (k : ℕ)
    (hsig : OmissionProperty f k) (p : I) : OmissionProperty (fixExcluded f p) k := by
  classical
  have hc := card_fixedRest p
  have ha := fixIncluded_addition (complementWeight f) (Fintype.card I - k) hsig p
  change AdditionProperty (complementWeight (fixExcluded f p))
    (Fintype.card (FixedRest p) - k)
  rw [fixExcluded_complement]
  convert ha using 1
  omega

end ContingencyTables.BinaryContraction

end OAI
