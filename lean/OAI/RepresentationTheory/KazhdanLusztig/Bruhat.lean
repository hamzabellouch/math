import OAI.RepresentationTheory.KazhdanLusztig.Model
import OAI.RepresentationTheory.KazhdanLusztig.Coxeter

namespace OAI

/-!
Strong Bruhat order, subwords, length, finite lower ideals and arbitrary finite intervals; the selected R family.
-/

namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}


theorem bruhat_refl (cs : CoxeterSystem M W) (x : W) : BruhatLE cs x x :=
  Relation.ReflTransGen.refl

theorem bruhat_trans (cs : CoxeterSystem M W) {x y z : W}
    (hxy : BruhatLE cs x y) (hyz : BruhatLE cs y z) : BruhatLE cs x z :=
  hxy.trans hyz

theorem length_le_of_bruhat (cs : CoxeterSystem M W) {x y : W}
    (h : BruhatLE cs x y) : cs.length x ≤ cs.length y := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih => exact le_trans hstep.1.le ih

theorem length_lt_of_bruhat_ne (cs : CoxeterSystem M W) {x y : W}
    (h : BruhatLE cs x y) (hne : x ≠ y) : cs.length x < cs.length y := by
  rcases h.cases_head with heq | ⟨z, hxz, hzy⟩
  · exact (hne heq).elim
  · exact lt_of_lt_of_le hxz.1 (length_le_of_bruhat cs hzy)

theorem bruhat_antisymm (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatLE cs x y) (hyx : BruhatLE cs y x) : x = y := by
  by_contra hne
  exact (not_lt_of_ge (length_le_of_bruhat cs hyx)) (length_lt_of_bruhat_ne cs hxy hne)

end KLInvariance

namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [Group W] {M : CoxeterMatrix B}


noncomputable def rPolynomial (cs : CoxeterSystem M W) (x y : W) : ℤ[X] :=
  (klFamilies cs).1 x y

end KLInvariance

section


namespace KLInvariance

open Polynomial

universe u v u' v'

variable {B : Type u} {W : Type v} [klPreservedInstance1 : Group W] {M : CoxeterMatrix B}


/-- A vertex has only finitely many incoming strong Bruhat edges, using
strong exchange proved from the Coxeter presentation above. -/
theorem finite_bruhat_predecessors (cs : CoxeterSystem M W) (b : W) :
    {x : W | BruhatStep cs x b}.Finite := by
  classical
  obtain ⟨ω, hω, heq⟩ := cs.exists_isReduced b
  refine ((cs.leftInvSeq ω).finite_toSet.image (fun t => t * b)).subset ?_
  rintro x ⟨hlen, t, href, hb⟩
  have hx : t * b = x := by
    rw [hb, ← mul_assoc, href.mul_self, one_mul]
  refine ⟨t, ?_, hx⟩
  apply CoxeterSupport.mem_leftInvSeq_of_inversion cs hω
  exact ⟨href, by rw [← heq, hx]; exact hlen⟩

/-- Finiteness of all lower Bruhat ideals, with no finite-rank assumption. -/
theorem finite_bruhat_lower (cs : CoxeterSystem M W) (b : W) :
    {x : W | BruhatLE cs x b}.Finite := by
  classical
  suffices ∀ n : ℕ, ∀ b : W, cs.length b = n → {x : W | BruhatLE cs x b}.Finite by
    exact this (cs.length b) b rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro b hb
    have hfinite : ({b} ∪ ⋃ z ∈ {z : W | BruhatStep cs z b},
        {x : W | BruhatLE cs x z}).Finite :=
      (Set.finite_singleton b).union ((finite_bruhat_predecessors cs b).biUnion
        (fun z hz => ih (cs.length z) (hb ▸ hz.1) z rfl))
    apply hfinite.subset
    intro x hx
    rcases hx.cases_tail with h | ⟨z, hxz, hzb⟩
    · exact Or.inl (h.symm)
    · exact Or.inr (Set.mem_iUnion.mpr ⟨z, Set.mem_iUnion.mpr ⟨hzb, hxz⟩⟩)

/-- The finite-interval obligation in the faithful trusted main target. -/
theorem interval_finite (cs : CoxeterSystem M W) (u b : W) :
    Finite (Interval cs u b) :=
  ((finite_bruhat_lower cs b).subset (fun _ hx => hx.2)).to_subtype

/-- The exact R recursion determines at most one R family. -/
theorem normalized_R_unique (cs : CoxeterSystem M W)
    {RP SQ : PolynomialFamilies W} (hRP : NormalizedKL cs RP) (hSQ : NormalizedKL cs SQ) :
    RP.1 = SQ.1 := by
  classical
  suffices ∀ n : ℕ, ∀ y : W, cs.length y = n → ∀ x, RP.1 x y = SQ.1 x y by
    funext x y
    exact this (cs.length y) y rfl x
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro y hy x
    by_cases h1 : y = 1
    · subst y
      by_cases hx : x = 1
      · subst x
        rw [hRP.R_diagonal, hSQ.R_diagonal]
      · have hn : ¬ BruhatLE cs x 1 := by
          intro h
          have hl := length_le_of_bruhat cs h
          have hx0 : cs.length x = 0 := by simpa using hl
          exact hx (cs.length_eq_zero_iff.mp hx0)
        rw [hRP.R_zero _ _ hn, hSQ.R_zero _ _ hn]
    · obtain ⟨i, hi⟩ := cs.exists_leftDescent_of_ne_one h1
      have hlt : cs.length (cs.simple i * y) < n := hy ▸ hi
      rw [hRP.R_recursion x y i hi, hSQ.R_recursion x y i hi]
      rw [ih _ hlt _ rfl x, ih _ hlt _ rfl (cs.simple i * x)]

/-- The degree/reciprocity rigidity used both by normalization uniqueness and
by the final main-theorem induction: no polynomial supported strictly below
the midpoint can be self-reciprocal about that midpoint. -/
theorem low_degree_reflect_eq_self (f : ℤ[X]) (d : ℕ)
    (hd : 2 * f.natDegree < d) (hself : reflect d f = f) : f = 0 := by
  by_contra hn
  have hc := congrArg (fun p : ℤ[X] => p.coeff f.natDegree) hself
  rw [coeff_reflect, revAt_le (by omega)] at hc
  rw [coeff_eq_zero_of_natDegree_lt (by omega), coeff_natDegree] at hc
  exact (leadingCoeff_ne_zero.mpr hn) hc.symm

/-- The polynomial part of the manuscript's normalization is unique; the
proof uses the actual finite strong-Bruhat intervals, not extra assumptions. -/
theorem normalized_P_unique (cs : CoxeterSystem M W)
    {RP SQ : PolynomialFamilies W} (hRP : NormalizedKL cs RP) (hSQ : NormalizedKL cs SQ) :
    RP.2 = SQ.2 := by
  classical
  have hR := normalized_R_unique cs hRP hSQ
  suffices ∀ n : ℕ, ∀ x y : W, rankDifference cs x y = n → RP.2 x y = SQ.2 x y by
    funext x y
    exact this (rankDifference cs x y) x y rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hxy
    by_cases hcomp : BruhatLE cs x y
    · by_cases heq : x = y
      · subst y
        rw [hRP.P_diagonal, hSQ.P_diagonal]
      · let : Finite (Interval cs x y) := interval_finite cs x y
        let : Fintype (Interval cs x y) := Fintype.ofFinite _
        let bottom : Interval cs x y := ⟨x, bruhat_refl cs x, hcomp⟩
        have hsum : (∑ z : Interval cs x y,
            RP.1 x z.val * (RP.2 z.val y - SQ.2 z.val y)) = RP.2 x y - SQ.2 x y := by
          rw [Finset.sum_eq_single bottom]
          · simp [bottom, hRP.R_diagonal]
          · intro z _ hz
            have hxz : x ≠ z.val := by
              intro hc
              apply hz
              exact Subtype.ext hc.symm
            have hlt := length_lt_of_bruhat_ne cs z.property.1 hxz
            have hle := length_le_of_bruhat cs z.property.2
            have hdiff : rankDifference cs z.val y < n := by
              dsimp [rankDifference] at hxy ⊢
              omega
            rw [ih _ hdiff z.val y rfl, sub_self, mul_zero]
          · simp
        have href : reflect (rankDifference cs x y) (RP.2 x y - SQ.2 x y) =
            RP.2 x y - SQ.2 x y := by
          rw [reflect_sub, hRP.reciprocity x y hcomp, hSQ.reciprocity x y hcomp,
            finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← Finset.sum_sub_distrib]
          rw [← hsum]
          apply Finset.sum_congr rfl
          intro z _
          rw [← hR, mul_sub]
        have hd1 := hRP.P_degree x y hcomp heq
        have hd2 := hSQ.P_degree x y hcomp heq
        have hdeg := natDegree_sub_le (RP.2 x y) (SQ.2 x y)
        have hzero := low_degree_reflect_eq_self (RP.2 x y - SQ.2 x y)
          (rankDifference cs x y) (by omega) href
        exact sub_eq_zero.mp hzero
    · rw [hRP.P_zero _ _ hcomp, hSQ.P_zero _ _ hcomp]

/-- Unique existence is still a separate obligation: this proves its
uniqueness half only, without postulating a normalized family. -/
theorem normalizedKL_unique (cs : CoxeterSystem M W)
    {RP SQ : PolynomialFamilies W} (hRP : NormalizedKL cs RP) (hSQ : NormalizedKL cs SQ) :
    RP = SQ :=
  Prod.ext (normalized_R_unique cs hRP hSQ) (normalized_P_unique cs hRP hSQ)


/-! Exchange consequences required for the source's finite-rank reduction
and for consistency of the equal-parameter Hecke recursion. -/

/-- Every word contains a reduced subword with the same product. -/
theorem exists_reduced_subword (cs : CoxeterSystem M W) (ω : List B) :
    ∃ ν : List B, ν.Sublist ω ∧ cs.IsReduced ν ∧ cs.wordProd ν = cs.wordProd ω := by
  induction ω with
  | nil => exact ⟨[], .refl _, by simp [CoxeterSystem.IsReduced], rfl⟩
  | cons i ω ih =>
    obtain ⟨ν, hsub, hν, heq⟩ := ih
    rcases cs.length_simple_mul (cs.wordProd ν) i with hasc | hdesc
    · refine ⟨i :: ν, hsub.cons_cons i, ?_, ?_⟩
      · simpa [CoxeterSystem.IsReduced, cs.wordProd_cons, hν.eq] using hasc
      · simp [cs.wordProd_cons, heq]
    · obtain ⟨j, hj, hdel⟩ := CoxeterSupport.strong_exchange cs hν
        ⟨cs.isReflection_simple i, by omega⟩
      refine ⟨ν.eraseIdx j, ((ν.eraseIdx_sublist j).trans hsub).cons i, ?_, ?_⟩
      · dsimp [CoxeterSystem.IsReduced]
        rw [← hdel, List.length_eraseIdx, ite_eq_left hj]
        have := hν.eq
        omega
      · rw [← hdel, heq, cs.wordProd_cons]

/-- A single downward reflection step can be realized inside any reduced word. -/
theorem subword_of_bruhat_step (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatStep cs x y) {ω : List B} (hω : cs.IsReduced ω)
    (hy : cs.wordProd ω = y) :
    ∃ ν : List B, ν.Sublist ω ∧ cs.IsReduced ν ∧ cs.wordProd ν = x := by
  obtain ⟨hlen, t, ht, rfl⟩ := hxy
  have hx : t * cs.wordProd ω = x := by simp [hy, ← mul_assoc, ht.mul_self]
  obtain ⟨j, hj, hdel⟩ := CoxeterSupport.strong_exchange cs hω
    ⟨ht, by
      rw [hx, hy]
      exact hlen⟩
  obtain ⟨ν, hsub, hν, heq⟩ := exists_reduced_subword cs (ω.eraseIdx j)
  exact ⟨ν, hsub.trans (ω.eraseIdx_sublist j), hν, heq.trans (hdel.symm.trans hx)⟩

/-- Forward subword property, for every chosen reduced expression of the top. -/
theorem reduced_subword_of_bruhat (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatLE cs x y) {ω : List B} (hω : cs.IsReduced ω)
    (hy : cs.wordProd ω = y) :
    ∃ ν : List B, ν.Sublist ω ∧ cs.IsReduced ν ∧ cs.wordProd ν = x := by
  induction hxy using Relation.ReflTransGen.head_induction_on generalizing ω with
  | refl => exact ⟨ω, .refl _, hω, hy⟩
  | head hstep _ ih =>
    obtain ⟨ν, hsub, hν, heq⟩ := ih hω hy
    obtain ⟨μ, hμsub, hμ, hμeq⟩ := subword_of_bruhat_step cs hstep hν heq
    exact ⟨μ, hμsub.trans hsub, hμ, hμeq⟩


/-- Simple left multiplication preserves the orientation of every reflection
edge except the edge carrying that simple reflection itself. -/
theorem bruhatStep_simple_mul (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatStep cs x y) (i : B) (hne : y ≠ cs.simple i * x) :
    BruhatStep cs (cs.simple i * x) (cs.simple i * y) := by
  obtain ⟨hlen, t, ht, heq⟩ := hxy
  refine ⟨?_, cs.simple i * t * cs.simple i, by simpa using ht.conj (cs.simple i), ?_⟩
  · rcases cs.length_simple_mul y i with hasc | hdesc
    · have hx := cs.length_simple_mul x i
      omega
    · obtain ⟨ω, hω, hωeq⟩ := cs.exists_isReduced (cs.simple i * y)
      have hprod : cs.wordProd (i :: ω) = y := by
        rw [cs.wordProd_cons, ← hωeq, cs.simple_mul_simple_cancel_left]
      have hr : cs.IsReduced (i :: ω) := by
        dsimp [CoxeterSystem.IsReduced]
        rw [hprod, ← hω.eq, ← hωeq]
        exact hdesc.symm
      have htx : t * cs.wordProd (i :: ω) = x := by
        rw [hprod, heq, ← mul_assoc, ht.mul_self, one_mul]
      obtain ⟨j, hj, hdel⟩ := CoxeterSupport.strong_exchange cs hr
        ⟨ht, by rw [htx, hprod]; exact hlen⟩
      cases j with
      | zero =>
        have hx : x = cs.wordProd ω := by simpa [htx] using hdel
        exact (hne (by rw [hx, ← cs.wordProd_cons, hprod])).elim
      | succ j =>
        have hx : x = cs.simple i * cs.wordProd (ω.eraseIdx j) := by
          rw [htx, List.eraseIdx_cons_succ, cs.wordProd_cons] at hdel
          exact hdel
        have hsx : cs.simple i * x = cs.wordProd (ω.eraseIdx j) := by simp [hx]
        have hj' : j < ω.length := by simpa using hj
        have hlen' := cs.length_wordProd_le (ω.eraseIdx j)
        rw [List.length_eraseIdx, ite_eq_left hj'] at hlen'
        rw [hsx, hωeq, hω.eq]
        omega
  · rw [heq]
    simp [mul_assoc]

/-- The smaller of `x` and `s*x` in Bruhat order. -/
noncomputable def lowerSimple (cs : CoxeterSystem M W) (i : B) (x : W) : W :=
  if cs.length (cs.simple i * x) < cs.length x then cs.simple i * x else x

/-- The larger of `x` and `s*x` in Bruhat order. -/
noncomputable def upperSimple (cs : CoxeterSystem M W) (i : B) (x : W) : W :=
  if cs.length (cs.simple i * x) < cs.length x then x else cs.simple i * x

theorem lowerSimple_le (cs : CoxeterSystem M W) (i : B) (x : W) :
    BruhatLE cs (lowerSimple cs i x) x := by
  classical
  unfold lowerSimple
  split_ifs with h
  · exact .single ⟨h, cs.simple i, cs.isReflection_simple i, by simp⟩
  · exact .refl

theorem le_upperSimple (cs : CoxeterSystem M W) (i : B) (x : W) :
    BruhatLE cs x (upperSimple cs i x) := by
  classical
  unfold upperSimple
  split_ifs with h
  · exact .refl
  · exact .single ⟨by have := cs.length_simple_mul x i; omega,
      cs.simple i, cs.isReflection_simple i, rfl⟩

@[simp] theorem lowerSimple_mul (cs : CoxeterSystem M W) (i : B) (x : W) :
    lowerSimple cs i (cs.simple i * x) = lowerSimple cs i x := by
  classical
  unfold lowerSimple
  rw [cs.simple_mul_simple_cancel_left]
  have := cs.length_simple_mul x i
  split_ifs <;> first | rfl | omega

@[simp] theorem upperSimple_mul (cs : CoxeterSystem M W) (i : B) (x : W) :
    upperSimple cs i (cs.simple i * x) = upperSimple cs i x := by
  classical
  unfold upperSimple
  rw [cs.simple_mul_simple_cancel_left]
  have := cs.length_simple_mul x i
  split_ifs <;> first | rfl | omega

theorem lowerSimple_step_mono (cs : CoxeterSystem M W) (i : B) {x y : W}
    (hxy : BruhatStep cs x y) :
    BruhatLE cs (lowerSimple cs i x) (lowerSimple cs i y) := by
  classical
  by_cases heq : y = cs.simple i * x
  · rw [heq, lowerSimple_mul]
    exact .refl
  · have hs := bruhatStep_simple_mul cs hxy i heq
    by_cases hx : cs.length (cs.simple i * x) < cs.length x
    · by_cases hy : cs.length (cs.simple i * y) < cs.length y
      · simp only [lowerSimple, ite_eq_left hx, ite_eq_left hy]
        exact .single hs
      · simp only [lowerSimple, ite_eq_left hx, ite_eq_right hy]
        have hlow := lowerSimple_le cs i x
        simp only [lowerSimple, ite_eq_left hx] at hlow
        exact hlow.trans (.single hxy)
    · by_cases hy : cs.length (cs.simple i * y) < cs.length y
      · simp only [lowerSimple, ite_eq_right hx, ite_eq_left hy]
        have hupp := le_upperSimple cs i x
        simp only [upperSimple, ite_eq_right hx] at hupp
        exact hupp.trans (.single hs)
      · simp only [lowerSimple, ite_eq_right hx, ite_eq_right hy]
        exact .single hxy

theorem upperSimple_step_mono (cs : CoxeterSystem M W) (i : B) {x y : W}
    (hxy : BruhatStep cs x y) :
    BruhatLE cs (upperSimple cs i x) (upperSimple cs i y) := by
  classical
  by_cases heq : y = cs.simple i * x
  · rw [heq, upperSimple_mul]
    exact .refl
  · have hs := bruhatStep_simple_mul cs hxy i heq
    by_cases hx : cs.length (cs.simple i * x) < cs.length x
    · by_cases hy : cs.length (cs.simple i * y) < cs.length y
      · simp only [upperSimple, ite_eq_left hx, ite_eq_left hy]
        exact .single hxy
      · simp only [upperSimple, ite_eq_left hx, ite_eq_right hy]
        have hupp := le_upperSimple cs i y
        simp only [upperSimple, ite_eq_right hy] at hupp
        exact (Relation.ReflTransGen.single hxy).trans hupp
    · by_cases hy : cs.length (cs.simple i * y) < cs.length y
      · simp only [upperSimple, ite_eq_right hx, ite_eq_left hy]
        have hlow := lowerSimple_le cs i y
        simp only [lowerSimple, ite_eq_left hy] at hlow
        exact (Relation.ReflTransGen.single hs).trans hlow
      · simp only [upperSimple, ite_eq_right hx, ite_eq_right hy]
        exact .single hs

theorem lowerSimple_mono (cs : CoxeterSystem M W) (i : B) {x y : W}
    (hxy : BruhatLE cs x y) :
    BruhatLE cs (lowerSimple cs i x) (lowerSimple cs i y) := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hstep _ ih => exact (lowerSimple_step_mono cs i hstep).trans ih

theorem upperSimple_mono (cs : CoxeterSystem M W) (i : B) {x y : W}
    (hxy : BruhatLE cs x y) :
    BruhatLE cs (upperSimple cs i x) (upperSimple cs i y) := by
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head hstep _ ih => exact (upperSimple_step_mono cs i hstep).trans ih


/-- The standard lifting property, now for the actual strong order. -/
theorem bruhat_lifting (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatLE cs x y) (i : B)
    (hx : cs.length x < cs.length (cs.simple i * x))
    (hy : cs.length (cs.simple i * y) < cs.length y) :
    BruhatLE cs x (cs.simple i * y) ∧ BruhatLE cs (cs.simple i * x) y := by
  have hx' : ¬cs.length (cs.simple i * x) < cs.length x := by omega
  constructor
  · simpa only [lowerSimple, ite_eq_right hx', ite_eq_left hy] using lowerSimple_mono cs i hxy
  · simpa only [upperSimple, ite_eq_right hx', ite_eq_left hy] using upperSimple_mono cs i hxy

/-- Converse subword property; no labels are added to Bruhat intervals. -/
theorem bruhat_of_subword (cs : CoxeterSystem M W) {ν ω : List B}
    (hsub : ν.Sublist ω) (hω : cs.IsReduced ω) :
    BruhatLE cs (cs.wordProd ν) (cs.wordProd ω) := by
  induction ω generalizing ν with
  | nil =>
    have : ν = [] := List.sublist_nil.mp hsub
    subst ν
    exact .refl
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have hasc : cs.length (cs.simple i * cs.wordProd ω) = cs.length (cs.wordProd ω) + 1 := by
      simpa [CoxeterSystem.IsReduced, cs.wordProd_cons, hω'.eq] using hω.eq
    have htop : upperSimple cs i (cs.wordProd ω) = cs.wordProd (i :: ω) := by
      simp [upperSimple, show ¬cs.length (cs.simple i * cs.wordProd ω) <
        cs.length (cs.wordProd ω) by omega, cs.wordProd_cons]
    rcases List.sublist_cons_iff.mp hsub with hsub' | ⟨μ, rfl, hμsub⟩
    · exact (ih hsub' hω').trans (htop ▸ le_upperSimple cs i (cs.wordProd ω))
    · have hle := upperSimple_mono cs i (ih hμsub hω')
      rw [htop] at hle
      have hx := le_upperSimple cs i (cs.simple i * cs.wordProd μ)
      rw [upperSimple_mul] at hx
      rw [cs.wordProd_cons]
      exact hx.trans hle

/-- The subword criterion with an arbitrary fixed reduced word for the top. -/
theorem bruhat_iff_reduced_subword (cs : CoxeterSystem M W) {x : W} {ω : List B}
    (hω : cs.IsReduced ω) :
    BruhatLE cs x (cs.wordProd ω) ↔
      ∃ ν : List B, ν.Sublist ω ∧ cs.IsReduced ν ∧ cs.wordProd ν = x := by
  constructor
  · intro hx
    exact reduced_subword_of_bruhat cs hx hω rfl
  · rintro ⟨ν, hsub, _, rfl⟩
    exact bruhat_of_subword cs hsub hω

/-- Precisely the finite-support part used by the manuscript's finite-rank
reduction: all lower elements are words in the generators of any reduced top
word. Equality of parabolic polynomial normalizations remains a later step. -/
theorem lower_ideal_finite_generator_support (cs : CoxeterSystem M W) (b : W) :
    ∃ J : Set B, J.Finite ∧ ∀ x, BruhatLE cs x b →
      ∃ ν : List B, (∀ i ∈ ν, i ∈ J) ∧ cs.wordProd ν = x := by
  obtain ⟨ω, hω, heq⟩ := cs.exists_isReduced b
  refine ⟨{i | i ∈ ω}, ω.finite_toSet, ?_⟩
  intro x hx
  obtain ⟨ν, hsub, _, hprod⟩ := reduced_subword_of_bruhat cs hx hω heq.symm
  exact ⟨ν, fun i hi => hsub.subset hi, hprod⟩


/-- Inversion preserves the actual strong Bruhat graph. -/
theorem bruhatStep_inv (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatStep cs x y) : BruhatStep cs x⁻¹ y⁻¹ := by
  obtain ⟨hlen, t, ht, heq⟩ := hxy
  refine ⟨by simpa using hlen, x⁻¹ * t * x, by simpa using ht.conj x⁻¹, ?_⟩
  rw [heq, mul_inv_rev, ht.inv]
  group

theorem bruhatStep_mul_simple (cs : CoxeterSystem M W) {x y : W}
    (hxy : BruhatStep cs x y) (i : B) (hne : y ≠ x * cs.simple i) :
    BruhatStep cs (x * cs.simple i) (y * cs.simple i) := by
  have hinv := bruhatStep_inv cs hxy
  have hne' : y⁻¹ ≠ cs.simple i * x⁻¹ := by
    intro heq
    apply hne
    have := congrArg Inv.inv heq
    simpa [mul_inv_rev] using this
  have h := bruhatStep_inv cs (bruhatStep_simple_mul cs hinv i hne')
  simpa [mul_inv_rev] using h

/-- The noncollapsed left/right simple square has consistent orientations. -/
theorem left_descent_mul_simple_iff (cs : CoxeterSystem M W) (i j : B) (x : W)
    (hne : cs.simple i * x ≠ x * cs.simple j) :
    cs.length (cs.simple i * (x * cs.simple j)) < cs.length (x * cs.simple j) ↔
      cs.length (cs.simple i * x) < cs.length x := by
  by_cases hx : cs.length (cs.simple i * x) < cs.length x
  · have hedge : BruhatStep cs (cs.simple i * x) x :=
      ⟨hx, cs.simple i, cs.isReflection_simple i, by simp⟩
    have hne' : x ≠ cs.simple i * x * cs.simple j := by
      intro heq
      apply hne
      have := congrArg (fun z => z * cs.simple j) heq
      simpa using this.symm
    have h := (bruhatStep_mul_simple cs hedge j hne').1
    simpa only [mul_assoc, hx, iff_true] using h
  · have hedge : BruhatStep cs x (cs.simple i * x) :=
      ⟨by have := cs.length_simple_mul x i; omega, cs.simple i,
        cs.isReflection_simple i, rfl⟩
    have h := (bruhatStep_mul_simple cs hedge j hne).1
    rw [mul_assoc] at h
    exact iff_of_false (by omega) hx

theorem right_descent_simple_mul_iff (cs : CoxeterSystem M W) (i j : B) (x : W)
    (hne : cs.simple i * x ≠ x * cs.simple j) :
    cs.length (cs.simple i * x * cs.simple j) < cs.length (cs.simple i * x) ↔
      cs.length (x * cs.simple j) < cs.length x := by
  have hne' : cs.simple j * x⁻¹ ≠ x⁻¹ * cs.simple i := by
    intro heq
    apply hne
    have h := congrArg Inv.inv heq
    simpa [mul_inv_rev] using h.symm
  have h := left_descent_mul_simple_iff cs j i x⁻¹ hne'
  have h1 : cs.length (cs.simple i * x * cs.simple j) =
      cs.length (cs.simple j * (x⁻¹ * cs.simple i)) := by
    rw [← cs.length_inv (cs.simple i * x * cs.simple j)]
    simp [mul_inv_rev]
  have h2 : cs.length (cs.simple i * x) = cs.length (x⁻¹ * cs.simple i) := by
    rw [← cs.length_inv (cs.simple i * x)]
    simp [mul_inv_rev]
  have h3 : cs.length (x * cs.simple j) = cs.length (cs.simple j * x⁻¹) := by
    rw [← cs.length_inv (x * cs.simple j)]
    simp [mul_inv_rev]
  rw [h1, h2, h3]
  simpa using h


end KLInvariance
end

end OAI
