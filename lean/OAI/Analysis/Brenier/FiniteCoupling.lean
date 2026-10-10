import Mathlib

namespace OAI

noncomputable section

open scoped BigOperators
open Set

namespace Problem358

variable {I J : Type*} [Fintype I] [Fintype J]

/-- The transportation polytope of two finite real-valued probability vectors is compact. -/
theorem isCompact_finite_coupling_set
    (a : I → ℝ) (b : J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hasum : ∑ i, a i = 1) :
    IsCompact {p : I → J → ℝ |
      (∀ i j, 0 ≤ p i j) ∧
      (∀ i, ∑ j, p i j = a i) ∧
      (∀ j, ∑ i, p i j = b j)} := by
  classical
  have hnonneg : IsClosed {p : I → J → ℝ | ∀ i j, 0 ≤ p i j} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_le continuous_const ((continuous_apply j).comp (continuous_apply i))
  have hrows : IsClosed {p : I → J → ℝ | ∀ i, ∑ j, p i j = a i} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun i => isClosed_eq (by fun_prop) continuous_const
  have hcols : IsClosed {p : I → J → ℝ | ∀ j, ∑ i, p i j = b j} := by
    simp only [ofPred_forall]
    exact isClosed_iInter fun j => isClosed_eq (by fun_prop) continuous_const
  have hclosed : IsClosed {p : I → J → ℝ |
      (∀ i j, 0 ≤ p i j) ∧
      (∀ i, ∑ j, p i j = a i) ∧
      (∀ j, ∑ i, p i j = b j)} := hnonneg.inter (hrows.inter hcols)
  apply (isCompact_Icc : IsCompact (Icc (0 : I → J → ℝ) 1)).of_isClosed_subset hclosed
  intro p hp
  refine ⟨hp.1, ?_⟩
  intro i j
  have hpij : p i j ≤ ∑ k, p i k :=
    Finset.single_le_sum (fun k _ => hp.1 i k) (Finset.mem_univ j)
  have hai : a i ≤ ∑ k, a k :=
    Finset.single_le_sum (fun k _ => ha k) (Finset.mem_univ i)
  rw [hp.2.1 i] at hpij
  rw [hasum] at hai
  exact hpij.trans hai

/-- Every finite transportation problem with probability margins has a cost minimizer.
No nonnegativity or metric assumptions on the finite cost matrix are needed. -/
theorem exists_minimal_finite_coupling
    (a : I → ℝ) (b : J → ℝ) (c : I → J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hasum : ∑ i, a i = 1) (hbsum : ∑ j, b j = 1) :
    ∃ p : I → J → ℝ,
      (∀ i j, 0 ≤ p i j) ∧
      (∀ i, ∑ j, p i j = a i) ∧
      (∀ j, ∑ i, p i j = b j) ∧
      ∀ q : I → J → ℝ,
        (∀ i j, 0 ≤ q i j) →
        (∀ i, ∑ j, q i j = a i) →
        (∀ j, ∑ i, q i j = b j) →
        (∑ i, ∑ j, p i j * c i j) ≤ ∑ i, ∑ j, q i j * c i j := by
  classical
  let S := {p : I → J → ℝ |
      (∀ i j, 0 ≤ p i j) ∧
      (∀ i, ∑ j, p i j = a i) ∧
      (∀ j, ∑ i, p i j = b j)}
  have hS : IsCompact S := isCompact_finite_coupling_set a b ha hasum
  have hne : S.Nonempty := by
    refine ⟨fun i j => a i * b j, ?_, ?_, ?_⟩
    · exact fun i j => mul_nonneg (ha i) (hb j)
    · intro i
      rw [← Finset.mul_sum, hbsum, mul_one]
    · intro j
      rw [← Finset.sum_mul, hasum, one_mul]
  let cost : (I → J → ℝ) → ℝ := fun p => ∑ i, ∑ j, p i j * c i j
  have hcost : Continuous cost := by fun_prop
  obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne hcost.continuousOn
  refine ⟨p, hp.1, hp.2.1, hp.2.2, ?_⟩
  intro q hq hqr hqc
  exact hmin ⟨hq, hqr, hqc⟩

end Problem358

end

noncomputable section

open scoped BigOperators InnerProductSpace

namespace Problem358

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The exact decrease in quadratic cost obtained by swapping two target sites. -/
theorem quadratic_swap_identity (x₀ x₁ y₀ y₁ : V) :
    ‖x₀ - y₁‖ ^ 2 + ‖x₁ - y₀‖ ^ 2 -
      (‖x₀ - y₀‖ ^ 2 + ‖x₁ - y₁‖ ^ 2) =
        2 * ⟪x₀ - x₁, y₀ - y₁⟫_ℝ := by
  simp only [norm_sub_sq_real, inner_sub_left, inner_sub_right]
  ring

/-- Pairwise optimality of a quadratic matching implies monotonicity. -/
theorem inner_sub_nonneg_of_quadratic_swap
    (x₀ x₁ y₀ y₁ : V)
    (h : ‖x₀ - y₀‖ ^ 2 + ‖x₁ - y₁‖ ^ 2 ≤
      ‖x₀ - y₁‖ ^ 2 + ‖x₁ - y₀‖ ^ 2) :
    0 ≤ ⟪x₀ - x₁, y₀ - y₁⟫_ℝ := by
  have he := quadratic_swap_identity x₀ x₁ y₀ y₁
  linarith

/-- A monotone pair of displacements cannot cancel at an interior interpolation time. -/
theorem monotone_interpolation_ne_zero
    (a b : V) (hmono : 0 ≤ ⟪a, b⟫_ℝ)
    (hne : a ≠ 0 ∨ b ≠ 0) {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (1 - t) • a + t • b ≠ 0 := by
  intro heq
  have hinner := congrArg (fun z : V => ⟪z, z⟫_ℝ) heq
  simp only [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, inner_zero_left] at hinner
  rw [real_inner_comm a b] at hinner
  have ha : 0 ≤ ⟪a, a⟫_ℝ := real_inner_self_nonneg
  have hb : 0 ≤ ⟪b, b⟫_ℝ := real_inner_self_nonneg
  have ht : 0 < 1 - t := sub_pos.mpr ht1
  rcases hne with ha0 | hb0
  · have hapos : 0 < ⟪a, a⟫_ℝ := real_inner_self_pos.mpr ha0
    nlinarith [mul_pos (sq_pos_of_pos ht) hapos,
      mul_nonneg (sq_nonneg t) hb, mul_nonneg (mul_nonneg ht.le ht0.le) hmono]
  · have hbpos : 0 < ⟪b, b⟫_ℝ := real_inner_self_pos.mpr hb0
    nlinarith [mul_pos (sq_pos_of_pos ht0) hbpos,
      mul_nonneg (sq_nonneg (1-t)) ha, mul_nonneg (mul_nonneg ht.le ht0.le) hmono]

/-- Distinct endpoint pairs in a monotone relation remain distinct at interior times. -/
theorem monotone_interpolated_sites_ne
    (x₀ x₁ y₀ y₁ : V)
    (hmono : 0 ≤ ⟪x₀ - x₁, y₀ - y₁⟫_ℝ)
    (hne : (x₀, y₀) ≠ (x₁, y₁))
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    (1-t) • x₀ + t • y₀ ≠ (1-t) • x₁ + t • y₁ := by
  have hdiff : x₀ - x₁ ≠ 0 ∨ y₀ - y₁ ≠ 0 := by
    by_contra h
    push Not at h
    apply hne
    exact Prod.ext (sub_eq_zero.mp h.1) (sub_eq_zero.mp h.2)
  have hn := monotone_interpolation_ne_zero (x₀-x₁) (y₀-y₁) hmono hdiff ht0 ht1
  intro heq
  apply hn
  rw [smul_sub, smul_sub]
  convert sub_eq_zero.mpr heq using 1
  abel

end Problem358

end

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem358
namespace FiniteCoupling

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The cost of a finite real-valued transport matrix. -/
def cost (c w : ι → κ → ℝ) : ℝ := ∑ i, ∑ j, w i j * c i j

/-- Optimality among nonnegative matrices with the same two marginals. -/
def IsOptimal (c w : ι → κ → ℝ) : Prop :=
  (∀ i j, 0 ≤ w i j) ∧
  ∀ q : ι → κ → ℝ, (∀ i j, 0 ≤ q i j) →
    (∀ i, ∑ j, q i j = ∑ j, w i j) →
    (∀ j, ∑ i, q i j = ∑ i, w i j) → cost c w ≤ cost c q

/-- Transfer mass from the diagonal corners to the off-diagonal corners. -/
def rectangleSwap (w : ι → κ → ℝ) (ε : ℝ) (i k : ι) (j l : κ)
    (u : ι) (v : κ) : ℝ :=
  w u v + ε * ((if u = i then 1 else 0) - (if u = k then 1 else 0)) *
    ((if v = l then 1 else 0) - (if v = j then 1 else 0))

omit [Fintype ι] in
lemma rectangleSwap_row (w : ι → κ → ℝ) (ε : ℝ) (i k : ι) (j l : κ) (u : ι) :
    ∑ v, rectangleSwap w ε i k j l u v = ∑ v, w u v := by
  simp [rectangleSwap, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]

omit [Fintype κ] in
lemma rectangleSwap_col (w : ι → κ → ℝ) (ε : ℝ) (i k : ι) (j l : κ) (v : κ) :
    ∑ u, rectangleSwap w ε i k j l u v = ∑ u, w u v := by
  simp [rectangleSwap, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.mul_sum, Finset.sum_sub_distrib]

omit [Fintype ι] [Fintype κ] in
lemma rectangleSwap_nonneg {w : ι → κ → ℝ} {ε : ℝ} {i k : ι} {j l : κ}
    (hw : ∀ u v, 0 ≤ w u v) (hε : 0 ≤ ε) (hij : ε ≤ w i j) (hkl : ε ≤ w k l)
    (hik : i ≠ k) (hjl : j ≠ l) : ∀ u v, 0 ≤ rectangleSwap w ε i k j l u v := by
  intro u v
  have huv := hw u v
  by_cases hui : u = i <;> by_cases huk : u = k <;>
    by_cases hvj : v = j <;> by_cases hvl : v = l <;>
    simp_all [rectangleSwap] <;> linarith [hw i l, hw k j]

lemma rectangleSwap_cost (c w : ι → κ → ℝ) (ε : ℝ) (i k : ι) (j l : κ) :
    cost c (rectangleSwap w ε i k j l) =
      cost c w + ε * (c i l + c k j - c i j - c k l) := by
  simp [cost, rectangleSwap, add_mul, sub_mul, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

/-- The two-point exchange inequality on the positive support of an optimal matrix. -/
lemma IsOptimal.cross_cost_le {c w : ι → κ → ℝ} (hopt : IsOptimal c w)
    {i k : ι} {j l : κ} (hij : 0 < w i j) (hkl : 0 < w k l) :
    c i j + c k l ≤ c i l + c k j := by
  by_cases hik : i = k
  · subst k
    linarith
  by_cases hjl : j = l
  · subst l
    linarith
  let ε : ℝ := min (w i j) (w k l)
  have hε : 0 < ε := lt_min hij hkl
  have hswap := hopt.2 (rectangleSwap w ε i k j l)
    (rectangleSwap_nonneg hopt.1 hε.le (min_le_left _ _) (min_le_right _ _) hik hjl)
    (rectangleSwap_row w ε i k j l) (rectangleSwap_col w ε i k j l)
  rw [rectangleSwap_cost] at hswap
  nlinarith

end FiniteCoupling

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The quadratic exchange inequality is exactly two-point monotonicity. -/
lemma inner_sub_nonneg_of_quadratic_cross {x x' y y' : F}
    (h : ‖x - y‖ ^ 2 + ‖x' - y'‖ ^ 2 ≤
      ‖x - y'‖ ^ 2 + ‖x' - y‖ ^ 2) :
    0 ≤ ⟪x - x', y - y'⟫ := by
  simp only [norm_sub_sq_real] at h
  simp only [inner_sub_left, inner_sub_right]
  linarith

/-- Positive entries of a finite quadratic optimal coupling are monotone. -/
lemma FiniteCoupling.IsOptimal.inner_nonneg
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {x : ι → F} {y : κ → F} {w : ι → κ → ℝ}
    (hopt : FiniteCoupling.IsOptimal (fun i j => ‖x i - y j‖ ^ 2) w)
    {i k : ι} {j l : κ} (hij : 0 < w i j) (hkl : 0 < w k l) :
    0 ≤ ⟪x i - x k, y j - y l⟫ :=
  inner_sub_nonneg_of_quadratic_cross (hopt.cross_cost_le hij hkl)

/-- A positive linear combination of two vectors with nonnegative inner product
can vanish only when both vectors vanish. -/
lemma eq_zero_of_pos_smul_add_smul_eq_zero {x y : F} {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hxy : 0 ≤ ⟪x, y⟫)
    (h : a • x + b • y = 0) : x = 0 ∧ y = 0 := by
  have hx := congrArg (fun z : F => ⟪z, x⟫) h
  have hy := congrArg (fun z : F => ⟪z, y⟫) h
  simp only [inner_add_left, real_inner_smul_left, inner_zero_left] at hx hy
  rw [real_inner_comm x y] at hx
  have hxx := real_inner_self_nonneg (x := x)
  have hyy := real_inner_self_nonneg (x := y)
  constructor
  · apply real_inner_self_nonpos.mp
    nlinarith [mul_nonneg hb.le hxy]
  · apply real_inner_self_nonpos.mp
    nlinarith [mul_nonneg ha.le hxy]

/-- Distinct endpoint pairs on a monotone relation cannot collide at interior time. -/
lemma interpolate_ne_of_inner_nonneg {x x' y y' : F} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1)
    (hxy : 0 ≤ ⟪x - x', y - y'⟫) (hne : (x, y) ≠ (x', y')) :
    (1 - t) • x + t • y ≠ (1 - t) • x' + t • y' := by
  intro heq
  have hzero : (1 - t) • (x - x') + t • (y - y') = 0 := by
    calc
      (1 - t) • (x - x') + t • (y - y') =
          ((1 - t) • x + t • y) - ((1 - t) • x' + t • y') := by
        simp only [smul_sub]
        abel
      _ = 0 := sub_eq_zero.mpr heq
  obtain ⟨hx, hy⟩ := eq_zero_of_pos_smul_add_smul_eq_zero
    (sub_pos.mpr ht1) ht0 hxy hzero
  exact hne (Prod.ext (sub_eq_zero.mp hx) (sub_eq_zero.mp hy))

end Problem358

end

noncomputable section
open scoped BigOperators InnerProductSpace

namespace Problem358
namespace FiniteCoupling

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
/-- A finite optimal coupling exists with any prescribed probability marginals. -/
theorem exists_optimal_with_marginals
    (a : I → ℝ) (b : J → ℝ) (c : I → J → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hasum : ∑ i, a i = 1) (hbsum : ∑ j, b j = 1) :
    ∃ p : I → J → ℝ,
      (∀ i, ∑ j, p i j = a i) ∧
      (∀ j, ∑ i, p i j = b j) ∧ IsOptimal c p := by
  obtain ⟨p, hp, hpr, hpc, hmin⟩ :=
    exists_minimal_finite_coupling a b c ha hb hasum hbsum
  refine ⟨p, hpr, hpc, hp, ?_⟩
  intro q hq hqr hqc
  exact hmin q hq (fun i => (hqr i).trans (hpr i))
    (fun j => (hqc j).trans (hpc j))

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The positive support of an optimal quadratic finite coupling has distinct
interpolated sites at every interior time, even when either endpoint marginal
contains repeated images across different coupling pairs. -/
theorem IsOptimal.interpolated_support_injective
    {x : I → V} {y : J → V} {p : I → J → ℝ}
    (hp : IsOptimal (fun i j => ‖x i - y j‖ ^ 2) p)
    (hx : Function.Injective x) (hy : Function.Injective y)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Function.Injective (fun q : {q : I × J // 0 < p q.1 q.2} =>
      (1-t) • x q.val.1 + t • y q.val.2) := by
  intro q r heq
  by_contra hne
  have hend : (x q.val.1, y q.val.2) ≠ (x r.val.1, y r.val.2) := by
    intro h
    apply hne
    apply Subtype.ext
    exact Prod.ext (hx (congrArg Prod.fst h)) (hy (congrArg Prod.snd h))
  exact monotone_interpolated_sites_ne _ _ _ _
    (hp.inner_nonneg q.property r.property) hend ht0 ht1 heq

/-- Finite quadratic transport admits a positive-support path with no collisions.
This packages the finite compactness and two-point exchange steps together. -/
theorem exists_optimal_noncolliding_path
    (a : I → ℝ) (b : J → ℝ) (x : I → V) (y : J → V)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hasum : ∑ i, a i = 1) (hbsum : ∑ j, b j = 1)
    (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ p : I → J → ℝ,
      (∀ i, ∑ j, p i j = a i) ∧
      (∀ j, ∑ i, p i j = b j) ∧
      IsOptimal (fun i j => ‖x i - y j‖ ^ 2) p ∧
      ∀ t : ℝ, 0 < t → t < 1 →
        Function.Injective (fun q : {q : I × J // 0 < p q.1 q.2} =>
          (1-t) • x q.val.1 + t • y q.val.2) := by
  obtain ⟨p, hpr, hpc, hopt⟩ := exists_optimal_with_marginals a b
    (fun i j => ‖x i - y j‖ ^ 2) ha hb hasum hbsum
  exact ⟨p, hpr, hpc, hopt,
    fun _ ht0 ht1 => hopt.interpolated_support_injective hx hy ht0 ht1⟩

end FiniteCoupling
end Problem358

end

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace Problem358
namespace PositiveFiniteCoupling

variable {ι : Type*} [Fintype ι]

/-- Retain only the strictly positive entries of a finite nonnegative weight family. -/
abbrev Support (w : ι → ℝ) := {i : ι // 0 < w i}

noncomputable instance supportFintype (w : ι → ℝ) : Fintype (Support w) :=
  by classical exact Subtype.fintype _

/-- Removing zero weights preserves every weighted real sum. -/
theorem sum_support_mul (w f : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i : Support w, w i * f i) = ∑ i, w i * f i := by
  classical
  have hzero : (∑ i : {i : ι // ¬ 0 < w i}, w i * f i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : w i = 0 := le_antisymm (le_of_not_gt i.property) (hw i)
    simp [hi]
  have h := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < w i)
    (fun i => w i * f i)
  simpa only [hzero, add_zero] using h

theorem sum_support (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    (∑ i : Support w, w i) = ∑ i, w i := by
  simpa using sum_support_mul w (fun _ => 1) hw

theorem support_nonempty (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hsum : ∑ i, w i = 1) : Nonempty (Support w) := by
  classical
  by_contra h
  have hz : ∀ i, w i = 0 := by
    intro i
    apply le_antisymm _ (hw i)
    by_contra hi
    exact h ⟨i, lt_of_not_ge hi⟩
  simp [hz] at hsum

variable {κ : Type*} [Fintype κ]

abbrev Pairs (w : ι → κ → ℝ) := Support (fun ij : ι × κ => w ij.1 ij.2)

theorem sum_pairs_mul (w c : ι → κ → ℝ) (hw : ∀ i j, 0 ≤ w i j) :
    (∑ p : Pairs w, w p.1.1 p.1.2 * c p.1.1 p.1.2) =
      ∑ i, ∑ j, w i j * c i j := by
  rw [sum_support_mul (fun p : ι × κ => w p.1 p.2)
    (fun p : ι × κ => c p.1 p.2) (fun p => hw p.1 p.2), Fintype.sum_prod_type]

theorem sum_pairs_eq_one (w : ι → κ → ℝ) (a : ι → ℝ)
    (hw : ∀ i j, 0 ≤ w i j) (hrow : ∀ i, ∑ j, w i j = a i)
    (ha : ∑ i, a i = 1) :
    (∑ p : Pairs w, w p.1.1 p.1.2) = 1 := by
  rw [sum_support (fun p : ι × κ => w p.1 p.2)
    (fun p => hw p.1 p.2), Fintype.sum_prod_type]
  simpa only [hrow] using ha

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

omit [Fintype ι] [Fintype κ] [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
/-- Injective endpoint site families give distinct positive coupling pairs. -/
theorem endpoint_pairs_injective {x : ι → F} {y : κ → F}
    (hx : Function.Injective x) (hy : Function.Injective y) (w : ι → κ → ℝ) :
    Function.Injective (fun p : Pairs w => (x p.1.1, y p.1.2)) := by
  intro p q hpq
  apply Subtype.ext
  exact Prod.ext (hx (congrArg Prod.fst hpq)) (hy (congrArg Prod.snd hpq))

/-- The positive pairs of an optimal quadratic matrix remain distinct at interior times. -/
theorem interpolated_sites_injective [DecidableEq ι] [DecidableEq κ]
    {x : ι → F} {y : κ → F} {w : ι → κ → ℝ}
    (hx : Function.Injective x) (hy : Function.Injective y)
    (hopt : FiniteCoupling.IsOptimal (fun i j => ‖x i - y j‖ ^ 2) w)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Function.Injective
      (fun p : Pairs w => (1-t) • x p.1.1 + t • y p.1.2) := by
  intro p q hpq
  by_contra hne
  apply interpolate_ne_of_inner_nonneg ht0 ht1
    (hopt.inner_nonneg p.property q.property) _ hpq
  exact fun heq => hne (endpoint_pairs_injective hx hy w heq)

/-- A finite quadratic optimal coupling, with zero entries removed, has positive
normalized weights and pairwise distinct interpolated sites for every interior time. -/
theorem exists_optimal_positive_pairs [DecidableEq ι] [DecidableEq κ]
    (a : ι → ℝ) (b : κ → ℝ) (x : ι → F) (y : κ → F)
    (ha : ∀ i, 0 ≤ a i) (hb : ∀ j, 0 ≤ b j)
    (hasum : ∑ i, a i = 1) (hbsum : ∑ j, b j = 1)
    (hx : Function.Injective x) (hy : Function.Injective y) :
    ∃ w : ι → κ → ℝ,
      (∀ i, ∑ j, w i j = a i) ∧
      (∀ j, ∑ i, w i j = b j) ∧
      FiniteCoupling.IsOptimal (fun i j => ‖x i - y j‖ ^ 2) w ∧
      (∑ p : Pairs w, w p.1.1 p.1.2) = 1 ∧
      ∀ t : ℝ, 0 < t → t < 1 → Function.Injective
        (fun p : Pairs w => (1-t) • x p.1.1 + t • y p.1.2) := by
  obtain ⟨w, hw, hrow, hcol, hmin⟩ :=
    exists_minimal_finite_coupling a b (fun i j => ‖x i - y j‖ ^ 2)
      ha hb hasum hbsum
  have hopt : FiniteCoupling.IsOptimal (fun i j => ‖x i - y j‖ ^ 2) w := by
    refine ⟨hw, ?_⟩
    intro q hq hqr hqc
    exact hmin q hq (fun i => (hqr i).trans (hrow i))
      (fun j => (hqc j).trans (hcol j))
  exact ⟨w, hrow, hcol, hopt, sum_pairs_eq_one w a hw hrow hasum,
    fun _ ht0 ht1 => interpolated_sites_injective hx hy hopt ht0 ht1⟩

end PositiveFiniteCoupling
end Problem358

end

end OAI
