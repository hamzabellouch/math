import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Abel
import Std

namespace OAI

section

/-!
# Energy after merging a bounded number of frequencies

This finite ordered-ring theorem supplies the Cauchy–Schwarz step in (A.10).
Its fiber-cardinality hypothesis is explicit.
-/

namespace UniqueGamesTheorem.Appendix.FiberEnergy

open scoped BigOperators

variable {α β R : Type*} [Fintype β] [DecidableEq β] [CommRing R] [LinearOrder R]
  [IsStrictOrderedRing R]

/-- The energy of a sum of merged coefficients is bounded by the largest
fiber size times the original coefficient energy. Signs and cancellations
are unrestricted; no injectivity assumption is made. -/
theorem finite_fiber_energy (s : Finset α) (compress : α → β) (a : α → R)
    (bound : R) (hbound : ∀ z,
      ((s.filter (fun y => compress y = z)).card : R) ≤ bound) :
    (∑ z, (∑ y ∈ s.filter (fun y => compress y = z), a y) ^ 2) ≤
      bound * ∑ y ∈ s, a y ^ 2 := by
  classical
  have hlocal (z : β) :
      (∑ y ∈ s.filter (fun y => compress y = z), a y) ^ 2 ≤
        bound * ∑ y ∈ s.filter (fun y => compress y = z), a y ^ 2 := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq
      (s.filter (fun y => compress y = z)) (fun _ => (1 : R)) a
    calc
      _ ≤ ((s.filter (fun y => compress y = z)).card : R) *
          ∑ y ∈ s.filter (fun y => compress y = z), a y ^ 2 := by simpa using hc
      _ ≤ _ := mul_le_mul_of_nonneg_right (hbound z)
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  calc
    _ ≤ ∑ z, bound * ∑ y ∈ s.filter (fun y => compress y = z), a y ^ 2 :=
      Finset.sum_le_sum (fun z _ => hlocal z)
    _ = bound * ∑ y ∈ s, a y ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_fiberwise]

end UniqueGamesTheorem.Appendix.FiberEnergy

end

section

/-! Finite Gram-energy estimates used in Lemma A.1. -/
namespace UniqueGamesTheorem.Appendix.F1Gram
open scoped BigOperators

/-- The squared entries of a Gram matrix are bounded by the squared total
energy of its underlying rows. This is a pairwise Cauchy–Schwarz argument. -/
theorem gram_energy_le {R C : Type*} [Fintype R] [Fintype C] (p : R → C → ℝ) :
    (∑ r, ∑ s, (∑ c, p r c * p s c)^2) ≤
      (∑ r, ∑ c, p r c^2)^2 := by
  classical
  let e : R → ℝ := fun r => ∑ c, p r c^2
  calc
    _ ≤ ∑ r, ∑ s, e r * e s := by
      apply Finset.sum_le_sum
      intro r _
      apply Finset.sum_le_sum
      intro s _
      exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (p r) (p s)
    _ = (∑ r, e r) * (∑ s, e s) := (Finset.sum_mul_sum _ _ _ _).symm
    _ = (∑ r, ∑ c, p r c^2)^2 := (pow_two _).symm

theorem sum_subtype_eq {A : Type*} [Fintype A] (P : A → Prop)
    [DecidablePred P] (f : A → ℝ) :
    (∑ x : {x // P x}, f x) = ∑ x : A, if P x then f x else 0 := by
  classical
  calc
    _ = ∑ x ∈ Finset.univ.filter P, f x := by
      refine Finset.sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
      · intro x _
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, x.property⟩
      · intro x _ y _ h
        exact Subtype.ext h
      · intro y hy
        exact ⟨⟨y, (Finset.mem_filter.mp hy).2⟩, Finset.mem_univ _, rfl⟩
      · intro x _
        rfl
    _ = _ := by rw [Finset.sum_filter]

theorem sum_comp_le {A B : Type*} [Fintype A] [Fintype B] (e : A → B)
    (he : Function.Injective e) (f : B → ℝ) (hf : ∀ b, 0 ≤ f b) :
    (∑ a, f (e a)) ≤ ∑ b, f b := by
  classical
  calc
    _ = ∑ b ∈ Finset.univ.image e, f b :=
      (Finset.sum_image (fun a _ b _ h => he h)).symm
    _ ≤ ∑ b ∈ Finset.univ, f b := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun b _ _ => hf b)

end UniqueGamesTheorem.Appendix.F1Gram

end

section

namespace UniqueGamesTheorem.Appendix.Induction

/-- The corrected outer-order cutoff (A.14), with natural subtraction explicit. -/
theorem outer_order_cutoff (d i j k a b : Nat)
    (ha : i + k ≤ a) (hb : j + k ≤ b) (ht : i + j + k ≤ d)
    (ho : (a - i - k) + (b - j - k) ≤ d - (i + j + k)) :
    a + b ≤ d + k := by
  omega

/-- Each complementary-space dimension is at most the original degree. -/
theorem complement_dimension_bounds (d i j k a b : Nat)
    (ha : i + k ≤ a) (hb : j + k ≤ b) (h : a + b ≤ d + k) :
    a - i ≤ d ∧ b - j ≤ d := by
  omega

/-- Recombination preserves the required derivative degree cutoff. -/
theorem recombined_order_cutoff (d k a b : Nat)
    (ha : k ≤ a) (hb : k ≤ b) (h : a + b ≤ d + k) :
    (a - k) + (b - k) + k ≤ d := by
  omega

theorem square_remainder_budget (d t : Nat) (ht : t ≤ d) :
    (d - t) * (d - t) + d * t ≤ d * d := by
  have hm := Nat.mul_le_mul_left (d - t) (Nat.sub_le d t)
  have hs : d - t + t = d := by omega
  have he : (d - t) * d + t * d = d * d := by
    rw [← Nat.add_mul, hs]
  rw [Nat.mul_comm d t]
  omega

/-- The exponent inequality preceding (A.16), with negative exponents moved
to the left side so natural subtraction cannot hide an invalid inequality. -/
theorem induction_exponent_budget (d t k : Nat) (ht : t ≤ d) (hk : k ≤ t) :
    100 * ((d - t) * (d - t)) + 27 * (d * t) + 6 * (d * k) +
      63 * (d * t) + 4 * (d * k) ≤ 100 * (d * d) := by
  have hs := Nat.mul_le_mul_left 100 (square_remainder_budget d t ht)
  have hm := Nat.mul_le_mul_left d hk
  omega

theorem antecedent_exponent_budget (d i j k t : Nat)
    (ht : t = i + j + k) (hd : t ≤ d) :
    d * (i + j) + 2 * (d * k) + k * k ≤ 3 * (d * t) := by
  have hk : k ≤ d := by omega
  have hm := Nat.mul_le_mul_right k hk
  have he : d * t = d * (i + j) + d * k := by
    rw [ht, Nat.mul_add]
  omega

/-- The factor from the fourth-power triangle inequality fits inside the
12d(i+j) budget used before (A.13). -/
theorem first_triangle_exponent_budget (d i j : Nat) (hi : i ≤ d) :
    7 * (d * (i + j)) + 3 * (i * j) ≤ 12 * (d * (i + j)) := by
  have hm := Nat.mul_le_mul_right j hi
  have he : d * (i + j) = d * i + d * j := Nat.mul_add d i j
  omega

/-- The derivative order t is at least half the original pair order. -/
theorem initial_order_bound (i j k : Nat) (hi : k ≤ i) (hj : k ≤ j) :
    i + j ≤ 2 * (i + j - k) := by
  omega

/-- For positive k the geometric-series exponent has at least d of slack. -/
theorem positive_rank_geometric_slack (d k : Nat) (hk : 1 ≤ k) :
    31 * (d * (k + 1)) + d ≤ 63 * (d * k) := by
  have hm := Nat.mul_le_mul_left d hk
  have he : d * (k + 1) = d * k + d := by simp [Nat.mul_add]
  omega

/-- The rank-dependent decay in (A.16) contains the corrected 8dk weight. -/
theorem corrected_weight_exponent (d k : Nat) :
    31 * (d * (k + 1)) + 4 * (d * k) =
      31 * d + 27 * (d * k) + 8 * (d * k) := by
  simp only [Nat.mul_add, Nat.mul_one]
  omega

/-- When B′ plus the prescribed kernel spans the domain, the map on B′
determines its extension. Thus fixing image and kernel in the antecedent
count leaves no additional induced-isomorphism choice. -/
theorem extension_unique {B V : Type} [Add B] [Add V]
    (zero : V) (X₁ X₂ : B → V) (B' K : B → Prop)
    (right_zero : ∀ v : V, v + zero = v)
    (add₁ : ∀ x y, X₁ (x + y) = X₁ x + X₁ y)
    (add₂ : ∀ x y, X₂ (x + y) = X₂ x + X₂ y)
    (span : ∀ x, ∃ b z, B' b ∧ K z ∧ x = b + z)
    (agree : ∀ b, B' b → X₁ b = X₂ b)
    (kill₁ : ∀ z, K z → X₁ z = zero)
    (kill₂ : ∀ z, K z → X₂ z = zero) : X₁ = X₂ := by
  funext x
  obtain ⟨b, z, hb, hz, hx⟩ := span x
  rw [hx, add₁, add₂, kill₁ z hz, kill₂ z hz, right_zero, right_zero]
  exact agree b hb

end UniqueGamesTheorem.Appendix.Induction

end

section

namespace UniqueGamesTheorem.Appendix.Level

/-- The unselected multiplier in factored form, after multiplying numerator
and denominator by `2^(2*r)`. Selected characters have multiplier one. -/
def rankFilter (d r : Nat) (selected : Bool) : Rat :=
  if selected then 1 else
    (((2 : Rat) ^ r - 2 ^ d) * (2 ^ r - 2 ^ (d - 1))) / ((2 : Rat) ^ r) ^ 2

theorem filter_polynomial_algebra (q x y : Rat) (hq : q ≠ 0) :
    (q - x) * (q - y) / q ^ 2 = 1 - (x + y) / q + x * y / q ^ 2 := by
  grind

theorem rankFilter_selected (d r : Nat) : rankFilter d r true = 1 := by
  simp [rankFilter]

theorem rankFilter_zero_at_d (d : Nat) : rankFilter d d false = 0 := by
  simp only [rankFilter, Bool.false_eq_true, ↓reduceIte]
  grind

theorem rankFilter_zero_at_pred (d : Nat) : rankFilter d (d - 1) false = 0 := by
  simp only [rankFilter, Bool.false_eq_true, ↓reduceIte]
  grind

/-- Only ranks `d-1` and `d` can restrict to rank `d-1`; no degree
bound on the original function is needed. -/
theorem only_two_source_ranks {d r s : Nat} (hd : 1 ≤ d)
    (hlo : s ≤ r) (hhi : r ≤ s + 1) (hs : s + 1 = d) :
    r = d ∨ r = d - 1 := by
  omega

/-- Selected characters lose exactly one rank. On an unselected character,
the two roots of the filter remove every possible unwanted contribution. -/
theorem rank_filter_character {d r s : Nat} (hd : 1 ≤ d)
    (selected : Bool) (c : Rat)
    (hlo : s ≤ r) (hhi : r ≤ s + 1)
    (hselected : selected = true → r = s + 1) :
    (if selected then if r = d then c else 0 else 0) =
      (if s + 1 = d then rankFilter d r selected * c else 0) := by
  cases selected with
  | true =>
    have hr := hselected rfl
    simp [rankFilter, hr]
  | false =>
    by_cases hs : s + 1 = d
    · have hr := only_two_source_ranks hd hlo hhi hs
      rcases hr with hr | hr
      · simp [hs, hr, rankFilter_zero_at_d]
      · simp [hs, hr, rankFilter_zero_at_pred]
    · simp [hs]

/-- A finite merged coefficient. `phase` can incorporate a translation
character and the indicator of one restriction fiber. -/
def mergedCoefficient {α : Type} (indices : List α)
    (phase coefficient : α → Rat) : Rat :=
  (indices.map (fun x => phase x * coefficient x)).sum

/-- The character identity survives arbitrary merging, signs, and
cancellation. No injectivity of the restriction of frequencies is assumed. -/
theorem rank_filter_commutes_with_merge {α : Type} (indices : List α)
    (d : Nat) (hd : 1 ≤ d) (rank restrictedRank : α → Nat)
    (selected : α → Bool) (phase coefficient : α → Rat)
    (hlo : ∀ x, restrictedRank x ≤ rank x)
    (hhi : ∀ x, rank x ≤ restrictedRank x + 1)
    (hselected : ∀ x, selected x = true → rank x = restrictedRank x + 1) :
    mergedCoefficient indices phase
        (fun x => if selected x then if rank x = d then coefficient x else 0 else 0) =
      mergedCoefficient indices phase
        (fun x => if restrictedRank x + 1 = d
          then rankFilter d (rank x) (selected x) * coefficient x else 0) := by
  unfold mergedCoefficient
  congr 1
  apply List.map_congr_left
  intro x _
  exact congrArg (fun c : Rat => phase x * c)
    (rank_filter_character hd (selected x) (coefficient x) (hlo x) (hhi x)
      (hselected x))

theorem higher_ranks_cannot_contaminate {d r s : Nat}
    (hhi : r ≤ s + 1) (hr : d < r) : s + 1 ≠ d := by
  omega

/-- Arithmetic in the iterated globality parameter
`4^k * 2^(4*k*d - 2*k*(k-1))`. -/
theorem iterated_globality_exponent {d k : Nat} (hd : 1 ≤ d) (hk : k ≤ d) :
    2 * k + 4 * k * d - 2 * k * (k - 1) ≤ 10 * d * d := by
  have hkd : k * d ≤ d * d := Nat.mul_le_mul_right d hk
  have hdd : d ≤ d * d := by
    have := Nat.mul_le_mul_left d hd
    simpa using this
  have hbasic : 2 * k + 4 * k * d ≤ 6 * d * d := by
    grind
  grind

theorem successor_le_two_pow (d : Nat) : d + 1 ≤ 2 ^ d := by
  induction d with
  | zero => decide
  | succ d ih =>
    rw [Nat.pow_succ]
    omega

/-- A deliberately coarse bound for the number of dimension-indexed
selector choices. The geometric subspace count is an explicit hypothesis. -/
theorem selector_multiplicity_bound {d count : Nat} (hd : 1 ≤ d)
    (hcount : count ≤ (d + 1) ^ 2 * 2 ^ (d * d)) :
    count ≤ 2 ^ (3 * d * d) := by
  have hs := Nat.pow_le_pow_left (successor_le_two_pow d) 2
  have hdd : d ≤ d * d := by
    have := Nat.mul_le_mul_left d hd
    simpa using this
  calc
    count ≤ (d + 1) ^ 2 * 2 ^ (d * d) := hcount
    _ ≤ (2 ^ d) ^ 2 * 2 ^ (d * d) := Nat.mul_le_mul_right _ hs
    _ = 2 ^ (d * 2 + d * d) := by rw [← Nat.pow_mul, ← Nat.pow_add]
    _ ≤ 2 ^ (3 * d * d) := Nat.pow_le_pow_right (by decide) (by grind)

/-- The final fourth-root exponent has the advertised slack. -/
theorem final_exponent_slack (d : Nat) : 113 * d * d ≤ 4 * (30 * d * d) := by
  grind

end UniqueGamesTheorem.Appendix.Level

namespace UniqueGamesTheorem.Appendix.Level.LinearRank

open Module LinearMap
attribute [local instance] Classical.propDecidable

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V] [FiniteDimensional K W] [FiniteDimensional K V]

/-- Restriction in the domain and quotient in the codomain, as actual
linear maps. This is the Fourier-frequency map of an affine restriction. -/
def compress (A : Submodule K V) (B : Submodule K W) (Y : W →ₗ[K] V) :
    B →ₗ[K] V ⧸ A := A.mkQ.comp (Y.comp B.subtype)

theorem finrank_comap_subtype_le (A B : Submodule K V) :
    finrank K (A.comap B.subtype) ≤ finrank K A := by
  rw [← Submodule.finrank_map_subtype_eq B (A.comap B.subtype),
    Submodule.map_comap_subtype]
  exact Submodule.finrank_mono inf_le_right

theorem quotient_rank_bounds (A : Submodule K V) (Y : W →ₗ[K] V) :
    finrank K (range (A.mkQ.comp Y)) ≤ finrank K (range Y) ∧
      finrank K (range Y) ≤ finrank K (range (A.mkQ.comp Y)) + finrank K A := by
  have h := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
  have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
    simp only [range_comp, Submodule.range_subtype]
  rw [hr, ker_comp, Submodule.ker_mkQ] at h
  have hk := finrank_comap_subtype_le A (range Y)
  omega

omit [FiniteDimensional K V] in
theorem quotient_rank_selected (A : Submodule K V) (Y : W →ₗ[K] V)
    (hA : A ≤ range Y) :
    finrank K (range (A.mkQ.comp Y)) + finrank K A = finrank K (range Y) := by
  have h := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
  have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
    simp only [range_comp, Submodule.range_subtype]
  rw [hr, ker_comp, Submodule.ker_mkQ,
    (Submodule.comapSubtypeEquivOfLe hA).finrank_eq] at h
  exact h

omit [FiniteDimensional K V] in
theorem domain_rank_bounds (B : Submodule K W) (Y : W →ₗ[K] V) :
    finrank K (range (Y.comp B.subtype)) ≤ finrank K (range Y) ∧
      finrank K (range Y) ≤
        finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) := by
  have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
  have h₂ := Y.finrank_range_add_finrank_ker
  have h₃ := B.finrank_quotient_add_finrank
  rw [ker_comp] at h₁
  have hk := finrank_comap_subtype_le (ker Y) B
  have hr : finrank K (range (Y.comp B.subtype)) ≤ finrank K (range Y) := by
    apply Submodule.finrank_mono
    exact LinearMap.range_comp_le_range _ _
  omega

omit [FiniteDimensional K V] in
theorem domain_rank_selected (B : Submodule K W) (Y : W →ₗ[K] V)
    (hB : ker Y ≤ B) :
    finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
  have h₂ := Y.finrank_range_add_finrank_ker
  have h₃ := B.finrank_quotient_add_finrank
  rw [ker_comp, (Submodule.comapSubtypeEquivOfLe hB).finrank_eq] at h₁
  omega

omit [FiniteDimensional K V] in
theorem hybrid_rank_loss (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) (hA : A ≤ range Y) (hB : A.comap Y ≤ B) :
    finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) =
      finrank K (range Y) := by
  have hquot := quotient_rank_selected A Y hA
  have hdom := domain_rank_selected B (A.mkQ.comp Y) (by
    simpa only [ker_comp, Submodule.ker_mkQ] using hB)
  have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
  rw [hc] at hdom
  omega

/-- Equality in the dimension bound for a subspace intersection forces
the original subspace to lie in the restricting subspace. -/
theorem finrank_comap_subtype_eq_iff (A B : Submodule K V) :
    finrank K (A.comap B.subtype) = finrank K A ↔ A ≤ B := by
  constructor
  · intro h
    have hdim := Submodule.finrank_map_subtype_eq B (A.comap B.subtype)
    rw [Submodule.map_comap_subtype, h] at hdim
    have heq : B ⊓ A = A := Submodule.eq_of_le_of_finrank_eq inf_le_right hdim
    calc
      A = B ⊓ A := heq.symm
      _ ≤ B := inf_le_left
  · intro h
    exact (Submodule.comapSubtypeEquivOfLe h).finrank_eq

theorem quotient_rank_equality_iff (A : Submodule K V) (Y : W →ₗ[K] V) :
    finrank K (range (A.mkQ.comp Y)) + finrank K A = finrank K (range Y) ↔
      A ≤ range Y := by
  constructor
  · intro heq
    have hn := (A.mkQ.comp (range Y).subtype).finrank_range_add_finrank_ker
    have hr : range (A.mkQ.comp (range Y).subtype) = range (A.mkQ.comp Y) := by
      simp only [range_comp, Submodule.range_subtype]
    rw [hr, ker_comp, Submodule.ker_mkQ] at hn
    apply (finrank_comap_subtype_eq_iff A (range Y)).mp
    omega
  · exact quotient_rank_selected A Y

omit [FiniteDimensional K V] in
theorem domain_rank_equality_iff (B : Submodule K W) (Y : W →ₗ[K] V) :
    finrank K (range (Y.comp B.subtype)) + finrank K (W ⧸ B) =
      finrank K (range Y) ↔ ker Y ≤ B := by
  constructor
  · intro heq
    have h₁ := (Y.comp B.subtype).finrank_range_add_finrank_ker
    have h₂ := Y.finrank_range_add_finrank_ker
    have h₃ := B.finrank_quotient_add_finrank
    rw [ker_comp] at h₁
    apply (finrank_comap_subtype_eq_iff (ker Y) B).mp
    omega
  · exact domain_rank_selected B Y

/-- Every genuine restriction loses at most its order in Fourier rank. -/
theorem compression_rank_bounds (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) :
    finrank K (range (compress A B Y)) ≤ finrank K (range Y) ∧
      finrank K (range Y) ≤
        finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) := by
  have hq := quotient_rank_bounds A Y
  have hd := domain_rank_bounds B (A.mkQ.comp Y)
  have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
  rw [hc] at hd
  omega

theorem hybrid_rank_loss_iff (A : Submodule K V) (B : Submodule K W)
    (Y : W →ₗ[K] V) :
    finrank K (range (compress A B Y)) + finrank K A + finrank K (W ⧸ B) =
      finrank K (range Y) ↔ A ≤ range Y ∧ A.comap Y ≤ B := by
  constructor
  · intro heq
    have hq := quotient_rank_bounds A Y
    have hd := domain_rank_bounds B (A.mkQ.comp Y)
    have hc : (A.mkQ.comp Y).comp B.subtype = compress A B Y := rfl
    rw [hc] at hd
    constructor
    · apply (quotient_rank_equality_iff A Y).mp
      omega
    · have he : finrank K (range ((A.mkQ.comp Y).comp B.subtype)) +
          finrank K (W ⧸ B) = finrank K (range (A.mkQ.comp Y)) := by
        rw [hc]
        omega
      have hk := (domain_rank_equality_iff B (A.mkQ.comp Y)).mp he
      simpa only [ker_comp, Submodule.ker_mkQ] using hk
  · rintro ⟨hA, hB⟩
    exact hybrid_rank_loss A B Y hA hB

/-- Instantiation of (A.17)'s rank filter for quotient by an actual line.
The only dimension hypothesis is the line's dimension; no rank cutoff is
imposed on the original map `Y`. -/
theorem line_rank_filter (A : Submodule K V) (Y : W →ₗ[K] V)
    (hline : finrank K A = 1) (d : Nat) (hd : 1 ≤ d) (c : Rat) :
    (if A ≤ range Y then
      if finrank K (range Y) = d then c else 0 else 0) =
      (if finrank K (range (A.mkQ.comp Y)) + 1 = d then
        UniqueGamesTheorem.Appendix.Level.rankFilter d (finrank K (range Y))
          (decide (A ≤ range Y)) * c else 0) := by
  classical
  have hb := quotient_rank_bounds A Y
  have hhi : finrank K (range Y) ≤ finrank K (range (A.mkQ.comp Y)) + 1 := by
    simpa only [hline] using hb.2
  have hs : decide (A ≤ range Y) = true →
      finrank K (range Y) = finrank K (range (A.mkQ.comp Y)) + 1 := by
    intro h
    have hl := quotient_rank_selected A Y (of_decide_eq_true h)
    omega
  simpa only [decide_eq_true_eq] using
    UniqueGamesTheorem.Appendix.Level.rank_filter_character hd (decide (A ≤ range Y)) c hb.1 hhi hs

omit [FiniteDimensional K V] in
/-- The dual order-one instance: restriction to an actual hyperplane. -/
theorem hyperplane_rank_filter (B : Submodule K W) (Y : W →ₗ[K] V)
    (hhyperplane : finrank K (W ⧸ B) = 1) (d : Nat) (hd : 1 ≤ d) (c : Rat) :
    (if ker Y ≤ B then
      if finrank K (range Y) = d then c else 0 else 0) =
      (if finrank K (range (Y.comp B.subtype)) + 1 = d then
        UniqueGamesTheorem.Appendix.Level.rankFilter d (finrank K (range Y))
          (decide (ker Y ≤ B)) * c else 0) := by
  classical
  have hb := domain_rank_bounds B Y
  have hhi : finrank K (range Y) ≤ finrank K (range (Y.comp B.subtype)) + 1 := by
    simpa only [hhyperplane] using hb.2
  have hs : decide (ker Y ≤ B) = true →
      finrank K (range Y) = finrank K (range (Y.comp B.subtype)) + 1 := by
    intro h
    have hl := domain_rank_selected B Y (of_decide_eq_true h)
    omega
  simpa only [decide_eq_true_eq] using
    UniqueGamesTheorem.Appendix.Level.rank_filter_character hd (decide (ker Y ≤ B)) c hb.1 hhi hs

end UniqueGamesTheorem.Appendix.Level.LinearRank

end

section

/-!
# Rank-additive pairs of linear maps

The rank-additive selector in Appendix A.1 has a concrete geometric meaning:
the two image spaces are disjoint and the two kernels span the domain. These
lemmas apply over any field and arbitrary finite dimensions, in particular
over `ZMod 2` with the second map equal to `Y + X`.
-/

namespace UniqueGamesTheorem.Appendix.RankAdditivity

open Module LinearMap

variable {K W V : Type*} [Field K] [AddCommGroup W] [AddCommGroup V]
  [Module K W] [Module K V]

/-- Disjoint images prevent cancellation between the two map values. -/
theorem ker_add_of_disjoint (f g : W →ₗ[K] V)
    (h : Disjoint (LinearMap.range f) (LinearMap.range g)) :
    LinearMap.ker (f + g) = LinearMap.ker f ⊓ LinearMap.ker g := by
  ext w
  constructor
  · intro hw
    have hsum : f w + g w = 0 := hw
    have hf : f w = 0 := by
      apply Submodule.disjoint_def.mp h (f w)
      · exact ⟨w, rfl⟩
      · exact ⟨-w, by simpa only [map_neg] using (eq_neg_of_add_eq_zero_left hsum).symm⟩
    have hg : g w = 0 := by simpa only [hf, zero_add] using hsum
    exact ⟨hf, hg⟩
  · rintro ⟨hf, hg⟩
    change f w + g w = 0
    change f w = 0 at hf
    change g w = 0 at hg
    rw [hf, hg, add_zero]

variable [FiniteDimensional K W]

/-- The exact rank-additivity criterion used to define `X ⪯ Y` in Appendix A.1. -/
theorem finrank_add_eq_iff (f g : W →ₗ[K] V) :
    finrank K (LinearMap.range (f + g)) =
        finrank K (LinearMap.range f) + finrank K (LinearMap.range g) ↔
      Disjoint (LinearMap.range f) (LinearMap.range g) ∧
        LinearMap.ker f ⊔ LinearMap.ker g = ⊤ := by
  have hf := f.finrank_range_add_finrank_ker
  have hg := g.finrank_range_add_finrank_ker
  have hfg := (f + g).finrank_range_add_finrank_ker
  have hker := (LinearMap.ker f).finrank_sup_add_finrank_inf_eq (LinearMap.ker g)
  constructor
  · intro hrank
    have hle := Submodule.finrank_mono (LinearMap.range_add_le f g)
    have himage := (LinearMap.range f).finrank_sup_add_finrank_inf_eq (LinearMap.range g)
    have hinf : finrank K (LinearMap.range f ⊓ LinearMap.range g : Submodule K V) = 0 := by
      omega
    have hd : Disjoint (LinearMap.range f) (LinearMap.range g) := by
      exact disjoint_iff.mpr (Submodule.finrank_eq_zero.mp hinf)
    refine ⟨hd, ?_⟩
    have heq := ker_add_of_disjoint f g hd
    rw [heq] at hfg
    apply Submodule.eq_top_of_finrank_eq
    omega
  · rintro ⟨hd, htop⟩
    rw [ker_add_of_disjoint f g hd] at hfg
    rw [htop, finrank_top] at hker
    omega

/-- The left image is contained in the total image for a rank-additive pair. -/
theorem range_left_le_range_add (f g : W →ₗ[K] V)
    (h : finrank K (LinearMap.range (f + g)) =
      finrank K (LinearMap.range f) + finrank K (LinearMap.range g)) :
    LinearMap.range f ≤ LinearMap.range (f + g) := by
  have hk := ((finrank_add_eq_iff f g).mp h).2
  intro v hv
  have hp : (v, (0 : V)) ∈ (LinearMap.range f).prod (LinearMap.range g) :=
    ⟨hv, Submodule.zero_mem _⟩
  rw [← LinearMap.range_prod_eq hk] at hp
  rcases hp with ⟨w, hw⟩
  have hwf : f w = v := congrArg Prod.fst hw
  have hwg : g w = 0 := congrArg Prod.snd hw
  refine ⟨w, ?_⟩
  change f w + g w = v
  rw [hwf, hwg, add_zero]

/-- The total kernel is contained in the left kernel for a rank-additive pair. -/
theorem ker_add_le_ker_left (f g : W →ₗ[K] V)
    (h : finrank K (LinearMap.range (f + g)) =
      finrank K (LinearMap.range f) + finrank K (LinearMap.range g)) :
    LinearMap.ker (f + g) ≤ LinearMap.ker f := by
  rw [ker_add_of_disjoint f g ((finrank_add_eq_iff f g).mp h).1]
  exact inf_le_left

def RankBelow (X Y : W →ₗ[K] V) : Prop :=
  finrank K (LinearMap.range Y) =
    finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X))

omit [FiniteDimensional K W] in
theorem add_remainder (X Y : W →ₗ[K] V) : X + (Y - X) = Y := by
  rw [add_comm X, sub_add_cancel]

theorem rankBelow_iff (X Y : W →ₗ[K] V) :
    RankBelow X Y ↔
      Disjoint (LinearMap.range X) (LinearMap.range (Y - X)) ∧
        LinearMap.ker X ⊔ LinearMap.ker (Y - X) = ⊤ := by
  have h := finrank_add_eq_iff X (Y - X)
  rw [add_remainder] at h
  exact h

theorem range_le_of_rankBelow (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.range X ≤ LinearMap.range Y := by
  have h' : finrank K (LinearMap.range (X + (Y - X))) =
      finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X)) := by
    rw [add_remainder]
    exact h
  simpa only [add_remainder] using range_left_le_range_add X (Y - X) h'

theorem ker_le_of_rankBelow (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.ker Y ≤ LinearMap.ker X := by
  have h' : finrank K (LinearMap.range (X + (Y - X))) =
      finrank K (LinearMap.range X) + finrank K (LinearMap.range (Y - X)) := by
    rw [add_remainder]
    exact h
  simpa only [add_remainder] using ker_add_le_ker_left X (Y - X) h'

theorem range_remainder_eq_range_on_kernel (X Y : W →ₗ[K] V) (h : RankBelow X Y) :
    LinearMap.range (Y - X) = LinearMap.range (Y.domRestrict (LinearMap.ker X)) := by
  have hc := ((rankBelow_iff X Y).mp h).2
  apply le_antisymm
  · rintro v ⟨w, hw⟩
    have ht : w ∈ LinearMap.ker X ⊔ LinearMap.ker (Y - X) := by rw [hc]; trivial
    rcases Submodule.mem_sup.mp ht with ⟨k, hk, j, hj, hkj⟩
    have hzk : (Y - X) k = (Y - X) w := by
      rw [← hkj, map_add, show (Y - X) j = 0 from hj, add_zero]
    refine ⟨⟨k, hk⟩, ?_⟩
    change Y k = v
    calc
      Y k = (Y - X) k := by
        change Y k = Y k - X k
        rw [show X k = 0 from hk, sub_zero]
      _ = (Y - X) w := hzk
      _ = v := hw
  · rintro v ⟨w, hw⟩
    refine ⟨(w : W), ?_⟩
    change Y w - X w = v
    rw [show X w = 0 from w.property, sub_zero]
    exact hw

theorem mem_ker_of_apply_mem_range_remainder (X Y : W →ₗ[K] V)
    (h : RankBelow X Y) (w : W) (hw : Y w ∈ LinearMap.range (Y - X)) :
    w ∈ LinearMap.ker X := by
  have hd := ((rankBelow_iff X Y).mp h).1
  have hz : (Y - X) w ∈ LinearMap.range (Y - X) := ⟨w, rfl⟩
  have hx : X w ∈ LinearMap.range (Y - X) := by
    have hs := (LinearMap.range (Y - X)).sub_mem hw hz
    have heq : Y w - (Y - X) w = X w := by
      simp only [LinearMap.sub_apply]
      abel
    exact heq ▸ hs
  exact Submodule.disjoint_def.mp hd (X w) ⟨w, rfl⟩ hx

end UniqueGamesTheorem.Appendix.RankAdditivity

end

end OAI
