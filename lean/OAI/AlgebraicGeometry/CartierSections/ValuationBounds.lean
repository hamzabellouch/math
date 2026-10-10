import OAI.AlgebraicGeometry.CartierSections.RegularJets
import Mathlib.RingTheory.Valuation.Basic

namespace OAI

/-!
# Valuation bounds for isolated jets

The boundary monomial ideal controls valuations of remainders. In particular,
the valuation of an isolated jet equals its least weight, and initial weights
bound every valuation with the prescribed boundary-coordinate values below.
-/

open scoped BigOperators

namespace CartierSections

section Basic
variable {A : Type*} [CommRing A]

theorem valuation_unit_zero (v : AddValuation A ENNReal) {u : A} (hu : IsUnit u) : v u = 0 := by
  obtain ⟨b, hb⟩ := hu.exists_left_inv
  have h : v b + v u = 0 := by rw [← v.map_mul, hb, v.map_one]
  exact (add_eq_zero.mp h).2

theorem valuation_prod (v : AddValuation A ENNReal) {ι : Type*} (s : Finset ι) (f : ι → A) :
    v (∏ i ∈ s, f i) = ∑ i ∈ s, v (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, v.map_mul, ih]

/-- The strict positive-threshold ideal of a nonnegative additive valuation. -/
def strictValuationIdeal (v : AddValuation A ENNReal) (t : ℝ) : Ideal A where
  carrier := {f | ENNReal.ofReal t < v f}
  zero_mem' := by simp
  add_mem' := fun hf hg => v.map_lt_add hf hg
  smul_mem' := by
    intro a f hf
    change ENNReal.ofReal t < v (a * f)
    rw [v.map_mul]
    exact hf.trans_le (le_add_left le_rfl)
end Basic

section MonomialValue
variable {k A ι : Type*} [Field k] [CommRing A] [Fintype ι]
  [Algebra (MvPolynomial ι k) A]

/-- Only the boundary-coordinate values are used; the transverse weights are
allowed to vanish even when the original valuation is positive on them. -/
theorem valuation_boundary_monomial (v : AddValuation A ENNReal)
    (B : Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hz : ∀ i ∈ B, v (algebraMap (MvPolynomial ι k) A (MvPolynomial.X i)) = ENNReal.ofReal (w i))
    (d : ι →₀ ℕ) (hd : ∀ i ∉ B, d i = 0) :
    v (algebraMap (MvPolynomial ι k) A (MvPolynomial.monomial d 1)) =
      ENNReal.ofReal (realWeight w d) := by
  classical
  have hm : algebraMap (MvPolynomial ι k) A (MvPolynomial.monomial d 1) =
      ∏ i, (algebraMap (MvPolynomial ι k) A (MvPolynomial.X i)) ^ d i := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
    simp
  rw [hm, valuation_prod]
  unfold realWeight
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hw i) (Nat.cast_nonneg _))]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ B
  · rw [v.map_pow, hz i hi, nsmul_eq_mul, ENNReal.ofReal_mul (hw i), ENNReal.ofReal_natCast]
    exact mul_comm _ _
  · simp [hd i hi]

/-- Elements of the higher-boundary-weight ideal have strictly higher valuation. -/
theorem valuation_gt_of_mem_boundaryWeightIdeal (v : AddValuation A ENNReal)
    (B : Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hz : ∀ i ∈ B, v (algebraMap (MvPolynomial ι k) A (MvPolynomial.X i)) = ENNReal.ofReal (w i))
    (L : ℝ) (hL : 0 ≤ L) {q : A}
    (hq : q ∈ chartBoundaryWeightIdeal (k := k) B w L) :
    ENNReal.ofReal L < v q := by
  have hle : chartBoundaryWeightIdeal (k := k) B w L ≤ strictValuationIdeal v L := by
    apply Ideal.span_le.mpr
    rintro _ ⟨d, ⟨hd, hweight⟩, rfl⟩
    change ENNReal.ofReal L < v _
    rw [valuation_boundary_monomial v B w hw hz d hd]
    exact (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hL hweight)).mpr hweight
  exact hle hq

/-- The isolated-jet congruence determines the valuation. -/
theorem valuation_isolated_jet (v : AddValuation A ENNReal)
    (B : Finset ι) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hz : ∀ i ∈ B, v (algebraMap (MvPolynomial ι k) A (MvPolynomial.X i)) = ENNReal.ofReal (w i))
    (α : ι →₀ ℕ) (hα : ∀ i ∉ B, α i = 0) {u q g : A} (hu : IsUnit u)
    (hq : q ∈ chartBoundaryWeightIdeal (k := k) B w (realWeight w α))
    (hg : g = u * algebraMap (MvPolynomial ι k) A (MvPolynomial.monomial α 1) + q) :
    v g = ENNReal.ofReal (realWeight w α) := by
  have hm : v (u * algebraMap (MvPolynomial ι k) A (MvPolynomial.monomial α 1)) =
      ENNReal.ofReal (realWeight w α) := by
    rw [v.map_mul, valuation_unit_zero v hu, zero_add]
    exact valuation_boundary_monomial v B w hw hz α hα
  have hqv := valuation_gt_of_mem_boundaryWeightIdeal v B w hw hz (realWeight w α)
    (Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (Nat.cast_nonneg _)) hq
  rw [hg, v.map_add_eq_of_lt_left (hm ▸ hqv), hm]
end MonomialValue
end CartierSections

namespace CartierSections
section RetractionLower
variable {k A ι : Type*} [Field k] [CommRing A] [Fintype ι]
  [Algebra k A] [Algebra (MvPolynomial ι k) A] [IsScalarTower k (MvPolynomial ι k) A]
  [Algebra A (MvPowerSeries ι k)]
  [Module.FaithfullyFlat A (MvPowerSeries ι k)]

/-- The initial weight bounds the valuation below by faithful flatness of expansion. -/
theorem valuation_ge_initial_weight
    (θ : A →ₐ[k] MvPowerSeries ι k)
    (hcoord : ∀ i, θ (algebraMap (MvPolynomial ι k) A (MvPolynomial.X i)) = MvPowerSeries.X i)
    (hθ : θ.toRingHom = algebraMap A (MvPowerSeries ι k))
    (v : AddValuation A ENNReal) (B : Finset ι) (w : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hwzero : ∀ i ∉ B, w i = 0)
    (hz : ∀ i ∈ B, v (algebraMap (MvPolynomial ι k) A (MvPolynomial.X i)) = ENNReal.ofReal (w i))
    (f : A) (L : ℝ)
    (hL : ∀ d, MvPowerSeries.coeff d (θ f) ≠ 0 → L ≤ realWeight w d) :
    ENNReal.ofReal L ≤ v f := by
  classical
  let E : Set (ι →₀ ℕ) := {d | (∀ i ∉ B, d i = 0) ∧ L ≤ realWeight w d}
  let I : Ideal A := Ideal.span
    ((fun d => algebraMap (MvPolynomial ι k) A (MvPolynomial.monomial d 1)) '' E)
  have hI : I.map θ.toRingHom = Ideal.span
      ((fun d => (MvPowerSeries.monomial d 1 : MvPowerSeries ι k)) '' E) := by
    dsimp only [I]
    rw [Ideal.map_span, Set.image_image]
    congr 1
    apply Set.image_congr
    intro d hd
    change θ (algebraMap (MvPolynomial ι k) A (MvPolynomial.monomial d 1)) = _
    rw [chart_polynomial_series θ hcoord]
    simp
  have hmemS : θ f ∈ I.map θ.toRingHom := by
    rw [hI]
    apply series_mem_span_monomials
    intro d hd
    let e := d.filter (fun i => i ∈ B)
    have hew : realWeight w e = realWeight w d := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ B
      · simp [e, hi]
      · simp [e, hi, hwzero i hi]
    refine ⟨e, ⟨?_, by simpa [hew] using hL d hd⟩, ?_⟩
    · intro i hi; simp [e, hi]
    · intro i
      by_cases hi : i ∈ B <;> simp [e, hi]
  have hmem : f ∈ I := by
    rw [← I.comap_map_eq_self_of_faithfullyFlat (B := MvPowerSeries ι k)]
    change algebraMap A (MvPowerSeries ι k) f ∈ I.map (algebraMap A (MvPowerSeries ι k))
    rw [← hθ]
    exact hmemS
  let J : Ideal A := {
    carrier := {g | ENNReal.ofReal L ≤ v g}
    zero_mem' := by simp
    add_mem' := fun hg hh => v.map_le_add hg hh
    smul_mem' := by
      intro a g hg
      change ENNReal.ofReal L ≤ v (a*g)
      rw [v.map_mul]
      exact hg.trans (le_add_left le_rfl) }
  have hle : I ≤ J := by
    apply Ideal.span_le.mpr
    rintro _ ⟨d, ⟨hd, hweight⟩, rfl⟩
    change ENNReal.ofReal L ≤ v _
    rw [valuation_boundary_monomial v B w hw hz d hd]
    exact ENNReal.ofReal_le_ofReal hweight
  exact hle hmem
end RetractionLower
end CartierSections

end OAI
