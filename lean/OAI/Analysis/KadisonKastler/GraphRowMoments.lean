import OAI.Analysis.KadisonKastler.FlattenedGraphVector
import OAI.Analysis.KadisonKastler.FiniteIndependentSamples

namespace OAI

/-! # Moments of a finite replicated graph row

The row consists of independently chosen left matrix translates of the
same clipped element. Its two fourth-moment sums reduce to the actual
matrix averages already shown to converge to the vector state.
-/

namespace KadisonKastler

open Filter
open scoped BigOperators Topology CStarAlgebra

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The positive left square of an operator row. -/
def graphRowSquare {I : Type*} [Fintype I] (Y : I → H →L[ℂ] H) : H →L[ℂ] H :=
  ∑ i, Y i * star (Y i)

/-- The fourth-moment cost controlling both rescaled row coordinates. -/
def graphRowCost (Ω : H) {I : Type*} [Fintype I] (Y : I → H →L[ℂ] H) : ℝ :=
  realVectorState Ω ((graphRowSquare Y) ^ 2) +
    (Fintype.card I : ℝ)⁻¹ * ∑ i, realVectorState Ω (star (Y i) * graphRowSquare Y * Y i)

/-- The concrete row of independently sampled left matrix translates. -/
def matrixGraphRow {I : Type*} {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H)) (z : H →L[ℂ] H)
    (ω : I → SignedPermutation (Fin d)) (i : I) : H →L[ℂ] H :=
  (matrixUnitSignedRepresentation E (ω i) : H →L[ℂ] H) * z

private theorem re_finiteAverage {G : Type*} [Fintype G] (f : G → ℂ) :
    (finiteAverage f).re = 𝔼 g, (f g).re := by
  have he : (𝔼 g, f g) = finiteAverage f := by
    rw [Fintype.expect_eq_sum_div_card]
    simp only [finiteAverage, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [← he]
  exact map_expect (Complex.reLm.restrictScalars ℚ≥0) f Finset.univ

private theorem realState_conj (M : VonNeumannAlgebra H) (Ω : H)
    (u : unitary (H →L[ℂ] H)) (hu : (u : H →L[ℂ] H) ∈ M)
    (hc : ∀ x ∈ M, inner ℂ Ω (((u : H →L[ℂ] H) * x) Ω) =
      inner ℂ Ω ((x * (u : H →L[ℂ] H)) Ω))
    (a : H →L[ℂ] H) (ha : a ∈ M) :
    realVectorState Ω (unitaryConj u a) = realVectorState Ω a := by
  have h := hc (a * star (u : H →L[ℂ] H))
    (M.mul_mem ha (M.toStarSubalgebra.star_mem' hu))
  apply congrArg Complex.re
  change inner ℂ Ω (((u : H →L[ℂ] H) * a * star (u : H →L[ℂ] H)) Ω) =
    inner ℂ Ω (a Ω)
  simpa only [mul_assoc, Unitary.star_mul_self_of_mem u.property, mul_one] using h

private theorem leftTranslate_left_square (u : unitary (H →L[ℂ] H)) (z : H →L[ℂ] H) :
    ((u : H →L[ℂ] H) * z) * star ((u : H →L[ℂ] H) * z) =
      unitaryConj u (z * star z) := by
  simp only [unitaryConj, star_mul, mul_assoc]

private theorem leftTranslate_pair (u v : unitary (H →L[ℂ] H)) (z : H →L[ℂ] H) :
    star ((u : H →L[ℂ] H) * z) *
        (((v : H →L[ℂ] H) * z) * star ((v : H →L[ℂ] H) * z)) *
          ((u : H →L[ℂ] H) * z) =
      star z * unitaryConj (star u) (unitaryConj v (z * star z)) * z := by
  simp only [star_mul, unitaryConj, Unitary.coe_star, star_star]
  noncomm_ring

private theorem leftTranslate_pair_diagonal (u : unitary (H →L[ℂ] H))
    (z : H →L[ℂ] H) :
    star z * unitaryConj (star u) (unitaryConj u (z * star z)) * z =
      (star z * z) ^ 2 := by
  rw [unitaryConj_star_unitaryConj]
  noncomm_ring

/-- Expanding the actual row cost yields two independent pair sums. -/
theorem graphRowCost_eq_pair_sums (Ω : H) {I : Type*} [Fintype I]
    (Y : I → H →L[ℂ] H) :
    graphRowCost Ω Y =
      (∑ i, ∑ j, realVectorState Ω ((Y i * star (Y i)) * (Y j * star (Y j)))) +
      (Fintype.card I : ℝ)⁻¹ *
        ∑ i, ∑ j, realVectorState Ω (star (Y i) * (Y j * star (Y j)) * Y i) := by
  simp only [graphRowCost, graphRowSquare, pow_two, Finset.sum_mul,
    Finset.mul_sum, map_sum]
  congr 1
  exact Finset.sum_comm

/-- The finite independent sampling law gives the exact expected cost
of the replicated row, before any limiting estimate. -/
theorem expect_matrixGraphRow_cost (M : VonNeumannAlgebra H) (Ω : H)
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I] {d : ℕ}
    (E : Generator.MatrixUnitSystem (Fin d) (H →L[ℂ] H))
    (hEM : E.algebra ≤ M.toStarSubalgebra)
    (hc : ∀ a ∈ E.algebra, ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (z : H →L[ℂ] H) (hz : z ∈ M) :
    (𝔼 ω : I → SignedPermutation (Fin d), graphRowCost Ω (matrixGraphRow E z ω)) =
      (Fintype.card I : ℝ) * realVectorState Ω ((z * star z) ^ 2) +
      (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) *
        realVectorState Ω ((z * star z) * matrixUnitAverage E (z * star z)) +
      realVectorState Ω ((star z * z) ^ 2) +
      ((Fintype.card I : ℝ) - 1) *
        realVectorState Ω (star z * matrixUnitAverage E (z * star z) * z) := by
  let u : SignedPermutation (Fin d) → unitary (H →L[ℂ] H) :=
    matrixUnitSignedRepresentation E
  let f : SignedPermutation (Fin d) → SignedPermutation (Fin d) → ℝ := fun g h =>
    realVectorState Ω (unitaryConj (u g) (z * star z) * unitaryConj (u h) (z * star z))
  let q : SignedPermutation (Fin d) → SignedPermutation (Fin d) → ℝ := fun g h =>
    realVectorState Ω (star z * unitaryConj (star (u g))
      (unitaryConj (u h) (z * star z)) * z)
  have hfdiag : (𝔼 g, f g g) = realVectorState Ω ((z * star z) ^ 2) := by
    have he (g : SignedPermutation (Fin d)) : f g g =
        realVectorState Ω ((z * star z) ^ 2) := by
      dsimp only [f]
      rw [← pow_two]
      have hp := map_pow (Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) (u g)) (z * star z) 2
      change unitaryConj (u g) ((z * star z) ^ 2) = (unitaryConj (u g) (z * star z)) ^ 2 at hp
      rw [← hp]
      exact realState_conj M Ω (u g) (hEM (matrixUnitSignedRepresentation_mem E g))
        (hc _ (matrixUnitSignedRepresentation_mem E g)) _
        (M.pow_mem (M.mul_mem hz (M.toStarSubalgebra.star_mem' hz)) 2)
    simp_rw [he]
    exact Fintype.expect_const _
  have hqdiag : (𝔼 g, q g g) = realVectorState Ω ((star z * z) ^ 2) := by
    simp only [q, leftTranslate_pair_diagonal, Fintype.expect_const]
  have hfpair : (𝔼 g, 𝔼 h, f g h) =
      realVectorState Ω ((z * star z) * matrixUnitAverage E (z * star z)) := by
    have h := congrArg Complex.re (matrixState_two_orbit_average M Ω E hEM hc
      (z * star z) (z * star z) (M.mul_mem hz (M.toStarSubalgebra.star_mem' hz))
      (M.mul_mem hz (M.toStarSubalgebra.star_mem' hz)))
    simp_rw [re_finiteAverage] at h
    exact h
  have hqpair : (𝔼 g, 𝔼 h, q g h) =
      realVectorState Ω (star z * matrixUnitAverage E (z * star z) * z) := by
    have h := congrArg Complex.re (matrixState_relative_orbit_average Ω E
      (star z) (z * star z) z)
    simp_rw [re_finiteAverage] at h
    exact h
  have he (ω : I → SignedPermutation (Fin d)) :
      graphRowCost Ω (matrixGraphRow E z ω) =
        (∑ i, ∑ j, f (ω i) (ω j)) +
          (Fintype.card I : ℝ)⁻¹ * ∑ i, ∑ j, q (ω i) (ω j) := by
    rw [graphRowCost_eq_pair_sums]
    simp only [matrixGraphRow]
    simp_rw [leftTranslate_pair, leftTranslate_left_square]
    rfl
  simp_rw [he]
  rw [Finset.expect_add_distrib, ← Finset.mul_expect,
    expect_sample_pair_sum, expect_sample_pair_sum, hfdiag, hqdiag, hfpair, hqpair]
  have hn : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

/-- A bounded operator controls the fourth vector-state moment by its
second moment, without a trace assumption. -/
theorem realVectorState_fourth_le_norm_sq (Ω : H) (z : H →L[ℂ] H) :
    realVectorState Ω ((star z * z) ^ 2) ≤ ‖z‖ ^ 2 * ‖z Ω‖ ^ 2 := by
  have he : (star z * z) ^ 2 = star (star z * z) * (star z * z) := by
    simp only [star_mul, star_star, pow_two]
  rw [he, realVectorState_star_mul_self, mul_apply_eq_comp]
  have hn := (star z).le_opNorm (z Ω)
  rw [norm_star] at hn
  have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
  simpa only [mul_pow] using hh

/-- The corresponding bound holds for the left square. -/
theorem realVectorState_reverse_fourth_le_norm_sq (Ω : H) (z : H →L[ℂ] H) :
    realVectorState Ω ((z * star z) ^ 2) ≤ ‖z‖ ^ 2 * ‖star z Ω‖ ^ 2 := by
  simpa only [star_star, norm_star] using realVectorState_fourth_le_norm_sq Ω (star z)

/-- The exact limiting cost of the independent replicated row. -/
theorem matrixGraphRow_cost_tendsto (M : VonNeumannAlgebra H) (Ω : H) (hΩ : ‖Ω‖ = 1)
    {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (d : ℕ → ℕ) (E : ∀ n, Generator.MatrixUnitSystem (Fin (d n)) (H →L[ℂ] H))
    (hmono : Monotone (fun n => (E n).algebra))
    (hEM : ∀ n, (E n).algebra ≤ M.toStarSubalgebra)
    (hirr : ∀ T ∈ M, (∀ n a, a ∈ (E n).algebra → a * T = T * a) →
      ∃ c : ℂ, T = c • (1 : H →L[ℂ] H))
    (hc : ∀ n a, a ∈ (E n).algebra → ∀ x ∈ M,
      inner ℂ Ω ((a * x) Ω) = inner ℂ Ω ((x * a) Ω))
    (z : H →L[ℂ] H) (hz : z ∈ M) :
    Tendsto (fun n => 𝔼 ω : I → SignedPermutation (Fin (d n)),
      graphRowCost Ω (matrixGraphRow (E n) z ω)) atTop
      (𝓝 ((Fintype.card I : ℝ) * realVectorState Ω ((z * star z) ^ 2) +
        (Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1) * ‖star z Ω‖ ^ 4 +
        realVectorState Ω ((star z * z) ^ 2) +
        ((Fintype.card I : ℝ) - 1) * (‖z Ω‖ ^ 2 * ‖star z Ω‖ ^ 2))) := by
  have hb : z * star z ∈ M := M.mul_mem hz (M.toStarSubalgebra.star_mem' hz)
  have hp := matrixState_two_orbit_tendsto M Ω hΩ d E hmono hEM hirr hc
    (z * star z) (z * star z) hb hb
  simp_rw [matrixState_two_orbit_average M Ω _ (hEM _) (hc _) _ _ hb hb] at hp
  have hq := matrixState_relative_orbit_tendsto M Ω hΩ d E hmono hEM hirr hc
    (star z) (z * star z) z hb
  simp_rw [matrixState_relative_orbit_average] at hq
  have hleft : operatorVectorState Ω (z * star z) = (‖star z Ω‖ ^ 2 : ℝ) := by
    simpa only [star_star] using operatorVectorState_star_mul_self Ω (star z)
  have hright : operatorVectorState Ω (star z * z) = (‖z Ω‖ ^ 2 : ℝ) :=
    operatorVectorState_star_mul_self Ω z
  rw [hleft] at hp
  rw [hleft, hright] at hq
  have hpR := Complex.continuous_re.tendsto _ |>.comp hp
  have hqR := Complex.continuous_re.tendsto _ |>.comp hq
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero] at hpR hqR
  have hpR' : Tendsto (fun n => realVectorState Ω ((z * star z) *
      matrixUnitAverage (E n) (z * star z))) atTop (𝓝 (‖star z Ω‖ ^ 4)) := by
    rw [show ‖star z Ω‖ ^ 2 * ‖star z Ω‖ ^ 2 = ‖star z Ω‖ ^ 4 by ring] at hpR
    exact hpR
  change Tendsto (fun n => realVectorState Ω (star z *
      matrixUnitAverage (E n) (z * star z) * z)) atTop
    (𝓝 (‖star z Ω‖ ^ 2 * ‖z Ω‖ ^ 2)) at hqR
  rw [mul_comm (‖star z Ω‖ ^ 2) (‖z Ω‖ ^ 2)] at hqR
  simp_rw [expect_matrixGraphRow_cost M Ω _ (hEM _) (hc _) z hz]
  exact (((hpR'.const_mul ((Fintype.card I : ℝ) * ((Fintype.card I : ℝ) - 1))).const_add
    ((Fintype.card I : ℝ) * realVectorState Ω ((z * star z) ^ 2))).add_const
      (realVectorState Ω ((star z * z) ^ 2))).add
        (hqR.const_mul ((Fintype.card I : ℝ) - 1))

end

end KadisonKastler

end OAI
