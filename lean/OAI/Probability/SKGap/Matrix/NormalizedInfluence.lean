import Mathlib
import OAI.Probability.SKGap.Localization.BilinearCoefficient
import OAI.Probability.SKGap.Gaussian.SquaredGaussianFourth

namespace OAI

section
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix Matrix.Norms.Elementwise
open scoped BigOperators
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
open scoped BigOperators NNReal ENNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set
namespace SKGapCutoff

lemma tanh_cubic_remainder (d : ℝ) : |Real.tanh d - d| ≤ |d|^3 := by
  let f (z : ℝ) := Real.tanh z - z
  have hd (z : ℝ) : HasDerivAt f (-(Real.tanh z)^2) z := by
    convert! (tanh_hasDerivAt z).sub (hasDerivAt_id z) using 1
    unfold scalarVariance
    ring
  have hb (z : ℝ) (hz : z ∈ segment ℝ 0 d) : ‖-(Real.tanh z)^2‖ ≤ |d|^2 := by
    have h1 : |Real.tanh z| ≤ |z| := by simpa using tanh_lipschitz 0 z
    have h2 : |z| ≤ |d| := by
      simpa only [sub_zero, Real.norm_eq_abs] using norm_sub_le_of_mem_segment hz
    rw [norm_neg, norm_pow, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (h1.trans h2) 2
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ segment ℝ 0 d) => (hd z).hasDerivWithinAt) hb
    (convex_segment 0 d) (left_mem_segment ℝ 0 d) (right_mem_segment ℝ 0 d)
  simpa only [f, Real.tanh_zero, sub_zero, Real.norm_eq_abs, pow_succ] using h

lemma normalized_tanh_difference (h d : ℝ) :
    (Real.tanh h - Real.tanh (h-d)) / scalarVariance h =
      Real.tanh d / (1 - Real.tanh h * Real.tanh d) := by
  have hc : Real.cosh (h-d) ≠ 0 := (Real.cosh_pos _).ne'
  have hh : Real.cosh h ≠ 0 := (Real.cosh_pos _).ne'
  have hd : Real.cosh d ≠ 0 := (Real.cosh_pos _).ne'
  have hm : Real.cosh h * Real.cosh d - Real.sinh h * Real.sinh d ≠ 0 := by
    simpa only [Real.cosh_sub] using hc
  rw [tanh_difference_eq, show h-(h-d)=d by ring, scalarVariance_eq]
  simp only [Real.tanh_eq_sinh_div_cosh]
  rw [Real.cosh_sub]
  field_simp

lemma rational_cubic_remainder (m u d : ℝ) (hm : |m| ≤ 1)
    (hd : |d| ≤ 1/2) (hu : |u| ≤ |d|) (hud : |u-d| ≤ |d|^3) :
    |u/(1-m*u) - d - m*d^2| ≤ 4*|d|^3 := by
  have hmud : |m*u| ≤ |d| := by
    rw [abs_mul]
    exact (mul_le_mul hm hu (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hden : 1/2 ≤ 1-m*u := by linarith [le_abs_self (m*u)]
  have hdenpos : 0 < 1-m*u := by linarith
  have hd0 := abs_nonneg d
  have he : u/(1-m*u) - d - m*d^2 =
      (u-d) + m*(u^2-d^2) + m^2*u^3/(1-m*u) := by
    apply mul_right_cancel₀ hdenpos.ne'
    simp only [sub_mul, add_mul, div_mul_cancel₀ _ hdenpos.ne']
    ring
  have hs : |u^2-d^2| ≤ |d|^3 := by
    have hh : |u^2-d^2| = |u-d| * |u+d| := by rw [← abs_mul]; congr 1; ring
    rw [hh]
    have ha : |u+d| ≤ 1 := (abs_add_le _ _).trans (by linarith)
    nlinarith [mul_le_mul hud ha (abs_nonneg _) (pow_nonneg hd0 3)]
  have ht : |m*(u^2-d^2)| ≤ |d|^3 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul hm hs (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
  have hq : |m^2*u^3/(1-m*u)| ≤ 2*|d|^3 := by
    rw [abs_div, abs_mul, abs_pow, abs_pow, abs_of_pos hdenpos, div_le_iff₀ hdenpos]
    have hm2 : |m|^2 ≤ 1 := by nlinarith [abs_nonneg m]
    have hu3 : |u|^3 ≤ |d|^3 := pow_le_pow_left₀ (abs_nonneg _) hu 3
    have hp := mul_le_mul hm2 hu3 (pow_nonneg (abs_nonneg _) _) (by norm_num : (0:ℝ) ≤ 1)
    nlinarith [mul_le_mul_of_nonneg_left hden (pow_nonneg hd0 3)]
  rw [he]
  exact (abs_add_le _ _).trans ((add_le_add ((abs_add_le _ _).trans (add_le_add hud ht)) hq).trans (by ring_nf; rfl))

lemma normalized_tanh_cubic (h d : ℝ) (hd : |d| ≤ 1/2) :
    |(Real.tanh h - Real.tanh (h-d))/scalarVariance h - d - Real.tanh h*d^2| ≤
      4*|d|^3 := by
  rw [normalized_tanh_difference]
  exact rational_cubic_remainder _ _ _ (Real.abs_tanh_lt_one h).le hd
    (by simpa using tanh_lipschitz 0 d) (tanh_cubic_remainder d)

lemma normalized_influence_cubic {n : ℕ} (J : Interaction n) (x : Spin n) (i j : Fin n)
    (hJ : |J j i| ≤ 1/4) :
    |influence J x i j / siteVariance J x j - J j i - 2*spin x i*mean J x j*(J j i)^2| ≤
      16*|J j i|^3 := by
  have ha : |2*J j i*spin x i| = 2*|J j i| := by
    rw [abs_mul, abs_mul, abs_spin_eq_one]; norm_num
  have hd : |2*J j i*spin x i| ≤ 1/2 := by rw [ha]; linarith
  have hh := normalized_tanh_cubic (field J x j) (2*J j i*spin x i) hd
  have hv : siteVariance J x j ≠ 0 := (siteVariance_pos J x j).ne'
  have he : influence J x i j / siteVariance J x j - J j i - 2*spin x i*mean J x j*(J j i)^2 =
      (spin x i / 2) * ((Real.tanh (field J x j) -
        Real.tanh (field J x j - 2*J j i*spin x i))/scalarVariance (field J x j) -
          2*J j i*spin x i - Real.tanh (field J x j)*(2*J j i*spin x i)^2) := by
    simp only [influence, halfDiff_as_flip, mean, field_flip_general, scalarVariance, siteVariance]
    have hs := spin_sq x i
    have ht : 1 - Real.tanh (field J x j)^2 ≠ 0 := (scalarVariance_pos _).ne'
    field_simp [ht]
    linear_combination (2 * J j i * (1 - Real.tanh (field J x j)^2) +
      4 * spin x i * Real.tanh (field J x j) * (J j i)^2 * (1 - Real.tanh (field J x j)^2)) * hs
  rw [he, abs_mul, abs_div, abs_spin_eq_one]
  rw [ha] at hh
  norm_num only [abs_of_pos (show (0:ℝ) < 2 by norm_num)]
  nlinarith

lemma matrix_opNorm_le_schur {n : ℕ} (A : Interaction n) (R : ℝ) (hR : 0 ≤ R)
    (hr : ∀ i, ∑ j, |A i j| ≤ R) (hc : ∀ j, ∑ i, |A i j| ≤ R) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A‖ ≤ R := by
  apply ContinuousLinearMap.opNorm_le_of_re_inner_le hR
  intro x y hx hy
  change inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) A x) y ≤ R
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  change (∑ i, y i * ∑ j, A i j*x j) ≤ R
  simp only [Finset.mul_sum]
  calc
    _ ≤ ∑ i, ∑ j, |A i j| * ((y i)^2 + (x j)^2)/2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hab : 2*|y i| *|x j| ≤ (y i)^2+(x j)^2 := by
        nlinarith [sq_nonneg (|y i|-|x j|), sq_abs (y i), sq_abs (x j)]
      have hp := mul_le_mul_of_nonneg_left hab (abs_nonneg (A i j))
      have hh : y i*(A i j*x j) ≤ |y i| *|A i j| *|x j| := by
        simpa only [abs_mul, mul_assoc] using le_abs_self (y i*(A i j*x j))
      nlinarith
    _ = ((∑ i, (y i)^2 * ∑ j, |A i j|) + ∑ j, (x j)^2 * ∑ i, |A i j|)/2 := by
      simp only [mul_add, add_div, Finset.sum_add_distrib, ← Finset.sum_div]
      rw [Finset.sum_comm (f := fun i j => |A i j| * (x j)^2)]
      simp only [← Finset.sum_mul]
      congr 2 <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring
    _ ≤ ((∑ i, (y i)^2 * R) + ∑ j, (x j)^2*R)/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact add_le_add
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hr i) (sq_nonneg _)))
        (Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hc i) (sq_nonneg _)))
    _ = R := by
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← EuclideanSpace.real_norm_sq_eq,
        ← EuclideanSpace.real_norm_sq_eq, hx, hy]
      ring

lemma matrix_diagonal_opNorm_le {n : ℕ} (d : Fin n → ℝ) (R : ℝ) (hR : 0 ≤ R)
    (hd : ∀ i, |d i| ≤ R) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.diagonal d)‖ ≤ R := by
  apply matrix_opNorm_le_schur _ R hR
  · intro i
    simpa [Matrix.diagonal, apply_ite, abs_zero] using hd i
  · intro i
    simpa [Matrix.diagonal, apply_ite, abs_zero] using hd i

noncomputable def normalizedInfluence {n : ℕ} (J : Interaction n) (x : Spin n) : Interaction n :=
  fun i j => influence J x i j / siteVariance J x j

noncomputable def influenceCubicError {n : ℕ} (J : Interaction n) (x : Spin n) : Interaction n :=
  fun i j => normalizedInfluence J x i j - J j i - 2*spin x i*mean J x j*(J j i)^2

lemma influenceCubicError_norm_le {n : ℕ} (J : Interaction n)
    (hsymm : ∀ i j, J i j=J j i) (x : Spin n) (c B : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1/4)
    (hB : 0 ≤ B) (hmax : ∀ i j, |J i j| ≤ c)
    (hcol : ∀ i, ∑ j, J j i^2 ≤ B) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (influenceCubicError J x)‖ ≤ 16*c*B := by
  have hp (i j : Fin n) : |influenceCubicError J x i j| ≤ 16*c*(J j i)^2 := by
    have hh := normalized_influence_cubic J x i j ((hmax j i).trans hc1)
    change |influenceCubicError J x i j| ≤ _ at hh
    apply hh.trans
    have hmul := mul_le_mul_of_nonneg_right (hmax j i) (sq_nonneg |J j i|)
    nlinarith [sq_abs (J j i)]
  apply matrix_opNorm_le_schur _ (16*c*B) (by positivity)
  · intro i
    calc
      _ ≤ ∑ j, 16*c*(J j i)^2 := Finset.sum_le_sum (fun j _ => hp i j)
      _ = 16*c*∑ j, J j i^2 := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcol i) (by positivity)
  · intro j
    calc
      _ ≤ ∑ i, 16*c*(J j i)^2 := Finset.sum_le_sum (fun i _ => hp i j)
      _ = 16*c*∑ i, J i j^2 := by simp only [hsymm j, Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (hcol j) (by positivity)

noncomputable def normalizedInfluenceApprox {n : ℕ} (β : ℝ) (J : Interaction n) (x : Spin n) : Interaction n :=
  fun i j => J i j + 2*β^2/(n:ℝ)*spin x i*mean J x j

lemma normalizedInfluence_sub_approx {n : ℕ} (β : ℝ) (g : GaussianCoordinates n) (x : Spin n) :
    normalizedInfluence (sampledInteraction g) x - normalizedInfluenceApprox β (sampledInteraction g) x =
      influenceCubicError (sampledInteraction g) x + (2:ℝ) •
        (Matrix.diagonal (spin x) * RandomMatrix.sampledSquaredDeviation β g *
          Matrix.diagonal (mean (sampledInteraction g) x)) := by
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul, normalizedInfluenceApprox,
    influenceCubicError, RandomMatrix.sampledSquaredDeviation, sampledInteraction_symm g j i]
  ring

lemma normalizedInfluence_approx_norm_le {n : ℕ} (β : ℝ) (g : GaussianCoordinates n) (x : Spin n)
    (c B : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1/4) (hB : 0 ≤ B)
    (hmax : ∀ i j, |sampledInteraction g i j| ≤ c)
    (hcol : ∀ i, ∑ j, sampledInteraction g j i^2 ≤ B) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (normalizedInfluence (sampledInteraction g) x - normalizedInfluenceApprox β (sampledInteraction g) x)‖ ≤
        16*c*B+2*‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (RandomMatrix.sampledSquaredDeviation β g)‖ := by
  have hs : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.diagonal (spin x))‖ ≤ 1 :=
    matrix_diagonal_opNorm_le _ 1 (by norm_num) (fun i => (abs_spin_eq_one x i).le)
  have hm : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (Matrix.diagonal (mean (sampledInteraction g) x))‖ ≤ 1 :=
    matrix_diagonal_opNorm_le _ 1 (by norm_num) (fun i => (Real.abs_tanh_lt_one _).le)
  have hp : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (Matrix.diagonal (spin x) * RandomMatrix.sampledSquaredDeviation β g *
        Matrix.diagonal (mean (sampledInteraction g) x))‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (RandomMatrix.sampledSquaredDeviation β g)‖ := by
    rw [map_mul, map_mul]
    calc
      _ ≤ _ * _ := norm_mul_le _ _
      _ ≤ (‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.diagonal (spin x))‖ *
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (RandomMatrix.sampledSquaredDeviation β g)‖) *
          ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.diagonal (mean (sampledInteraction g) x))‖ := by
        exact mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
      _ ≤ (1 * ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (RandomMatrix.sampledSquaredDeviation β g)‖) * 1 := by
        gcongr
      _ = _ := by ring
  rw [normalizedInfluence_sub_approx, map_add]
  calc
    _ ≤ _ + _ := norm_add_le _ _
    _ ≤ _ := add_le_add
      (influenceCubicError_norm_le _ (sampledInteraction_symm g) x c B hc hc1 hB hmax hcol)
      (by rw [map_smul, norm_smul]; norm_num only [Real.norm_eq_abs, abs_of_pos (show (0:ℝ)<2 by norm_num)]; exact mul_le_mul_of_nonneg_left hp (by norm_num))

lemma normalizedInfluence_approx_tendsto (β ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => disorderLaw β n {g | ∃ x : Spin n, ε <
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (normalizedInfluence (sampledInteraction g) x - normalizedInfluenceApprox β (sampledInteraction g) x)‖})
      atTop (nhds 0) := by
  let B : ℝ := (2*(β^2+10))^2
  let c : ℝ := min (1/4) (ε/(64*(B+1)))
  have hB : 0 ≤ B := sq_nonneg _
  have hc : 0 < c := lt_min (by norm_num) (by positivity)
  have hc1 : c ≤ 1/4 := min_le_left _ _
  have hcd : 16*c*B ≤ ε/4 := by
    calc
      _ ≤ 16*(ε/(64*(B+1)))*(B+1) := mul_le_mul
        (mul_le_mul_of_nonneg_left (min_le_right _ _) (by norm_num)) (by linarith)
        hB (by positivity)
      _ = ε/4 := by field_simp; ring
  have hl := (RandomMatrix.sampled_opNorm_tendsto β).add
    ((RandomMatrix.sampled_maxEntry_tendsto β c hc).add
      (RandomMatrix.sampledSquaredDeviation_tendsto β (ε/8) (by positivity)))
  simp only [add_zero] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hl
    (Eventually.of_forall (fun _ => bot_le))
  apply Eventually.of_forall
  intro n
  let N : Set (GaussianCoordinates n) := {g | 2*(β^2+10) <
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g)‖}
  let E : Set (GaussianCoordinates n) := {g | ∃ i j, c ≤ |sampledInteraction g i j|}
  let V : Set (GaussianCoordinates n) := {g | ε/8 <
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (RandomMatrix.sampledSquaredDeviation β g)‖}
  have hs : {g | ∃ x : Spin n, ε < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (normalizedInfluence (sampledInteraction g) x - normalizedInfluenceApprox β (sampledInteraction g) x)‖} ⊆
      N ∪ (E ∪ V) := by
    intro g hg
    by_cases hN : g ∈ N
    · exact Or.inl hN
    by_cases hE : g ∈ E
    · exact Or.inr (Or.inl hE)
    by_cases hV : g ∈ V
    · exact Or.inr (Or.inr hV)
    have hn : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g)‖ ≤ 2*(β^2+10) :=
      le_of_not_gt hN
    have he (i j : Fin n) : |sampledInteraction g i j| ≤ c :=
      (not_le.mp (fun h => hE ⟨i,j,h⟩)).le
    have hv : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (RandomMatrix.sampledSquaredDeviation β g)‖ ≤ ε/8 :=
      le_of_not_gt hV
    obtain ⟨x,hx⟩ := hg
    have hp := normalizedInfluence_approx_norm_le β g x c B hc.le hc1 hB he (fun i =>
      (RandomMatrix.matrix_column_sq_le _ i).trans (pow_le_pow_left₀ (norm_nonneg _) hn 2))
    exfalso
    linarith
  exact (measure_mono hs).trans ((measure_union_le N (E ∪ V)).trans
    (add_le_add le_rfl (measure_union_le E V)))

noncomputable def influenceApprox {n : ℕ} (β : ℝ) (J : Interaction n) (x : Spin n) : Interaction n :=
  normalizedInfluenceApprox β J x * Matrix.diagonal (siteVariance J x)

lemma influence_eq_normalized_mul {n : ℕ} (J : Interaction n) (x : Spin n) :
    influence J x = normalizedInfluence J x * Matrix.diagonal (siteVariance J x) := by
  ext i j
  simp only [Matrix.mul_diagonal, normalizedInfluence]
  rw [div_mul_cancel₀ _ (siteVariance_pos J x j).ne']

lemma influenceApprox_apply {n : ℕ} (β : ℝ) (J : Interaction n) (x : Spin n) (i j : Fin n) :
    influenceApprox β J x i j = J i j*siteVariance J x j +
      2*β^2/(n:ℝ)*spin x i*(mean J x j*siteVariance J x j) := by
  simp only [influenceApprox, Matrix.mul_diagonal, normalizedInfluenceApprox]
  ring

lemma influence_approx_error_le {n : ℕ} (β : ℝ) (J : Interaction n) (x : Spin n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (influence J x - influenceApprox β J x)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (normalizedInfluence J x - normalizedInfluenceApprox β J x)‖ := by
  have hv : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (Matrix.diagonal (siteVariance J x))‖ ≤ 1 := by
    apply matrix_diagonal_opNorm_le _ 1 (by norm_num)
    intro i
    rw [abs_of_pos (siteVariance_pos J x i)]
    exact siteVariance_le_one J x i
  rw [influence_eq_normalized_mul, influenceApprox, ← Matrix.sub_mul, map_mul]
  exact (norm_mul_le _ _).trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hv (norm_nonneg _))

lemma influence_approx_tendsto (β ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n => disorderLaw β n {g | ∃ x : Spin n, ε <
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (influence (sampledInteraction g) x - influenceApprox β (sampledInteraction g) x)‖})
      atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (normalizedInfluence_approx_tendsto β ε hε) (Eventually.of_forall (fun _ => bot_le))
  apply Eventually.of_forall
  intro n
  apply measure_mono
  rintro g ⟨x,hx⟩
  exact ⟨x,hx.trans_le (influence_approx_error_le β (sampledInteraction g) x)⟩

lemma normalizedInfluenceApprox_norm_le {n : ℕ} (β : ℝ) (J : Interaction n) (x : Spin n) :
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (normalizedInfluenceApprox β J x)‖ ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ + 2*β^2 := by
  let R : Interaction n := fun i j => 2*β^2/(n:ℝ)*spin x i*mean J x j
  have he : normalizedInfluenceApprox β J x = J+R := rfl
  have hr : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) R‖ ≤ 2*β^2 := by
    by_cases hn : n=0
    · subst n
      have hz : R=0 := Subsingleton.elim _ _
      rw [hz, map_zero, norm_zero]; positivity
    have hn0 : 0 < (n:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hp (i j : Fin n) : |R i j| ≤ 2*β^2/(n:ℝ) := by
      change |2*β^2/(n:ℝ)*spin x i*mean J x j| ≤ _
      rw [abs_mul, abs_mul, abs_spin_eq_one, mul_one, abs_of_nonneg (by positivity : 0 ≤ 2*β^2/(n:ℝ))]
      exact (mul_le_mul_of_nonneg_left (Real.abs_tanh_lt_one _).le (by positivity)).trans_eq (mul_one _)
    apply matrix_opNorm_le_schur _ (2*β^2) (by positivity)
    · intro i
      calc
        _ ≤ ∑ j : Fin n, 2*β^2/(n:ℝ) := Finset.sum_le_sum (fun j _ => hp i j)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
    · intro j
      calc
        _ ≤ ∑ i : Fin n, 2*β^2/(n:ℝ) := Finset.sum_le_sum (fun i _ => hp i j)
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp
  rw [he, map_add]
  exact (norm_add_le _ _).trans (add_le_add le_rfl hr)

lemma normalizedInfluence_opNorm_tight (β : ℝ) :
    Tendsto (fun n => disorderLaw β n {g | ∃ x : Spin n,
      2*(β^2+10)+2*β^2+1 <
        ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (normalizedInfluence (sampledInteraction g) x)‖})
      atTop (nhds 0) := by
  have hl := (RandomMatrix.sampled_opNorm_tendsto β).add
    (normalizedInfluence_approx_tendsto β 1 (by norm_num))
  simp only [add_zero] at hl
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hl
    (Eventually.of_forall (fun _ => bot_le))
  apply Eventually.of_forall
  intro n
  refine (measure_mono (show {g | ∃ x : Spin n, 2*(β^2+10)+2*β^2+1 <
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (normalizedInfluence (sampledInteraction g) x)‖} ⊆
    {g | 2*(β^2+10) < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g)‖} ∪
    {g | ∃ x : Spin n, 1 < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ)
      (normalizedInfluence (sampledInteraction g) x - normalizedInfluenceApprox β (sampledInteraction g) x)‖}
    from ?_)).trans (measure_union_le _ _)
  rintro g ⟨x,hx⟩
  by_cases hJ : 2*(β^2+10) < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g)‖
  · exact Or.inl hJ
  apply Or.inr
  refine ⟨x,?_⟩
  have hh := normalizedInfluenceApprox_norm_le β (sampledInteraction g) x
  have ht := norm_le_norm_sub_add
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (normalizedInfluence (sampledInteraction g) x))
    (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (normalizedInfluenceApprox β (sampledInteraction g) x))
  rw [← map_sub] at ht
  linarith [le_of_not_gt hJ]

end SKGapCutoff

open scoped BigOperators Matrix Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory Filter Set

end

end OAI
