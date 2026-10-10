import Mathlib
import OAI.Probability.SKGap.Gaussian.ReplicaTailWeight
import OAI.Probability.SKGap.Localization.ScalarVariance
import OAI.Probability.SKGap.Localization.SeparatedCard

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
namespace SKGapCutoff.RandomMatrix

lemma gaussian_linear_upper_tail {ι : Type*} [Fintype ι] (v : ℝ≥0) (a : ι → ℝ)
    (r t : ℝ) (ht : 0 < t) :
    (Measure.pi (fun _ : ι => gaussianReal 0 v)) {g | r ≤ ∑ i, a i * g i} ≤
      ENNReal.ofReal (Real.exp (v * (∑ i, a i ^ 2) * t^2 / 2 - t*r)) := by
  let μ := Measure.pi (fun _ : ι => gaussianReal 0 v)
  have he (g : ι → ℝ) : ∑ i, (t*a i)*g i = t * ∑ i, a i*g i := by
    simp only [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring
  have hs : {g : ι → ℝ | r ≤ ∑ i, a i*g i} ⊆
      {g | Real.exp (t*r) ≤ Real.exp (∑ i, (t*a i)*g i)} := by
    intro g hg
    rw [Set.mem_ofPred_eq, he]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hg ht.le)
  refine (measure_mono hs).trans ?_
  have hh := probability_markov_real μ (fun g => Real.exp (∑ i, (t*a i)*g i))
    (integrable_exp_gaussian_linear v (fun i => t*a i)) (fun _ => (Real.exp_pos _).le)
    (Real.exp (t*r)) (Real.exp_pos _)
  rw [integral_exp_gaussian_linear] at hh
  convert! hh using 2
  rw [← Real.exp_sub]
  congr 1
  have heq : ∑ i, (t*a i)^2 = t^2 * ∑ i, a i^2 := by
    simp only [mul_pow, Finset.mul_sum]
  rw [heq]
  ring

lemma gaussian_linear_abs_tail {ι : Type*} [Fintype ι] (v : ℝ≥0) (a : ι → ℝ)
    (r t : ℝ) (ht : 0 < t) :
    (Measure.pi (fun _ : ι => gaussianReal 0 v)) {g | r ≤ |∑ i, a i * g i|} ≤
      2 * ENNReal.ofReal (Real.exp (v * (∑ i, a i ^ 2) * t^2 / 2 - t*r)) := by
  have hs : {g : ι → ℝ | r ≤ |∑ i, a i*g i|} =
      {g | r ≤ ∑ i, a i*g i} ∪ {g | r ≤ ∑ i, (-a i)*g i} := by
    ext g
    simp only [Set.mem_ofPred_eq, Set.mem_union, neg_mul, Finset.sum_neg_distrib]
    rw [le_abs]
  rw [hs]
  have hh := gaussian_linear_upper_tail v (fun i => -a i) r t ht
  simp only [neg_sq] at hh
  calc
    _ ≤ _ + _ := measure_union_le _ _
    _ ≤ _ + _ := add_le_add (gaussian_linear_upper_tail v a r t ht) hh
    _ = _ := by rw [two_mul]

def bilinearCoefficient {n : ℕ} (x y : Fin n → ℝ) (p : Fin n × Fin n) : ℝ :=
  if p.1 < p.2 then x p.1 * y p.2 + x p.2 * y p.1 else 0

lemma bilinear_sampled {n : ℕ} (x y : Fin n → ℝ) (g : GaussianCoordinates n) :
    ∑ i, ∑ j, x i * sampledInteraction g i j * y j =
      ∑ p, bilinearCoefficient x y p * g p := by
  have hp (i j : Fin n) : x i * sampledInteraction g i j * y j =
      (if i < j then x i*y j*g (i,j) else 0) +
      (if j < i then x i*y j*g (j,i) else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [sampledInteraction, ne_of_lt h, min_eq_left h.le, max_eq_right h.le,
        h, not_lt_of_ge h.le]; ring
    · subst j; simp [sampledInteraction]
    · simp [sampledInteraction, ne_of_gt h, min_eq_right h.le, max_eq_left h.le,
        h, not_lt_of_ge h.le]; ring
  simp_rw [hp]
  simp only [Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if j < i then x i*y j*g (j,i) else 0)]
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j <;> simp [bilinearCoefficient, h, add_mul]

lemma bilinearCoefficient_sq_le {n : ℕ} (x y : Fin n → ℝ) :
    ∑ p, bilinearCoefficient x y p ^ 2 ≤
      2 * (∑ i, x i^2) * (∑ i, y i^2) := by
  have hp (i j : Fin n) : bilinearCoefficient x y (i,j)^2 +
      bilinearCoefficient x y (j,i)^2 ≤ 2 * (x i^2*y j^2 + x j^2*y i^2) := by
    rcases lt_trichotomy i j with h | h | h
    · simp only [bilinearCoefficient, h, not_lt_of_ge h.le, ite_true, ite_false, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero]
      nlinarith [sq_nonneg (x i*y j-x j*y i)]
    · subst j; simp only [bilinearCoefficient, lt_self_iff_false, ite_false, zero_pow (by decide : (2:ℕ) ≠ 0), add_zero]
      positivity
    · simp only [bilinearCoefficient, h, not_lt_of_ge h.le, ite_true, ite_false, zero_pow (by decide : (2:ℕ) ≠ 0), zero_add]
      nlinarith [sq_nonneg (x i*y j-x j*y i)]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  simp only [mul_add, Finset.sum_add_distrib] at hs
  rw [Finset.sum_comm (f := fun i j => bilinearCoefficient x y (j,i)^2)] at hs
  rw [Fintype.sum_prod_type]
  have he : ∑ i, ∑ j, 2*(x i^2*y j^2) = 2 * (∑ i, x i^2) * (∑ j, y j^2) := by
    calc
      _ = 2 * (∑ i, ∑ j, x i^2*y j^2) := by simp only [Finset.mul_sum]
      _ = 2 * ((∑ i, x i^2) * (∑ j, y j^2)) := by rw [Finset.sum_mul_sum]
      _ = _ := by ring
  have he' : ∑ i, ∑ j, 2*(x j^2*y i^2) = 2 * (∑ i, x i^2) * (∑ j, y j^2) := by
    rw [Finset.sum_comm]; exact he
  rw [he, he'] at hs
  linarith

lemma sampled_inner {n : ℕ} (x y : EuclideanSpace ℝ (Fin n)) (g : GaussianCoordinates n) :
    inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g) x) y =
      ∑ p, bilinearCoefficient y x p * g p := by
  rw [real_inner_comm, Matrix.inner_toEuclideanCLM]
  change (∑ i, y i * ∑ j, sampledInteraction g i j * x j) = _
  simp only [Finset.mul_sum, ← mul_assoc]
  exact bilinear_sampled y x g

lemma sampled_inner_tail (β : ℝ) {n : ℕ} (hn : 0 < n)
    (x y : EuclideanSpace ℝ (Fin n)) (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) :
    disorderLaw β n {g | β^2+10 ≤ |inner (𝕜 := ℝ)
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g) x) y|} ≤
      2 * ENNReal.ofReal (Real.exp (-(10:ℝ)*n)) := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hcoef : ∑ p, bilinearCoefficient y x p ^ 2 ≤ 2 := by
    have hh := bilinearCoefficient_sq_le y x
    rw [← EuclideanSpace.real_norm_sq_eq, ← EuclideanSpace.real_norm_sq_eq] at hh
    have hx2 : ‖x‖^2 ≤ 1 := by nlinarith [norm_nonneg x]
    have hy2 : ‖y‖^2 ≤ 1 := by nlinarith [norm_nonneg y]
    nlinarith [mul_le_mul hy2 hx2 (sq_nonneg ‖x‖) (by norm_num : (0:ℝ) ≤ 1)]
  simp_rw [sampled_inner]
  have hh := gaussian_linear_abs_tail (Real.toNNReal (β^2/n))
    (bilinearCoefficient y x) (β^2+10) n hnR
  refine hh.trans (mul_le_mul' (le_refl 2) (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)))
  rw [Real.coe_toNNReal _ (div_nonneg (sq_nonneg β) hnR.le)]
  have hv : β^2/(n:ℝ) * (∑ p, bilinearCoefficient y x p^2) * (n:ℝ)^2 / 2 ≤ β^2*n := by
    calc
      _ ≤ β^2/(n:ℝ) * 2 * (n:ℝ)^2 / 2 := by gcongr
      _ = _ := by field_simp
  nlinarith

lemma sampled_opNorm_tail (β : ℝ) {n : ℕ} (hn : 0 < n) :
    disorderLaw β n {g | 2*(β^2+10) < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g)‖} ≤
      ENNReal.ofReal (2 * (81:ℝ)^n * Real.exp (-(10:ℝ)*n)) := by
  classical
  obtain ⟨s, hb, hc, hs⟩ := unit_ball_net n
  let E (x y : EuclideanSpace ℝ (Fin n)) : Set (GaussianCoordinates n) :=
    {g | β^2+10 ≤ |inner (𝕜 := ℝ) (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g) x) y|}
  have hsub : {g | 2*(β^2+10) < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g)‖} ⊆
      ⋃ x ∈ s, ⋃ y ∈ s, E x y := by
    intro g hg
    by_contra hnot
    have hb' : ∀ x ∈ s, ∀ y ∈ s, |inner (𝕜 := ℝ)
        (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g) x) y| ≤ β^2+10 := by
      intro x hx y hy
      have hh : g ∉ E x y := fun hgE => hnot (Set.mem_iUnion₂.mpr
        ⟨x, hx, Set.mem_iUnion₂.mpr ⟨y, hy, hgE⟩⟩)
      exact (not_le.mp hh).le
    have hh := opNorm_le_of_net (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g)) s hb hc
      (β^2+10) (by positivity) hb'
    exact not_lt_of_ge hh hg
  have hu : disorderLaw β n (⋃ x ∈ s, ⋃ y ∈ s, E x y) ≤
      ∑ x ∈ s, ∑ y ∈ s, disorderLaw β n (E x y) := by
    refine (measure_biUnion_finset_le s _).trans ?_
    exact Finset.sum_le_sum (fun x _ => measure_biUnion_finset_le s (E x))
  refine (measure_mono hsub).trans (hu.trans ?_)
  calc
    _ ≤ ∑ _x ∈ s, ∑ _y ∈ s, 2 * ENNReal.ofReal (Real.exp (-(10:ℝ)*n)) := by
      exact Finset.sum_le_sum (fun x hx => Finset.sum_le_sum (fun y hy =>
        sampled_inner_tail β hn x y (hb x hx) (hb y hy)))
    _ = ENNReal.ofReal (2 * (s.card:ℝ)^2 * Real.exp (-(10:ℝ)*n)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (show (0:ℝ) ≤ s.card by positivity), ENNReal.ofReal_natCast]
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (by
      have hh : (s.card : ℝ)^2 ≤ (81:ℝ)^n := by
        calc
          _ ≤ ((9:ℝ)^n)^2 := pow_le_pow_left₀ (by positivity) hs 2
          _ = _ := by rw [← pow_mul, mul_comm n 2, pow_mul]; norm_num
      gcongr)

lemma sampled_opNorm_tendsto (β : ℝ) :
    Tendsto (fun n => disorderLaw β n {g |
      2*(β^2+10) < ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) (sampledInteraction g)‖})
      atTop (nhds 0) := by
  have hq : 81 * Real.exp (-10) < 1 := by
    rw [Real.exp_neg, ← div_eq_mul_inv, div_lt_one (Real.exp_pos _)]
    have h2 : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    have hp : (81:ℝ) < (Real.exp 1)^10 := (by norm_num : (81:ℝ) < 2^10).trans_le
      (pow_le_pow_left₀ (by norm_num) h2 10)
    simpa only [← Real.exp_nat_mul, Nat.cast_ofNat, mul_one] using hp
  have hlim : Tendsto (fun n : ℕ => 2 * (81:ℝ)^n * Real.exp (-(10:ℝ)*n))
      atTop (nhds 0) := by
    have hh := (tendsto_pow_atTop_nhds_zero_of_lt_one
      (by positivity : (0:ℝ) ≤ 81*Real.exp (-10)) hq).const_mul 2
    simp only [mul_zero] at hh
    convert! hh using 1
    ext n
    rw [mul_pow, ← Real.exp_nat_mul]
    rw [show (n:ℝ)*(-10) = -(10:ℝ)*n by ring]
    ring
  have hlimE : Tendsto (fun n : ℕ => ENNReal.ofReal
      (2 * (81:ℝ)^n * Real.exp (-(10:ℝ)*n))) atTop (nhds 0) := by
    convert! ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim using 1
    simp only [ENNReal.ofReal_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimE
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact sampled_opNorm_tail β hn

lemma gaussian_entry_tail (β : ℝ) {n : ℕ} (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ)
    (p : Fin n × Fin n) :
    disorderLaw β n {g | δ ≤ |g p|} ≤
      2 * ENNReal.ofReal (Real.exp (-(δ^2/(2*(β^2+1)))*(n:ℝ))) := by
  have hnR : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have hB : 0 < β^2+1 := by positivity
  have ht : 0 < δ*n/(β^2+1) := by positivity
  have hh := gaussian_linear_abs_tail (Real.toNNReal (β^2/n)) (Pi.single p 1)
    δ (δ*n/(β^2+1)) ht
  have he (g : GaussianCoordinates n) : ∑ i, (Pi.single p (1:ℝ) : (Fin n × Fin n) → ℝ) i * g i = g p := by
    simp [Pi.single_apply]
  simp only [he] at hh
  have hsq : ∑ i : Fin n × Fin n, ((Pi.single p (1:ℝ) : (Fin n × Fin n) → ℝ) i)^2 = 1 := by simp [Pi.single_apply]
  rw [hsq, mul_one, Real.coe_toNNReal _ (div_nonneg (sq_nonneg β) hnR.le)] at hh
  suffices hc : β^2/(n:ℝ) * (δ*n/(β^2+1))^2/2 - δ*n/(β^2+1)*δ ≤
      -(δ^2/(2*(β^2+1)))*(n:ℝ) from
    hh.trans (mul_le_mul' (le_refl 2) (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hc)))
  have heq : β^2/(n:ℝ) * (δ*n/(β^2+1))^2/2 - δ*n/(β^2+1)*δ =
      -(δ^2/(2*(β^2+1)))*(n:ℝ) - δ^2*n/(2*(β^2+1)^2) := by
    field_simp
    ring
  rw [heq]
  exact sub_le_self _ (by positivity)

lemma sampled_maxEntry_tail (β : ℝ) {n : ℕ} (hn : 0 < n) (δ : ℝ) (hδ : 0 < δ) :
    disorderLaw β n {g | ∃ i j, δ ≤ |sampledInteraction g i j|} ≤
      ENNReal.ofReal (2*(n:ℝ)^2 * Real.exp (-(δ^2/(2*(β^2+1)))*(n:ℝ))) := by
  have hsub : {g : GaussianCoordinates n | ∃ i j, δ ≤ |sampledInteraction g i j|} ⊆
      ⋃ p : Fin n × Fin n, {g | δ ≤ |g p|} := by
    intro g hg
    obtain ⟨i, j, hij⟩ := hg
    have hne : i ≠ j := by
      intro heq; subst j
      simp only [sampledInteraction_diag, abs_zero] at hij
      exact (not_le_of_gt hδ) hij
    exact Set.mem_iUnion.mpr ⟨(min i j, max i j), by simpa [sampledInteraction, hne] using hij⟩
  calc
    _ ≤ _ := measure_mono hsub
    _ ≤ ∑ p : Fin n × Fin n, disorderLaw β n {g | δ ≤ |g p|} := measure_iUnion_fintype_le _ _
    _ ≤ ∑ _p : Fin n × Fin n, 2 * ENNReal.ofReal (Real.exp (-(δ^2/(2*(β^2+1)))*(n:ℝ))) :=
      Finset.sum_le_sum (fun p _ => gaussian_entry_tail β hn δ hδ p)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
      simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_pow (show (0:ℝ) ≤ n by positivity),
        ENNReal.ofReal_natCast, Nat.cast_mul]
      ring

lemma sampled_maxEntry_tendsto (β : ℝ) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => disorderLaw β n {g | ∃ i j, δ ≤ |sampledInteraction g i j|})
      atTop (nhds 0) := by
  have hc : 0 < δ^2/(2*(β^2+1)) := by positivity
  have hlim : Tendsto (fun n : ℕ => 2*(n:ℝ)^2 * Real.exp (-(δ^2/(2*(β^2+1)))*(n:ℝ)))
      atTop (nhds 0) := by
    have hh := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 (δ^2/(2*(β^2+1))) hc).comp (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n:ℝ)) atTop atTop)
    have hh' := hh.const_mul 2
    convert! hh' using 1
    · ext n; dsimp only [Function.comp_def]; rw [Real.rpow_two]; ring
    · simp only [mul_zero]
  have hlimE : Tendsto (fun n : ℕ => ENNReal.ofReal
      (2*(n:ℝ)^2 * Real.exp (-(δ^2/(2*(β^2+1)))*(n:ℝ)))) atTop (nhds 0) := by
    convert! ENNReal.continuous_ofReal.continuousAt.tendsto.comp hlim using 1
    simp only [ENNReal.ofReal_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimE
    (Eventually.of_forall (fun _ => bot_le))
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact sampled_maxEntry_tail β hn δ hδ

lemma matrix_column_sq_le {n : ℕ} (J : Interaction n) (j : Fin n) :
    ∑ i, J i j^2 ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖^2 := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single j 1
  have he : ‖e‖ = 1 := by simp [e]
  have hh : ‖A e‖ ≤ ‖A‖ := by simpa only [he, mul_one] using A.le_opNorm e
  have hv : ‖A e‖^2 = ∑ i, J i j^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    have hi : A e i = J i j := by
      change (∑ k, J i k * ((Pi.single j (1:ℝ) : Fin n → ℝ) k)) = J i j
      simp [Pi.single_apply]
    rw [hi]
  rw [← hv]
  exact pow_le_pow_left₀ (norm_nonneg _) hh 2

lemma matrix_bilinear_le {n : ℕ} (J : Interaction n) (a b : Fin n → ℝ) :
    |∑ i, ∑ j, a i * J j i * b j| ≤
      ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ / 2 *
        ((∑ i, a i^2) + ∑ j, b j^2) := by
  let A := Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J
  let aE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 a
  let bE : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 b
  have he : (∑ i, ∑ j, a i * J j i * b j) = inner (𝕜 := ℝ) bE (A aE) := by
    rw [Matrix.inner_toEuclideanCLM]
    change (∑ i, ∑ j, a i * J j i * b j) = ∑ j, b j * (∑ i, J j i * a i)
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  have hh : |inner (𝕜 := ℝ) bE (A aE)| ≤ ‖A‖ * (‖aE‖ * ‖bE‖) := by
    calc
      _ ≤ ‖bE‖ * ‖A aE‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖bE‖ * (‖A‖ * ‖aE‖) := mul_le_mul_of_nonneg_left (A.le_opNorm _) (norm_nonneg _)
      _ = _ := by ring
  have hsq : ‖aE‖ * ‖bE‖ ≤ (‖aE‖^2+‖bE‖^2)/2 := by nlinarith [sq_nonneg (‖aE‖-‖bE‖)]
  have hh' := mul_le_mul_of_nonneg_left hsq (norm_nonneg A)
  rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq] at hh'
  exact hh.trans (by simpa only [aE, bE, mul_div_assoc, div_mul_eq_mul_div] using hh')

lemma matrix_entry_le_opNorm {n : ℕ} (J : Interaction n) (i j : Fin n) :
    |J i j| ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ := by
  have hh : J i j^2 ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖^2 := by
    exact (Finset.single_le_sum (f := fun i => J i j^2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ i)).trans (matrix_column_sq_le J j)
  exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp (by simpa only [sq_abs] using hh)

lemma rough_square_of_opNorm {n : ℕ} (J : Interaction n) (hJ : ∀ i j, J i j = J j i)
    (C : ℝ) (hC : 0 ≤ C) (hJC : ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℝ) J‖ ≤ C)
    (p : VectorFields n) (x : Spin n) :
    (∑ i, 2*p x i*gradientGenerator J p x i) - generator J (vectorSquare p) x ≤
      (2*(C+4*C^2)+4*(2*Real.exp (8*C)*C^2)-2) * vectorSquare p x - vectorDissipation J p x := by
  have hM (i : Fin n) : ∑ j, J j i^2 ≤ C^2 := (matrix_column_sq_le J i).trans
    (pow_le_pow_left₀ (norm_nonneg _) hJC 2)
  have hJB (a b : Fin n → ℝ) : |∑ i, ∑ j, a i*J j i*b j| ≤
      C/2*((∑ i, a i^2)+∑ j, b j^2) := by
    exact (matrix_bilinear_le J a b).trans (by gcongr)
  exact gradient_square_le J p x (C+4*C^2) (2*Real.exp (8*C)*C^2)
    (influence_quadratic_le J hJ x (p x) C (C^2) hC hJB hM)
    (influence_weighted_row_le J x C (C^2) (fun i j => (matrix_entry_le_opNorm J i j).trans hJC) hM)

lemma sampled_rough_square_good (β : ℝ) :
    let C := 2*(β^2+10)
    Tendsto (fun n => disorderLaw β n {g | ¬ ∀ (p : VectorFields n) (x : Spin n),
      (∑ i, 2*p x i*gradientGenerator (sampledInteraction g) p x i) -
        generator (sampledInteraction g) (vectorSquare p) x ≤
      (2*(C+4*C^2)+4*(2*Real.exp (8*C)*C^2)-2) * vectorSquare p x -
        vectorDissipation (sampledInteraction g) p x}) atTop (nhds 0) := by
  dsimp only
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (sampled_opNorm_tendsto β)
    (Eventually.of_forall (fun _ => bot_le))
  apply Eventually.of_forall
  intro n
  apply measure_mono
  intro g hg
  by_contra hnot
  apply hg
  exact rough_square_of_opNorm (sampledInteraction g) (sampledInteraction_symm g)
    (2*(β^2+10)) (by positivity) (le_of_not_gt hnot)

end SKGapCutoff.RandomMatrix

open scoped BigOperators NNReal ENNReal Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Filter Set

end

end OAI
