import Mathlib

namespace OAI

section
noncomputable section
open scoped BigOperators NNReal ENNReal
open MeasureTheory Metric Set
namespace SKRatio.MatrixNet

lemma separated_card_le {n : ℕ} (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hb : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hs : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → (1/4:ℝ) < dist x y) :
    (s.card : ℝ) ≤ (9:ℝ)^n := by
  have hd : Set.PairwiseDisjoint (↑s) (fun x : EuclideanSpace ℝ (Fin n) => ball x (1/8)) := by
    intro x hx y hy hxy
    exact ball_disjoint_ball (by linarith [hs x hx y hy hxy])
  have hsub : (⋃ x ∈ s, ball x (1/8)) ⊆ ball (0 : EuclideanSpace ℝ (Fin n)) (9/8) := by
    intro y hy
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.mp hy
    have h := dist_triangle y x (0 : EuclideanSpace ℝ (Fin n))
    simp only [mem_ball, dist_zero_right] at hy h ⊢
    linarith [hb x hx]
  have hm := measureReal_mono (μ := volume) hsub measure_ball_ne_top
  rw [measureReal_biUnion_finset hd (fun _ _ => measurableSet_ball)] at hm
  have hvol (x : EuclideanSpace ℝ (Fin n)) (r : ℝ) (hr : 0 < r) :
      volume.real (ball x r) = r ^ n * volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    simp only [measureReal_def, Measure.addHaar_ball_of_pos volume x hr,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _), finrank_euclideanSpace,
      Fintype.card_fin]
  simp only [hvol _ _ (by norm_num : (0:ℝ) < 1/8),
    hvol _ _ (by norm_num : (0:ℝ) < 9/8), Finset.sum_const, nsmul_eq_mul] at hm
  have hp : 0 < volume.real (ball (0 : EuclideanSpace ℝ (Fin n)) 1) := by
    exact ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_ne_top
  have hh : (s.card : ℝ) * (1/8:ℝ)^n ≤ (9/8:ℝ)^n :=
    (mul_le_mul_iff_left₀ hp).mp (by simpa only [mul_assoc] using hm)
  have he : (9/8:ℝ)^n = (9:ℝ)^n * (1/8:ℝ)^n := by rw [← mul_pow]; congr 1; norm_num
  rw [he] at hh
  exact (mul_le_mul_iff_left₀ (show 0 < (1/8:ℝ)^n by positivity)).mp
    (by simpa only [mul_comm] using hh)

lemma unit_ball_net (n : ℕ) :
    ∃ s : Finset (EuclideanSpace ℝ (Fin n)),
      (∀ x ∈ s, ‖x‖ ≤ 1) ∧
      (∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ 1/4) ∧
      (s.card : ℝ) ≤ (9:ℝ)^n := by
  classical
  let A := closedBall (0 : EuclideanSpace ℝ (Fin n)) 1
  obtain ⟨C, _, hCf, hC⟩ := exists_finite_isCover_of_isCompact
    (by norm_num : (1/8 : ℝ≥0) ≠ 0) (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)
  have hpack : packingNumber (1/4 : ℝ≥0) A ≠ ⊤ := by
    have hle := (packingNumber_two_mul_le_externalCoveringNumber (1/8 : ℝ≥0) A).trans
      hC.externalCoveringNumber_le_encard
    norm_num only [show (2:ℝ≥0)*(1/8) = 1/4 by norm_num] at hle
    exact ne_top_of_le_ne_top (Set.encard_ne_top_iff.mpr hCf) hle

  let D := maximalSeparatedSet (1/4 : ℝ≥0) A
  have hDf : D.Finite := Set.encard_ne_top_iff.mp (by
    rw [show D = maximalSeparatedSet (1/4 : ℝ≥0) A from rfl, encard_maximalSeparatedSet hpack]
    exact hpack)
  refine ⟨hDf.toFinset, ?_, ?_, ?_⟩
  · intro x hx
    have h := maximalSeparatedSet_subset (ε := (1/4 : ℝ≥0)) (A := A) (hDf.mem_toFinset.mp hx)
    simpa only [A, mem_closedBall, dist_zero_right] using h
  · intro x hx
    have hxA : x ∈ A := by simpa only [A, mem_closedBall, dist_zero_right] using hx
    obtain ⟨y, hy, hdist⟩ := isCover_maximalSeparatedSet hpack hxA
    refine ⟨y, hDf.mem_toFinset.mpr hy, ?_⟩
    change edist x y ≤ ((1/4 : ℝ≥0) : ℝ≥0∞) at hdist
    have h := ENNReal.toReal_mono (by norm_num : ((1/4 : ℝ≥0) : ℝ≥0∞) ≠ ⊤) hdist
    simpa only [edist_dist, ENNReal.toReal_ofReal (dist_nonneg : 0 ≤ dist x y),
      ENNReal.coe_toReal, NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using h
  · apply separated_card_le
    · intro x hx
      have h := maximalSeparatedSet_subset (ε := (1/4 : ℝ≥0)) (A := A) (hDf.mem_toFinset.mp hx)
      simpa only [A, mem_closedBall, dist_zero_right] using h
    · intro x hx y hy hxy
      have h := isSeparated_maximalSeparatedSet (ε := (1/4 : ℝ≥0)) (A := A)
        (hDf.mem_toFinset.mp hx) (hDf.mem_toFinset.mp hy) hxy
      simpa only [edist_dist, ENNReal.coe_lt_ofReal, NNReal.coe_div, NNReal.coe_one,
        NNReal.coe_ofNat] using h

lemma opNorm_le_of_net {n : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    (s : Finset (EuclideanSpace ℝ (Fin n)))
    (hb : ∀ x ∈ s, ‖x‖ ≤ 1)
    (hcover : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ∃ y ∈ s, dist x y ≤ 1/4)
    (M : ℝ) (hM : 0 ≤ M)
    (hnet : ∀ x ∈ s, ∀ y ∈ s, |inner (𝕜 := ℝ) (A x) y| ≤ M) : ‖A‖ ≤ 2*M := by
  have hh : ‖A‖ ≤ M + ‖A‖/2 := by
    apply ContinuousLinearMap.opNorm_le_of_re_inner_le (by positivity)
    intro x y hx hy
    obtain ⟨a, ha, hxa⟩ := hcover x hx.le
    obtain ⟨b, hb', hyb⟩ := hcover y hy.le
    have hxan : ‖x-a‖ ≤ 1/4 := by simpa only [dist_eq_norm] using hxa
    have hybn : ‖y-b‖ ≤ 1/4 := by simpa only [dist_eq_norm] using hyb
    have h₁ : |inner (𝕜 := ℝ) (A (x-a)) y| ≤ ‖A‖/4 := by
      calc
        _ ≤ ‖A (x-a)‖ * ‖y‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖x-a‖) * ‖y‖ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖A‖/4 := by rw [hy, mul_one]; nlinarith [norm_nonneg A]
    have h₂ : |inner (𝕜 := ℝ) (A a) (y-b)| ≤ ‖A‖/4 := by
      calc
        _ ≤ ‖A a‖ * ‖y-b‖ := abs_real_inner_le_norm _ _
        _ ≤ (‖A‖ * ‖a‖) * ‖y-b‖ := mul_le_mul_of_nonneg_right (A.le_opNorm _) (norm_nonneg _)
        _ ≤ ‖A‖ * (1:ℝ) * (1/4) := mul_le_mul
          (mul_le_mul_of_nonneg_left (hb a ha) (norm_nonneg A)) hybn (norm_nonneg _) (by positivity)
        _ = ‖A‖/4 := by ring
    have he : inner (𝕜 := ℝ) (A x) y = inner (𝕜 := ℝ) (A (x-a)) y +
        inner (𝕜 := ℝ) (A a) (y-b) + inner (𝕜 := ℝ) (A a) b := by
      simp only [map_sub, inner_sub_left, inner_sub_right]; ring
    change inner (𝕜 := ℝ) (A x) y ≤ M + ‖A‖/2
    rw [he]
    have hh := hnet a ha b hb'
    linarith [le_abs_self (inner (𝕜 := ℝ) (A (x-a)) y),
      le_abs_self (inner (𝕜 := ℝ) (A a) (y-b)), le_abs_self (inner (𝕜 := ℝ) (A a) b)]
  linarith

lemma opNorm_tail_of_bilinear {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {n : ℕ} (A : Ω → EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
    {u : ℝ} (hu : 0 ≤ u) (P : ℝ≥0∞)
    (h : ∀ x y : EuclideanSpace ℝ (Fin n), ‖x‖ ≤ 1 → ‖y‖ ≤ 1 →
      μ {ω | u ≤ |inner (𝕜 := ℝ) (A ω x) y|} ≤ P) :
    μ {ω | 2*u < ‖A ω‖} ≤ (81:ℝ≥0∞)^n*P := by
  classical
  obtain ⟨s,hb,hc,hs⟩ := unit_ball_net n
  let E (x y : EuclideanSpace ℝ (Fin n)) : Set Ω :=
    {ω | u ≤ |inner (𝕜 := ℝ) (A ω x) y|}
  have hsub : {ω | 2*u < ‖A ω‖} ⊆ ⋃ x ∈ s, ⋃ y ∈ s, E x y := by
    intro ω hω
    by_contra hn
    have hnet : ∀ x ∈ s, ∀ y ∈ s, |inner (𝕜 := ℝ) (A ω x) y| ≤ u := by
      intro x hx y hy
      have he : ω ∉ E x y := fun hh => hn
        (mem_iUnion₂.mpr ⟨x,hx,mem_iUnion₂.mpr ⟨y,hy,hh⟩⟩)
      exact (not_le.mp he).le
    exact not_lt_of_ge (opNorm_le_of_net (A ω) s hb hc u hu hnet) hω
  have hs2 : (s.card:ℝ)^2 ≤ (81:ℝ)^n := by
    calc
      _ ≤ ((9:ℝ)^n)^2 := pow_le_pow_left₀ (by positivity) hs 2
      _ = _ := by rw [←pow_mul,mul_comm n 2,pow_mul]; norm_num
  have hsE : (s.card : ℝ≥0∞)^2 ≤ (81:ℝ≥0∞)^n := by
    simpa only [ENNReal.ofReal_pow (Nat.cast_nonneg s.card),
      ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 81),
      ENNReal.ofReal_natCast, ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hs2
  calc
    _ ≤ μ (⋃ x ∈ s, ⋃ y ∈ s, E x y) := measure_mono hsub
    _ ≤ ∑ x ∈ s, ∑ y ∈ s, μ (E x y) :=
      (measure_biUnion_finset_le s _).trans
        (Finset.sum_le_sum (fun x _ => measure_biUnion_finset_le s (E x)))
    _ ≤ ∑ _x ∈ s, ∑ _y ∈ s, P := Finset.sum_le_sum
      (fun x hx => Finset.sum_le_sum (fun y hy => h x y (hb x hx) (hb y hy)))
    _ = (s.card:ℝ≥0∞)^2*P := by simp only [Finset.sum_const,nsmul_eq_mul]; ring
    _ ≤ _ := mul_le_mul' hsE le_rfl

lemma matrix_opNorm_le_schur {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (R : ℝ) (hR : 0 ≤ R)
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

end SKRatio.MatrixNet

end
end

end OAI
