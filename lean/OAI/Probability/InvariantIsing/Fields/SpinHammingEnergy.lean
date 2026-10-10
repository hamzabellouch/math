import OAI.Probability.InvariantIsing.Pressure.PressureLipschitz

namespace OAI

/-! The deterministic energy cost of changing a prescribed number of
spins. These bounds apply to the slice comparisons in the magnetic theorem. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma spinVector_sub_norm_sq {N : ℕ} (σ τ : Spin N) :
    ‖spinVector σ - spinVector τ‖ ^ 2 = 4 * (hammingDist σ τ : ℝ) := by
  classical
  rw [EuclideanSpace.real_norm_sq_eq]
  change (∑ i, (spinValue (σ i) - spinValue (τ i)) ^ 2) = _
  have hi (i : Fin N) : (spinValue (σ i) - spinValue (τ i)) ^ 2 =
      if σ i ≠ τ i then 4 else 0 := by
    cases hσ : σ i <;> cases hτ : τ i <;> norm_num [spinValue]
  simp_rw [hi]
  simp [hammingDist, Finset.sum_ite, mul_comm]

lemma sum_abs_spinValue_sub {N : ℕ} (σ τ : Spin N) :
    (∑ i, |spinValue (σ i) - spinValue (τ i)|) = 2 * (hammingDist σ τ : ℝ) := by
  classical
  have hi (i : Fin N) : |spinValue (σ i) - spinValue (τ i)| =
      if σ i ≠ τ i then 2 else 0 := by
    cases hσ : σ i <;> cases hτ : τ i <;> norm_num [spinValue]
  simp_rw [hi]
  simp [hammingDist, Finset.sum_ite, mul_comm]

lemma abs_fieldEnergy_sub_spin_le {N : ℕ} (c : Fin N → ℝ) (σ τ : Spin N)
    {C : ℝ} (hc : ∀ i, |c i| ≤ C) :
    |fieldEnergy c σ - fieldEnergy c τ| ≤ 2 * C * (hammingDist σ τ : ℝ) := by
  have he : fieldEnergy c σ - fieldEnergy c τ =
      ∑ i, c i * (spinValue (σ i) - spinValue (τ i)) := by
    simp only [fieldEnergy, mul_sub, Finset.sum_sub_distrib]
  rw [he]
  calc
    _ ≤ ∑ i, |c i * (spinValue (σ i) - spinValue (τ i))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, C * |spinValue (σ i) - spinValue (τ i)| := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hc i) (abs_nonneg _)
    _ = 2 * C * (hammingDist σ τ : ℝ) := by
      rw [← Finset.mul_sum, sum_abs_spinValue_sub]
      ring

lemma abs_rotatedEnergy_sub_spin_le {N : ℕ} (eig : Fin N → ℝ) (U : Rotation N)
    (σ τ : Spin N) {K : ℝ} (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K) :
    |rotatedEnergy eig U σ - rotatedEnergy eig U τ| ≤
      2 * K * Real.sqrt ((N : ℝ) * (hammingDist σ τ : ℝ)) := by
  let x := U (spinVector σ)
  let y := U (spinVector τ)
  let D : ℝ := hammingDist σ τ
  have hD : 0 ≤ D := Nat.cast_nonneg _
  have hx : ∑ i, x i ^ 2 = N := rotated_spin_sq_sum U σ
  have hy : ∑ i, y i ^ 2 = N := rotated_spin_sq_sum U τ
  have hm : (∑ i, (x i - y i) ^ 2) = 4 * D := by
    calc
      _ = ‖x - y‖ ^ 2 := by rw [EuclideanSpace.real_norm_sq_eq]; rfl
      _ = 4 * D := by
        change ‖U (spinVector σ) - U (spinVector τ)‖ ^ 2 = _
        rw [← U.map_sub, U.norm_map, spinVector_sub_norm_sq]
  have hp : (∑ i, (x i + y i) ^ 2) ≤ 4 * (N : ℝ) := by
    have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show (x i + y i) ^ 2 ≤ 2 * x i ^ 2 + 2 * y i ^ 2 by
        nlinarith [sq_nonneg (x i - y i)])
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hx, hy] at hi
    linarith
  have hw : (∑ i, (eig i * (x i - y i)) ^ 2) ≤ K ^ 2 * (4 * D) := by
    rw [← hm, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_pow]
    have hb : eig i ^ 2 ≤ K ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (heig i)
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => eig i * (x i - y i)) (fun i => x i + y i)
  have hs : (∑ i, (eig i * (x i - y i)) * (x i + y i)) ^ 2 ≤
      (4 * K * Real.sqrt ((N : ℝ) * D)) ^ 2 := by
    calc
      _ ≤ (∑ i, (eig i * (x i - y i)) ^ 2) * ∑ i, (x i + y i) ^ 2 := hcs
      _ ≤ (K ^ 2 * (4 * D)) * (4 * (N : ℝ)) :=
        mul_le_mul hw hp (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
      _ = _ := by rw [mul_pow, Real.sq_sqrt (by positivity)]; ring
  have ha : |∑ i, (eig i * (x i - y i)) * (x i + y i)| ≤
      4 * K * Real.sqrt ((N : ℝ) * D) := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simpa only [sq_abs] using hs
  have he : rotatedEnergy eig U σ - rotatedEnergy eig U τ =
      (1 / 2 : ℝ) * ∑ i, (eig i * (x i - y i)) * (x i + y i) := by
    rw [rotatedEnergy, rotatedEnergy, ← mul_sub, ← Finset.sum_sub_distrib]
    change (1 / 2 : ℝ) * (∑ i, (eig i * x i ^ 2 - eig i * y i ^ 2)) = _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact (mul_le_mul_of_nonneg_left ha (by norm_num)).trans_eq (by dsimp [D]; ring)

end InvariantIsing

end

end OAI
