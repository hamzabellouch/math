import OAI.Probability.InvariantIsing.Haar.MatrixRotation

namespace OAI

/-!
# Frobenius continuity of Haar pressure

The Lipschitz constant is independent of dimension and of a deterministic
magnetic field. This is the finite-volume estimate required to apply the
published SO(N) concentration input.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Matrix

namespace InvariantIsing

lemma specialRotation_spin_dist_sq_le {N : ℕ} (U V : SpecialOrthogonal N)
    (σ : Spin N) :
    (∑ i, (specialRotation U (spinVector σ) i -
      specialRotation V (spinVector σ) i) ^ 2) ≤
      (N : ℝ) * frobeniusDistance U V ^ 2 := by
  have he (i : Fin N) : specialRotation U (spinVector σ) i -
      specialRotation V (spinVector σ) i =
      ∑ j, ((U : Matrix (Fin N) (Fin N) ℝ) i j -
        (V : Matrix (Fin N) (Fin N) ℝ) i j) * spinValue (σ j) := by
    simp only [specialRotation_apply, spinVector_apply, sub_mul, Finset.sum_sub_distrib]
  have hrow (i : Fin N) := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun j => (U : Matrix (Fin N) (Fin N) ℝ) i j -
      (V : Matrix (Fin N) (Fin N) ℝ) i j) (fun j => spinValue (σ j))
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hrow i)
  simp only [spinValue_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one, ← Finset.sum_mul] at hsum
  simp_rw [he]
  rw [frobeniusDistance, Real.sq_sqrt (Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => sq_nonneg _)]
  nlinarith

lemma abs_rotatedEnergy_sub_rotation_le {N : ℕ} (eig : Fin N → ℝ)
    (U V : SpecialOrthogonal N) (K : ℝ) (hK : 0 ≤ K)
    (heig : ∀ i, |eig i| ≤ K) (σ : Spin N) :
    |rotatedEnergy eig (specialRotation U) σ -
      rotatedEnergy eig (specialRotation V) σ| ≤
      K * N * frobeniusDistance U V := by
  let x := specialRotation U (spinVector σ)
  let y := specialRotation V (spinVector σ)
  let d := frobeniusDistance U V
  have hd : 0 ≤ d := Real.sqrt_nonneg _
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hx : ∑ i, x i ^ 2 = N := rotated_spin_sq_sum _ _
  have hy : ∑ i, y i ^ 2 = N := rotated_spin_sq_sum _ _
  have hm : (∑ i, (x i - y i) ^ 2) ≤ (N : ℝ) * d ^ 2 :=
    specialRotation_spin_dist_sq_le U V σ
  have hp : (∑ i, (x i + y i) ^ 2) ≤ 4 * (N : ℝ) := by
    have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
      show (x i + y i) ^ 2 ≤ 2 * x i ^ 2 + 2 * y i ^ 2 by
        nlinarith [sq_nonneg (x i - y i)])
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hx, hy] at hi
    linarith
  have hw : (∑ i, (eig i * (x i - y i)) ^ 2) ≤
      K ^ 2 * ∑ i, (x i - y i) ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [mul_pow]
    have hb : eig i ^ 2 ≤ K ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hK).mpr (heig i)
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => eig i * (x i - y i)) (fun i => x i + y i)
  have hs : (∑ i, (eig i * (x i - y i)) * (x i + y i)) ^ 2 ≤
      (2 * K * (N : ℝ) * d) ^ 2 := by
    calc
      _ ≤ (∑ i, (eig i * (x i - y i)) ^ 2) * ∑ i, (x i + y i) ^ 2 := hcs
      _ ≤ (K ^ 2 * ∑ i, (x i - y i) ^ 2) * (4 * (N : ℝ)) :=
        mul_le_mul hw hp (Finset.sum_nonneg fun i _ => sq_nonneg _) (by positivity)
      _ ≤ (K ^ 2 * ((N : ℝ) * d ^ 2)) * (4 * (N : ℝ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (sq_nonneg _))
          (by positivity)
      _ = _ := by ring
  have ha : |∑ i, (eig i * (x i - y i)) * (x i + y i)| ≤
      2 * K * (N : ℝ) * d := by
    apply (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp
    simpa only [sq_abs] using hs
  have he : rotatedEnergy eig (specialRotation U) σ -
      rotatedEnergy eig (specialRotation V) σ =
      (1 / 2 : ℝ) * ∑ i, (eig i * (x i - y i)) * (x i + y i) := by
    rw [rotatedEnergy, rotatedEnergy, ← mul_sub, ← Finset.sum_sub_distrib]
    change (1 / 2 : ℝ) * (∑ i, (eig i * x i ^ 2 - eig i * y i ^ 2)) = _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [he, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  exact (mul_le_mul_of_nonneg_left ha (by norm_num)).trans_eq (by dsimp [d]; ring)

lemma abs_rotatedPressure_sub_rotation_le {N : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U V : SpecialOrthogonal N) (c : Fin N → ℝ)
    (K : ℝ) (hK : 0 ≤ K) (heig : ∀ i, |eig i| ≤ K) :
    |rotatedPressure eig (specialRotation U) c -
      rotatedPressure eig (specialRotation V) c| ≤ K * frobeniusDistance U V := by
  have h := abs_logPartition_sub_le
    (fun σ => rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ)
    (fun σ => rotatedEnergy eig (specialRotation V) σ + fieldEnergy c σ)
    (K * N * frobeniusDistance U V) (fun σ => by
      simpa only [add_sub_add_right_eq_sub] using
        abs_rotatedEnergy_sub_rotation_le eig U V K hK heig σ)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  calc
    _ = (N : ℝ)⁻¹ * |logPartition (fun σ =>
        rotatedEnergy eig (specialRotation U) σ + fieldEnergy c σ) -
        logPartition (fun σ => rotatedEnergy eig (specialRotation V) σ + fieldEnergy c σ)| := by
      rw [rotatedPressure, rotatedPressure, ← mul_sub, abs_mul,
        abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)]
    _ ≤ (N : ℝ)⁻¹ * (K * N * frobeniusDistance U V) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = K * frobeniusDistance U V := by field_simp

end InvariantIsing

end

end OAI
