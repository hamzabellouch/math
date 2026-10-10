import OAI.Probability.InvariantIsing.Arrays.PerturbationWeights
import OAI.Probability.InvariantIsing.Arrays.OverlapBounds

namespace OAI

/-! The deterministic spectral-diagonal perturbation as an exact eigenvalue shift. -/

noncomputable section

open IsingPerceptron
open scoped BigOperators

namespace InvariantIsing

def diagonalPerturbedEigenvalues {N m : ℕ} (eig : Fin N → ℝ)
    (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ) (t : ℝ) (i : Fin N) : ℝ :=
  t * eig i + 2 * perturbationScale N * ∑ a, if i ∈ I a then v a else 0

/-- This is the first term of the manuscript's perturbation, including
its coefficient `N e_N`, in the actual rotated Ising Hamiltonian. -/
theorem rotatedEnergy_diagonalPerturbation {N m : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (I : Fin m → Finset (Fin N))
    (v : Fin m → ℝ) (t : ℝ) (σ : Spin N) :
    rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U σ =
      t * rotatedEnergy eig U σ + N * perturbationScale N * ∑ a, v a * projectedOverlap U (I a) σ σ := by
  classical
  have hn : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  unfold rotatedEnergy diagonalPerturbedEigenvalues projectedOverlap
  simp_rw [add_mul, Finset.sum_add_distrib]
  have he : (∑ i, (2 * perturbationScale N * ∑ a, if i ∈ I a then v a else 0) *
      U (spinVector σ) i ^ 2) =
      2 * perturbationScale N * ∑ a, v a * ∑ i ∈ I a, U (spinVector σ) i ^ 2 := by
    calc
      _ = (2 * perturbationScale N) *
          ∑ i, ∑ a, (if i ∈ I a then v a else 0) * U (spinVector σ) i ^ 2 := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
      _ = (2 * perturbationScale N) *
          ∑ a, ∑ i, (if i ∈ I a then v a else 0) * U (spinVector σ) i ^ 2 := by
        rw [Finset.sum_comm]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        simp only [ite_mul, zero_mul, Finset.sum_ite_mem, Finset.univ_inter]
  rw [he]
  simp_rw [← pow_two]
  have hl : (∑ i, t * eig i * U (spinVector σ) i ^ 2) =
      t * ∑ i, eig i * U (spinVector σ) i ^ 2 := by
    simp only [Finset.mul_sum, mul_assoc]
  have hs : (∑ a, v a * ((N : ℝ)⁻¹ * ∑ i ∈ I a, U (spinVector σ) i ^ 2)) =
      (N : ℝ)⁻¹ * ∑ a, v a * ∑ i ∈ I a, U (spinVector σ) i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hl, hs]
  field_simp [hn]

lemma diagonalPerturbedEigenvalues_abs_le {N m : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (I : Fin m → Finset (Fin N)) (v : Fin m → ℝ)
    (hv : ∀ a, |v a| ≤ 2) (t : ℝ) (ht : |t| ≤ 1)
    (K : ℝ) (heig : ∀ i, |eig i| ≤ K) (i : Fin N) :
    |diagonalPerturbedEigenvalues eig I v t i| ≤ K + 4 * m := by
  have hs : |∑ a, if i ∈ I a then v a else 0| ≤ 2 * m := by
    calc
      _ ≤ ∑ a, |if i ∈ I a then v a else 0| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin m, (2 : ℝ) := Finset.sum_le_sum fun a _ => by
        split_ifs
        · exact hv a
        · norm_num
      _ = _ := by simp; ring
  have hp : 0 ≤ perturbationScale N := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have htE : |t * eig i| ≤ K := by
    rw [abs_mul]
    exact (mul_le_mul ht (heig i) (abs_nonneg _) (by norm_num)).trans_eq (one_mul _)
  have hshift : |2 * perturbationScale N * ∑ a, if i ∈ I a then v a else 0| ≤ 4 * m := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg (by norm_num) hp)]
    calc
      _ ≤ (2 * perturbationScale N) * (2 * m) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 2 * (2 * m) := by
        exact mul_le_mul_of_nonneg_right
          (by simpa only [mul_one] using
            (mul_le_mul_of_nonneg_left (perturbationScale_le_one hN)
              (show (0 : ℝ) ≤ 2 by norm_num))) (show 0 ≤ 2 * (m : ℝ) by positivity)
      _ = _ := by ring
  exact (abs_add_le _ _).trans (add_le_add htE hshift)

/-- Replacing one diagonal coordinate adds exactly its bounded observable,
even when all other spectral coordinates and the temperature are present. -/
lemma rotatedEnergy_diagonal_coordinate {N m : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (I : Fin m → Finset (Fin N))
    (v : Fin m → ℝ) (t : ℝ) (a : Fin m) (w : ℝ) (σ : Spin N) :
    rotatedEnergy (diagonalPerturbedEigenvalues eig I (Function.update v a w) t) U σ =
      rotatedEnergy (diagonalPerturbedEigenvalues eig I (Function.update v a 0) t) U σ +
        N * perturbationScale N * w * projectedOverlap U (I a) σ σ := by
  classical
  rw [rotatedEnergy_diagonalPerturbation hN, rotatedEnergy_diagonalPerturbation hN]
  have hs : (∑ b, Function.update v a w b * projectedOverlap U (I b) σ σ) =
      (∑ b, Function.update v a 0 b * projectedOverlap U (I b) σ σ) +
        w * projectedOverlap U (I a) σ σ := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a),
      ← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
    simp only [Function.update_self, zero_mul, add_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro b hb
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    simp only [Function.update_of_ne hba]
  rw [hs]
  ring

lemma abs_rotatedEnergy_diagonalPerturbation_le {N m : ℕ} (hN : 0 < N)
    (eig : Fin N → ℝ) (U : Rotation N) (I : Fin m → Finset (Fin N))
    (v : Fin m → ℝ) (hv : ∀ a, |v a| ≤ 2) (t : ℝ) (σ : Spin N) :
    |rotatedEnergy (diagonalPerturbedEigenvalues eig I v t) U σ - t * rotatedEnergy eig U σ| ≤
      2 * m * N * perturbationScale N := by
  have he : 0 ≤ perturbationScale N := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hs : |∑ a, v a * projectedOverlap U (I a) σ σ| ≤ 2 * m := by
    calc
      _ ≤ ∑ a, |v a * projectedOverlap U (I a) σ σ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin m, (2 : ℝ) := Finset.sum_le_sum fun a _ => by
        rw [abs_mul]
        exact (mul_le_mul (hv a) (projectedOverlap_abs_le_one U (I a) σ σ)
          (abs_nonneg _) (by norm_num)).trans_eq (mul_one _)
      _ = _ := by simp; ring
  rw [rotatedEnergy_diagonalPerturbation hN, add_sub_cancel_left, abs_mul,
    abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) he)]
  exact (mul_le_mul_of_nonneg_left hs (mul_nonneg (Nat.cast_nonneg _) he)).trans_eq (by ring)

end InvariantIsing

end

end OAI
