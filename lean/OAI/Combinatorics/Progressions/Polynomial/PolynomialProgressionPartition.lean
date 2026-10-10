import OAI.Combinatorics.Progressions.Polynomial.PolynomialCoordinatePartition

namespace OAI

section

namespace Erdos3

universe u

open Polynomial
open scoped NNReal

def PolynomialProgressionPartitionBound (k : ℕ) (K : ℝ) (p : ℕ) : Prop :=
  ∀ (ι : Type u) [Fintype ι] (P : ι → Polynomial ℝ),
    (∀ i, (P i).natDegree ≤ k) → ∀ (N H : ℕ), 0 < H →
    K * ((Fintype.card ι : ℝ) + 1) ≤ H →
    H ^ (p * (Fintype.card ι + 1) ^ (2 * k)) ≤ N →
    ∀ (F : (ι → ℝ) → ℝ) (L : ℝ≥0), LipschitzWith L F →
    (∀ x : ι → ℝ, ∀ m : ι → ℤ, F (fun i => x i + m i) = F x) →
    (∀ x, F x ∈ Set.Icc (0 : ℝ) 1) →
    ∃ (Q : FiniteProgressionPartition N) (c : Q.Label → ℝ),
      Fintype.card Q.Label * H ≤ 2 ^ k * N ∧
      (∀ i, c i ∈ Set.Icc (0 : ℝ) 1) ∧
      ∀ i n, n < Q.length i →
        dist (F (fun j => (P j).eval ((Q.start i + Q.step i * n : ℕ) : ℝ))) (c i) ≤
          (k : ℝ) * L / H

theorem polynomialProgressionPartitionBound_zero : PolynomialProgressionPartitionBound.{u} 0 1 1 := by
  intro ι _ P hP N H hH hscale hsize F L hF hperiod hF01
  have hHN : H ≤ N := by simpa using hsize
  refine ⟨FiniteProgressionPartition.whole N, (fun _ => F (fun i => (P i).coeff 0)), ?_, ?_, ?_⟩
  · have hcard : Fintype.card (FiniteProgressionPartition.whole N).Label = 1 := by
      let : Unique (FiniteProgressionPartition.whole N).Label := inferInstanceAs (Unique Unit)
      exact Fintype.card_unique
    rw [hcard]
    simpa using hHN
  · intro i
    exact hF01 _
  · intro i n hn
    have heq (x : ℝ) : (fun j => (P j).eval x) = fun j => (P j).coeff 0 := by
      funext j
      simpa only [eval_C] using congrArg (fun Q : Polynomial ℝ => Q.eval x)
        (eq_C_of_natDegree_le_zero (hP j))
    rw [heq]
    simp

theorem PolynomialProgressionPartitionBound.step {k p C e : ℕ} {K : ℝ}
    (hp : 0 < p) (hpartition : PolynomialProgressionPartitionBound.{u} k K p)
    (hW : PolynomialIntervalPowerBound (k + 1) C e) :
    PolynomialProgressionPartitionBound.{u} (k + 1) (max K (schmidtRecurrenceBase C e))
      (p * ((k + 3) * schmidtRecurrenceExponent e + 1)) := by
  intro ι _ P hP N H hH hscale hsize F L hF hperiod hF01
  let d := Fintype.card ι
  let r := p * (d + 1) ^ (2 * k)
  let T := H ^ r
  have hr : 0 < r := Nat.mul_pos hp (pow_pos (by omega : 0 < d + 1) _)
  have hT : 0 < T := pow_pos hH _
  have hHT : H ≤ T := by
    simpa only [pow_one] using (show H ^ 1 ≤ H ^ r from pow_le_pow_right₀ (by omega) (by omega))
  have hscaleK : K * ((Fintype.card ι : ℝ) + 1) ≤ H :=
    (mul_le_mul_of_nonneg_right (le_max_left K _) (by positivity)).trans hscale
  have hscaleW : schmidtRecurrenceBase C e * ((Fintype.card ι : ℝ) + 1) ≤ T := by
    have h := (mul_le_mul_of_nonneg_right (le_max_right K _) (by positivity)).trans hscale
    exact h.trans (by exact_mod_cast hHT)
  have hsizeT : T ^ (((k + 3) * schmidtRecurrenceExponent e * (d + 1) ^ 2) + 1) ≤ N := by
    apply le_trans _ hsize
    change (H ^ r) ^ _ ≤ H ^ _
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by omega) (polynomial_partition_exponent_step k p (schmidtRecurrenceExponent e) d)
  obtain ⟨q, hq, hqbound, hreduce⟩ := hW.polynomial_progression_reduction P hP T hT hscaleW hF hperiod
  have hfit : q * T ≤ N := by
    calc
      _ ≤ T ^ ((k + 3) * schmidtRecurrenceExponent e * (d + 1) ^ 2) * T :=
        Nat.mul_le_mul_right T hqbound
      _ = T ^ (((k + 3) * schmidtRecurrenceExponent e * (d + 1) ^ 2) + 1) := (pow_succ _ _).symm
      _ ≤ N := hsizeT
  let B := FiniteProgressionPartition.blocks N q T hq hT
  have hBlength (i : B.Label) : B.length i ≤ T := truncatedProgressionLength_le _ _ _ _
  have hBcard : Fintype.card B.Label * T ≤ 2 * N := progressionBlock_label_count_mul_le_twice hfit
  choose R hRdegree hRerror using (fun i : B.Label => hreduce (B.start i : ℝ))
  have hlocal (i : B.Label) := hpartition ι (R i) (hRdegree i) T H hH hscaleK le_rfl F L hF hperiod hF01
  choose Q c hQcard hc hQerror using hlocal
  let child (i : B.Label) := (Q i).restrict (B.length i) (hBlength i)
  let result := B.bind child
  refine ⟨result, (fun i => c i.1 i.2), ?_, ?_, ?_⟩
  · have hchild (i : B.Label) : Fintype.card (child i).Label * H ≤ 2 ^ k * T := hQcard i
    calc
      Fintype.card result.Label * H ≤ Fintype.card B.Label * (2 ^ k * T) :=
        B.bind_card_mul_le child H _ hchild
      _ = 2 ^ k * (Fintype.card B.Label * T) := by ring
      _ ≤ 2 ^ k * (2 * N) := Nat.mul_le_mul_left _ hBcard
      _ = 2 ^ (k + 1) * N := by rw [pow_succ]; ring
  · intro i
    exact hc i.1 i.2
  · rintro ⟨i, j⟩ n hn
    let s := (child i).start j + (child i).step j * n
    have hsB : s < B.length i := (child i).point_lt j hn
    have hsT : s < T := hsB.trans_le (hBlength i)
    have houter := hRerror i s hsT
    have hnQ : n < (Q i).length j := hn.trans_le ((Q i).restrict_length_le _ (hBlength i) j)
    have hinner := hQerror i j n hnQ
    change dist (F (fun z => (R i z).eval (s : ℝ))) (c i j) ≤ (k : ℝ) * L / H at hinner
    have hindex : result.start ⟨i, j⟩ + result.step ⟨i, j⟩ * n = B.start i + q * s := by
      change (B.start i + q * (child i).start j) + (q * (child i).step j) * n = _
      dsimp [s]
      ring
    rw [hindex]
    have houter' : dist (F (fun z => (P z).eval ((B.start i + q * s : ℕ) : ℝ)))
        (F (fun z => (R i z).eval (s : ℝ))) ≤ (L : ℝ) / T := by
      simpa only [Nat.cast_add, Nat.cast_mul] using houter
    calc
      _ ≤ dist (F (fun z => (P z).eval ((B.start i + q * s : ℕ) : ℝ)))
          (F (fun z => (R i z).eval (s : ℝ))) +
          dist (F (fun z => (R i z).eval (s : ℝ))) (c i j) := dist_triangle _ _ _
      _ ≤ (L : ℝ) / T + (k : ℝ) * L / H := add_le_add houter' hinner
      _ ≤ _ := polynomial_partition_error_step k L.coe_nonneg hH hHT

theorem exists_polynomial_progression_partition_bound (k : ℕ) :
    ∃ (K : ℝ) (p : ℕ), 1 ≤ K ∧ 0 < p ∧ PolynomialProgressionPartitionBound.{u} k K p := by
  induction k with
  | zero => exact ⟨1, 1, le_rfl, by decide, polynomialProgressionPartitionBound_zero⟩
  | succ k ih =>
    obtain ⟨K, p, hK, hp, hpartition⟩ := ih
    obtain ⟨C, e, hC, he, hW⟩ := polynomial_weyl_inverse_power_interval k
    exact ⟨max K (schmidtRecurrenceBase C e), p * ((k + 3) * schmidtRecurrenceExponent e + 1),
      hK.trans (le_max_left _ _), Nat.mul_pos hp (by omega), hpartition.step hp hW⟩

end Erdos3

end

end OAI
