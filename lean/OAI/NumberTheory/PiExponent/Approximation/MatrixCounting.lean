import OAI.NumberTheory.PiExponent.Approximation.MatrixArithmetic
import OAI.NumberTheory.PiExponent.Polynomials.SimplexRational

namespace OAI

open scoped BigOperators
open Filter Topology

namespace PiExponent.MatrixCounting

noncomputable def rowCount {m : ℕ} (K : ℕ) (v0 θ : ℚ)
    (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  Fintype.card (InterpolationMatrix.Row K (v0 : ℝ) (θ : ℝ) (MatrixArithmetic.logWeights q) H)

noncomputable def lowIndexCount {m : ℕ} (A : ℚ) (q : Fin m → ℕ) (H : ℝ) : ℝ :=
  (realWeightedSimplex (MatrixArithmetic.logWeights q) ((A : ℝ) * H)).card

noncomputable def rationalLogWeights {m : ℕ} (q : Fin m → ℕ) (i : Fin m) : ℚ :=
  (⌈Real.log (q i)⌉₊ : ℚ)

@[simp] theorem rationalLogWeights_cast {m : ℕ} (q : Fin m → ℕ) (i : Fin m) :
    (rationalLogWeights q i : ℝ) = MatrixArithmetic.logWeights q i := by
  simp [rationalLogWeights, MatrixArithmetic.logWeights]

theorem rationalLogWeights_pos {m : ℕ} (q : Fin m → ℕ) (hq : ∀ i, 2 ≤ q i)
    (i : Fin m) : 0 < rationalLogWeights q i := by
  have h := MatrixArithmetic.ceil_log_weight_pos (hq i)
  unfold rationalLogWeights
  exact_mod_cast h

theorem tendsto_rowCount_normalized {m : ℕ} (K : ℕ) (v0 θ : ℚ)
    (q : Fin m → ℕ) (hv0 : 0 < v0) (hθ : 0 < θ) (hq : ∀ i, 2 ≤ q i) :
    Tendsto (fun H : ℝ => rowCount K v0 θ q H / H ^ (m + 1)) atTop
      (𝓝 ((K : ℝ) * (θ : ℝ) ^ m /
        (((m + 1).factorial : ℝ) * (v0 : ℝ) * ∏ i, MatrixArithmetic.logWeights q i))) := by
  let V : Fin (m + 1) → ℚ := Fin.cases v0 (fun i => rationalLogWeights q i / θ)
  have hV : ∀ i, 0 < V i := by
    intro i
    exact Fin.cases hv0 (fun j => div_pos (rationalLogWeights_pos q hq j) hθ) i
  have hcast : (fun i => (V i : ℝ)) =
      InterpolationMatrix.rowWeights (v0 : ℝ) (θ : ℝ) (MatrixArithmetic.logWeights q) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [V, InterpolationMatrix.rowWeights]
    · simp [V, InterpolationMatrix.rowWeights]
  have hp : ∏ i, (V i : ℝ) =
      (v0 : ℝ) * (∏ i, MatrixArithmetic.logWeights q i) / (θ : ℝ) ^ m := by
    rw [Fin.prod_univ_succ]
    simp [V, Finset.prod_div_distrib, mul_div_assoc]
  have ht := (tendsto_card_strictWeightedSimplex_rational V hV).const_mul (K : ℝ)
  have hθ0 : (θ : ℝ) ≠ 0 := by exact_mod_cast hθ.ne'
  have he : (K : ℝ) * (1 / (((m + 1).factorial : ℝ) * ∏ i, (V i : ℝ))) =
      (K : ℝ) * (θ : ℝ) ^ m /
        (((m + 1).factorial : ℝ) * (v0 : ℝ) * ∏ i, MatrixArithmetic.logWeights q i) := by
    rw [hp]
    field_simp
  rw [he] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun H => by
    simp only [rowCount, InterpolationMatrix.row_card, Nat.cast_mul]
    rw [← hcast]
    ring)

theorem tendsto_lowIndexCount_normalized {m : ℕ} (A : ℚ)
    (q : Fin m → ℕ) (hA : 0 < A) (hq : ∀ i, 2 ≤ q i) :
    Tendsto (fun H : ℝ => lowIndexCount A q H / H ^ m) atTop
      (𝓝 ((A : ℝ) ^ m / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i))) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have ht : Tendsto (fun H : ℝ => (A : ℝ) * H) atTop atTop :=
    Tendsto.const_mul_atTop hAR tendsto_id
  have h := ((tendsto_card_realWeightedSimplex_rational (rationalLogWeights q)
    (rationalLogWeights_pos q hq)).comp ht).mul_const ((A : ℝ) ^ m)
  simp only [rationalLogWeights_cast] at h
  have he : 1 / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i) * (A : ℝ) ^ m =
      (A : ℝ) ^ m / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i) := by ring
  rw [he] at h
  have hweights : (fun i => (rationalLogWeights q i : ℝ)) = MatrixArithmetic.logWeights q := by
    funext i
    exact rationalLogWeights_cast q i
  apply h.congr'
  exact Eventually.of_forall (fun H => by
    simp only [Function.comp_apply, lowIndexCount, mul_pow]
    field_simp)

theorem tendsto_row_lowIndex_ratio {m : ℕ} (K : ℕ) (v0 θ A : ℚ)
    (q : Fin m → ℕ) (hv0 : 0 < v0) (hθ : 0 < θ) (hA : 0 < A)
    (hq : ∀ i, 2 ≤ q i) :
    Tendsto (fun H : ℝ => rowCount K v0 θ q H / (H * lowIndexCount A q H)) atTop
      (𝓝 ((K : ℝ) * (θ : ℝ) ^ m / (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m))) := by
  have hAR : (0 : ℝ) < A := by exact_mod_cast hA
  have hvR : (0 : ℝ) < v0 := by exact_mod_cast hv0
  have hθR : (0 : ℝ) < θ := by exact_mod_cast hθ
  have hP : 0 < ∏ i, MatrixArithmetic.logWeights q i :=
    Finset.prod_pos (fun i _ => MatrixArithmetic.ceil_log_weight_pos (hq i))
  have hfac : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
  have hd : (A : ℝ) ^ m / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i) ≠ 0 :=
    (div_pos (pow_pos hAR m) (mul_pos hfac hP)).ne'
  have h := (tendsto_rowCount_normalized K v0 θ q hv0 hθ hq).div
    (tendsto_lowIndexCount_normalized A q hA hq) hd
  have he :
      ((K : ℝ) * (θ : ℝ) ^ m /
        (((m + 1).factorial : ℝ) * (v0 : ℝ) * ∏ i, MatrixArithmetic.logWeights q i)) /
        ((A : ℝ) ^ m / ((m.factorial : ℝ) * ∏ i, MatrixArithmetic.logWeights q i)) =
      (K : ℝ) * (θ : ℝ) ^ m / (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m) := by
    simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  rw [he] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with H hH
  change (rowCount K v0 θ q H / H ^ (m + 1)) / (lowIndexCount A q H / H ^ m) =
    rowCount K v0 θ q H / (H * lowIndexCount A q H)
  by_cases hn : lowIndexCount A q H = 0
  · simp [hn]
  · simp only [pow_succ]
    field_simp [hH.ne', hn]

theorem tendsto_collisionRatio {m : ℕ} (K : ℕ) (v0 θ A : ℚ)
    (q : Fin m → ℕ) (hv0 : 0 < v0) (hθ : 0 < θ) (hA : 0 < A)
    (hq : ∀ i, 2 ≤ q i) (c η : ℝ) :
    Tendsto (fun H : ℝ => c * η ^ 2 * rowCount K v0 θ q H /
      (H * lowIndexCount A q H)) atTop
      (𝓝 (c * η ^ 2 * (K : ℝ) * (θ : ℝ) ^ m /
        (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m))) := by
  have ht := (tendsto_row_lowIndex_ratio K v0 θ A q hv0 hθ hA hq).const_mul (c * η ^ 2)
  have he : (c * η ^ 2) *
      ((K : ℝ) * (θ : ℝ) ^ m / (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m)) =
      c * η ^ 2 * (K : ℝ) * (θ : ℝ) ^ m /
        (((m : ℝ) + 1) * (v0 : ℝ) * (A : ℝ) ^ m) := by ring
  rw [he] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun H => by
    change (c * η ^ 2) * (rowCount K v0 θ q H / (H * lowIndexCount A q H)) = _
    ring)

end PiExponent.MatrixCounting

end OAI
