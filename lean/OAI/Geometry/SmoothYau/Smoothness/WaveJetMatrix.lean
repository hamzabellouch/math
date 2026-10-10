import Mathlib

namespace OAI

noncomputable section
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open MvPolynomial
open Set Filter
open scoped ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter Function MvPolynomial
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open scoped Topology
open Set Filter Manifold Bundle MeasureTheory
open scoped Topology ContDiff ENNReal
open Matrix
open scoped Topology Matrix.Norms.Elementwise
open Set Filter Manifold Bundle
open scoped Topology ContDiff
open Set Filter MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Topology
open Set Filter
open scoped Topology Matrix ContDiff Matrix.Norms.Elementwise
namespace YauCounterexamples

def waveJetMatrix (a δ b00 b01 b10 b11 : ℝ) :
    Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) ℝ :=
  Matrix.fromBlocks !![1, 1; a, a + δ] 0 0 !![b00, b10; b01, b11]

theorem waveJetMatrix_det (a δ b00 b01 b10 b11 : ℝ) :
    Matrix.det (waveJetMatrix a δ b00 b01 b10 b11) = δ * (b00 * b11 - b10 * b01) := by
  rw [waveJetMatrix, Matrix.det_fromBlocks_zero₂₁]
  simp only [Matrix.det_fin_two, Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

theorem contDiff_matrixDet {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ContDiff ℝ ∞ (Matrix.det : Matrix ι ι ℝ → ℝ) := by
  change ContDiff ℝ ∞ (fun A : Matrix ι ι ℝ => Matrix.det A)
  simp only [Matrix.det_apply]
  fun_prop

theorem continuous_waveJetMatrix (a b00 b01 b10 b11 : ℝ) :
    Continuous (fun δ => waveJetMatrix a δ b00 b01 b10 b11) := by
  unfold waveJetMatrix
  fun_prop

theorem determinant_linear_lower_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : ℝ → Matrix ι ι ℝ) (hA : ContinuousAt A 0) (D : ℝ) (hD : D ≠ 0)
    (hdet : ∀ δ, Matrix.det (A δ) = δ * D) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      ∀ R : Matrix ι ι ℝ, ‖R‖ ≤ δ ^ 2 →
        |D| / 2 * δ ≤ |Matrix.det (A δ + R)| := by
  obtain ⟨K, s, hs, hKs⟩ :=
    ((contDiff_matrixDet (ι := ι)).of_le (show (1 : ℕ∞ω) ≤ (∞ : ℕ∞ω) from by simp)).contDiffAt.exists_lipschitzOnWith
      (x := A 0)
  obtain ⟨r, hr, hrs⟩ := Metric.mem_nhds_iff.mp hs
  have hpre : ∀ᶠ δ in 𝓝 (0 : ℝ), dist (A δ) (A 0) < r / 2 :=
    hA (Metric.ball_mem_nhds (A 0) (by linarith))
  obtain ⟨t, ht, htA⟩ := Metric.eventually_nhds_iff.mp hpre
  refine ⟨min t (min 1 (min (r / 2) (|D| / (2 * ((K : ℝ) + 1))))), ?_, ?_⟩
  · exact lt_min ht (lt_min zero_lt_one (lt_min (by linarith)
      (div_pos (abs_pos.mpr hD) (by positivity))))
  intro δ hδ hδε R hR
  have hδt : δ < t := hδε.trans_le (min_le_left _ _)
  have hδ1 : δ < 1 := hδε.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδr : δ < r / 2 := hδε.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hδD : δ < |D| / (2 * ((K : ℝ) + 1)) := hδε.trans_le
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  have hAdist : dist (A δ) (A 0) < r / 2 := htA (by simpa [Real.dist_eq, abs_of_pos hδ] using hδt)
  have hRr : ‖R‖ < r / 2 := lt_of_le_of_lt hR (by nlinarith)
  have hAs : A δ ∈ s := hrs (by change dist (A δ) (A 0) < r; linarith)
  have hARs : A δ + R ∈ s := hrs (by
    change dist (A δ + R) (A 0) < r
    calc
      _ ≤ dist (A δ + R) (A δ) + dist (A δ) (A 0) := dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add (by simpa using hRr) hAdist
      _ = r := by ring)
  have hdiff := hKs.dist_le_mul (x := A δ + R) hARs (y := A δ) hAs
  rw [Real.dist_eq, hdet, dist_eq_norm, add_sub_cancel_left] at hdiff
  have hDbound : 2 * ((K : ℝ) + 1) * δ < |D| := by
    have h := (lt_div_iff₀ (by positivity)).mp hδD
    nlinarith
  have hKδ : (K : ℝ) * δ ^ 2 ≤ |D| / 2 * δ := by
    have hK : 0 ≤ (K : ℝ) := K.coe_nonneg
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hR K.coe_nonneg
  have htriangle : |δ * D| ≤ |Matrix.det (A δ + R) - δ * D| + |Matrix.det (A δ + R)| := by
    simpa only [sub_add_cancel, abs_sub_comm] using
      abs_add_le (δ * D - Matrix.det (A δ + R)) (Matrix.det (A δ + R))
  rw [abs_mul, abs_of_pos hδ] at htriangle
  nlinarith

theorem determinant_uniform_error_bound {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M C d : ℝ) (hC : 0 ≤ C) (hd : 0 < d) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ δ : ℝ, 0 < δ → δ < ε →
      ∀ A R : Matrix ι ι ℝ, ‖A‖ ≤ M → d * δ ≤ |A.det| →
        ‖R‖ ≤ C * δ ^ 2 → d / 2 * δ ≤ |(A + R).det| := by
  obtain ⟨K, hK⟩ := (contDiff_matrixDet (ι := ι)).contDiffOn.exists_lipschitzOnWith
    (by simp) (convex_closedBall (0 : Matrix ι ι ℝ) (M + 1))
    (isCompact_closedBall (0 : Matrix ι ι ℝ) (M + 1))
  refine ⟨min 1 (min (1 / (C + 1)) (d / (2 * ((K : ℝ) + 1) * (C + 1)))), ?_, ?_⟩
  · exact lt_min zero_lt_one (lt_min (by positivity) (by positivity))
  intro δ hδ hδε A R hA hdet hR
  have hδ1 : δ < 1 := hδε.trans_le (min_le_left _ _)
  have hδC : δ < 1 / (C + 1) := hδε.trans_le
    ((min_le_right _ _).trans (min_le_left _ _))
  have hδd : δ < d / (2 * ((K : ℝ) + 1) * (C + 1)) := hδε.trans_le
    ((min_le_right _ _).trans (min_le_right _ _))
  have hCδ : C * δ < 1 := by
    have h := (lt_div_iff₀ (by positivity : 0 < C + 1)).mp hδC
    nlinarith
  have hR1 : ‖R‖ < 1 := by
    have hsq : δ ^ 2 ≤ δ := by nlinarith
    have := mul_le_mul_of_nonneg_left hsq hC
    linarith
  have hAs : A ∈ Metric.closedBall 0 (M + 1) := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using (by linarith : ‖A‖ ≤ M + 1)
  have hARs : A + R ∈ Metric.closedBall 0 (M + 1) := by
    simp only [Metric.mem_closedBall, dist_zero_right]
    exact (norm_add_le A R).trans (by linarith)
  have hdiff := hK.dist_le_mul (x := A + R) hARs (y := A) hAs
  rw [Real.dist_eq, dist_eq_norm, add_sub_cancel_left] at hdiff
  have hKδ : (K : ℝ) * C * δ ^ 2 ≤ d / 2 * δ := by
    have h := (lt_div_iff₀ (by positivity : 0 < 2 * ((K : ℝ) + 1) * (C + 1))).mp hδd
    have hkk : (K : ℝ) * C ≤ ((K : ℝ) + 1) * (C + 1) := by
      nlinarith [K.coe_nonneg]
    have hmm := mul_le_mul_of_nonneg_right hkk hδ.le
    have hp := mul_le_mul_of_nonneg_right hmm hδ.le
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hR K.coe_nonneg
  have htriangle : |A.det| ≤ |(A + R).det - A.det| + |(A + R).det| := by
    simpa only [sub_add_cancel, abs_sub_comm] using
      abs_add_le (A.det - (A + R).det) (A + R).det
  nlinarith

end YauCounterexamples

end

end OAI
