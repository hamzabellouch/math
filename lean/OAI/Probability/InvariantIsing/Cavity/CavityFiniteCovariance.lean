import OAI.Probability.InvariantIsing.Cavity.CavityFiniteInnovation
import OAI.Probability.InvariantIsing.Cavity.CavityDiagonalSpectralPrecision

namespace OAI

/-! Positivity and precision of the finite-alphabet covariance used by
the cavity calculation. No dimension-dependent spectral bound is needed. -/

noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

variable {ι : Type*} [Fintype ι] {d : ℕ}

def cavityFiniteCovariance (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → ι) (x : ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  (finiteInverse rho lam hrho hsum x • 1 - Matrix.diagonal (fun i => lam (g i)))⁻¹

lemma cavityFiniteCovariance_diagonal (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → ι) {x : ℝ} (hx : 0 < x) :
    cavityFiniteCovariance rho lam hrho hsum g x =
      Matrix.diagonal (fun i => (finiteInverse rho lam hrho hsum x - lam (g i))⁻¹) := by
  unfold cavityFiniteCovariance
  have he : finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i)) =
      Matrix.diagonal (fun i => finiteInverse rho lam hrho hsum x - lam (g i)) := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  apply Matrix.inv_eq_right_inv
  rw [he, Matrix.diagonal_mul_diagonal]
  have hg (i : Fin d) : finiteInverse rho lam hrho hsum x - lam (g i) ≠ 0 :=
    (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hx).1 (g i))).ne'
  simp [hg]

lemma cavityFiniteCovariance_posDef (rho lam : ι → ℝ) (hrho : ∀ a, 0 < rho a)
    (hsum : ∑ a, rho a = 1) (g : Fin d → ι) {x : ℝ} (hx : 0 < x) :
    (cavityFiniteCovariance rho lam hrho hsum g x).PosDef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g hx]
  exact Matrix.PosDef.diagonal (fun i => inv_pos.mpr
    (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hx).1 (g i))))

lemma cavityFiniteCovariance_sub_posSemidef (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    {x y : ℝ} (hy : 0 < y) (hyx : y ≤ x) :
    (cavityFiniteCovariance rho lam hrho hsum g x -
      cavityFiniteCovariance rho lam hrho hsum g y).PosSemidef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g (hy.trans_le hyx),
    cavityFiniteCovariance_diagonal rho lam hrho hsum g hy, Matrix.diagonal_sub]
  apply Matrix.PosSemidef.diagonal
  intro i
  apply sub_nonneg.mpr
  exact inv_anti₀ (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum
    (hy.trans_le hyx)).1 (g i)))
    (sub_le_sub_right (finiteInverse_antitone_pos rho lam hrho hsum hy hyx) _)

lemma finiteInverse_strict_antitone_pos (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    finiteInverse rho lam hrho hsum x < finiteInverse rho lam hrho hsum y := by
  apply lt_of_le_of_ne (finiteInverse_antitone_pos rho lam hrho hsum hy hyx.le)
  intro he
  have h := congrArg (finiteResolvent rho lam) he
  rw [(finiteInverse_spec rho lam hrho hsum (hy.trans hyx)).2,
    (finiteInverse_spec rho lam hrho hsum hy).2] at h
  exact hyx.ne h.symm

lemma cavityFiniteCovariance_sub_posDef (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    {x y : ℝ} (hy : 0 < y) (hyx : y < x) :
    (cavityFiniteCovariance rho lam hrho hsum g x -
      cavityFiniteCovariance rho lam hrho hsum g y).PosDef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g (hy.trans hyx),
    cavityFiniteCovariance_diagonal rho lam hrho hsum g hy, Matrix.diagonal_sub]
  apply Matrix.PosDef.diagonal
  intro i
  apply sub_pos.mpr
  simpa only [one_div] using one_div_lt_one_div_of_lt
    (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum (hy.trans hyx)).1 (g i)))
    (sub_lt_sub_right (finiteInverse_strict_antitone_pos rho lam hrho hsum hy hyx) _)

lemma cavityFiniteCovariance_root_posSemidef (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    {x q₀ : ℝ} (hx : 0 < x) (hq₀ : 0 ≤ q₀) :
    (q₀ • ((1 / finiteSecondResolvent rho lam (finiteInverse rho lam hrho hsum x)) •
      (cavityFiniteCovariance rho lam hrho hsum g x *
        cavityFiniteCovariance rho lam hrho hsum g x))).PosSemidef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g hx, Matrix.diagonal_mul_diagonal]
  have hM : 0 < finiteSecondResolvent rho lam (finiteInverse rho lam hrho hsum x) :=
    finiteSecondResolvent_pos (fun a => (hrho a).le) hsum
      (finiteInverse_spec rho lam hrho hsum hx).1
  exact ((Matrix.PosSemidef.diagonal (fun i => mul_self_nonneg _)).smul
    (one_div_nonneg.mpr hM.le)).smul hq₀

theorem cavityFiniteCovariance_step_precision (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    (A : Matrix (Fin d) (Fin d) ℝ) (a : ι)
    (hK : (A - Matrix.diagonal (fun i => lam (g i))).transpose =
      A - Matrix.diagonal (fun i => lam (g i)))
    (hA : (lam a • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    {x y ζ : ℝ} (hy : 0 < y) (hyx : y ≤ x) (hζ : 0 ≤ ζ)
    (S : Matrix (Fin d) (Fin d) ℝ) (hS : S.PosSemidef)
    (hΔ : cavityFiniteCovariance rho lam hrho hsum g x -
      cavityFiniteCovariance rho lam hrho hsum g y = ζ • S) :
    (cavityFactorPrecision
      (ζ • cavityBackwardQuadratic (A - Matrix.diagonal (fun i => lam (g i)))
        (cavityFiniteCovariance rho lam hrho hsum g y)) (CFC.sqrt S)).PosDef := by
  rw [cavityFiniteCovariance_diagonal rho lam hrho hsum g hy]
  apply cavity_scaled_step_precision _ S hK hS ζ hζ
    (fun i => (finiteInverse rho lam hrho hsum x - lam (g i))⁻¹)
    (fun i => (finiteInverse rho lam hrho hsum y - lam (g i))⁻¹)
  · intro i
    exact inv_pos.mpr (sub_pos.mpr
      ((finiteInverse_spec rho lam hrho hsum (hy.trans_le hyx)).1 (g i)))
  · intro i
    exact (inv_pos.mpr (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hy).1 (g i)))).le
  · intro i
    exact inv_anti₀ (sub_pos.mpr
      ((finiteInverse_spec rho lam hrho hsum (hy.trans_le hyx)).1 (g i)))
      (sub_le_sub_right (finiteInverse_antitone_pos rho lam hrho hsum hy hyx) _)
  · right
    intro i
    exact inv_pos.mpr (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hy).1 (g i)))
  · exact cavity_resolvent_diagonal_gap A (fun i => lam (g i)) (lam a)
      (finiteInverse rho lam hrho hsum x) hA
      ((finiteInverse_spec rho lam hrho hsum (hy.trans_le hyx)).1 a)
  · simpa only [cavityFiniteCovariance_diagonal rho lam hrho hsum g (hy.trans_le hyx),
      cavityFiniteCovariance_diagonal rho lam hrho hsum g hy] using hΔ

theorem cavityFiniteCovariance_terminal_precision (rho lam : ι → ℝ)
    (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1) (g : Fin d → ι)
    (A : Matrix (Fin d) (Fin d) ℝ) (a : ι) (ha : ∀ i, lam (g i) ≤ lam a)
    (hK : (A - Matrix.diagonal (fun i => lam (g i))).transpose =
      A - Matrix.diagonal (fun i => lam (g i)))
    (hA : (lam a • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosSemidef)
    {x : ℝ} (hx : 0 < x) :
    (cavityFactorPrecision (A - Matrix.diagonal (fun i => lam (g i)))
      (CFC.sqrt (cavityFiniteCovariance rho lam hrho hsum g x))).PosDef := by
  apply cavity_resolvent_terminal_precision A _ (fun i => lam (g i)) (lam a)
    (finiteInverse rho lam hrho hsum x) hK hA ha
    ((finiteInverse_spec rho lam hrho hsum hx).1 a)
  rw [cavity_covariance_sqrt_factor _ (cavityFiniteCovariance_posDef rho lam hrho hsum g hx).posSemidef,
    cavityFiniteCovariance_diagonal rho lam hrho hsum g hx]

lemma cavity_finite_spectral_upper {m n : ℕ}
    (lam : Fin m → ℝ) (a : Fin m) (ha : ∀ i, lam i ≤ lam a)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1) :
    (lam a • (1 : Matrix (Fin d) (Fin d) ℝ) -
      B.transpose * cavityRepeatedSpectrum (n := n) lam * B).PosSemidef := by
  have hD : (lam a • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
      cavityRepeatedSpectrum (n := n) lam).PosSemidef := by
    rw [cavityRepeatedSpectrum_shift_eq]
    exact Matrix.PosSemidef.diagonal (fun i => sub_nonneg.mpr (ha _))
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hB] using
    hD.conjTranspose_mul_mul_same B

end InvariantIsing

end

end OAI
