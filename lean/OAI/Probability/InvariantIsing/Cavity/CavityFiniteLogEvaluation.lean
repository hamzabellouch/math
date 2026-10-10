import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCovariancePath
import OAI.Probability.InvariantIsing.Cavity.CavityFullLogEvaluation
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteEvaluation
import OAI.Probability.InvariantIsing.Cavity.CavityFieldResidual

namespace OAI

/-! The actual finite spectral cavity logarithmic normalizer is exactly
its variational trial value. All covariance and precision requirements
are derived from the finite spectrum and its block geometry. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem cavity_finite_log_evaluation
    {m d N n : ℕ} (hN : 0 < N)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (counts : Fin m → ℕ) (hcounts_le : ∀ a, counts a ≤ N)
    (hcounts : ∀ a, (Finset.univ.filter (fun i => g i = a)).card = N - counts a)
    (hcounts_rho : ∀ a, (counts a : ℝ) = (N : ℝ) * rho a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (U : Rotation N) :
    let hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
    let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (chainExponent cut)
        (cavityGaussianMarks S) : Measure (NoiseTree (EuclideanSpace ℝ (Fin d)) n))
    Integrable (cavityRootedLogNormalizer n K (H n) L (c • 1) (uniformSpinPrior N)) P ∧
      (N : ℝ)⁻¹ * (∫ ω, cavityRootedLogNormalizer n K (H n) L (c • 1)
        (uniformSpinPrior N) ω ∂P) =
        fieldValue h 0 + fieldPairing p h / 2 + spectralFunctional (finiteR rho lam hrho hsum) p := by
  intro hq0 h H S S₀ K L c P
  let x := cavityFiniteDeficitPath p q
  have hx (i : ℕ) : 0 < x i :=
    cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop i
  have hxm : Antitone x := cavityFiniteDeficitPath_antitone p q hq.monotone
  have hK : K.transpose = K := by
    dsimp only [K, cavityRepeatedSpectrum]
    simp only [Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, Matrix.mul_assoc]
  have hH (i : ℕ) : (H i).transpose = H i :=
    cavityFiniteCovariancePath_symmetric rho lam hrho hsum g p q i
  have hS (i : ℕ) : (S i).PosSemidef :=
    cavityFiniteNoiseCovariance_posSemidef rho lam hrho hsum g p cut hcut hfirst hlast
      q hq hp htop i
  have hS₀ : S₀.PosSemidef :=
    cavityFiniteCovariance_root_posSemidef rho lam hrho hsum g (hx 0) (hq0 0)
  have hdet (i : ℕ) : IsUnit (1 - H i * K).det :=
    cavity_finite_tilt_isUnit rho lam hrho hsum B hB g (x i) (hx i)
  have hΔ (i : ℕ) : H i - H (i + 1) = chainExponent cut i • S i :=
    cavityFiniteNoiseCovariance_delta rho lam hrho hsum g p cut hcut hfirst q i
  have hA := cavity_finite_spectral_upper lam a ha B hB
  have hQ (i : ℕ) : (cavityFactorPrecision
      (chainExponent cut i • cavityBackwardQuadratic K (H (i + 1))) (CFC.sqrt (S i))).PosDef :=
    cavityFiniteCovariance_step_precision rho lam hrho hsum g _ a hK hA
      (hx (i + 1)) (hxm (Nat.le_succ i)) (finite_chainExponent_pos cut hcut hfirst i).le
      (S i) (hS i) (hΔ i)
  have hR : (H n).PosSemidef :=
    (cavityFiniteCovariancePath_posDef rho lam hrho hsum g p cut hfirst hlast q hq hp htop n).posSemidef
  have hQR : (cavityFactorPrecision K (CFC.sqrt (H n))).PosDef :=
    cavityFiniteCovariance_terminal_precision rho lam hrho hsum g _ a (fun i => ha (g i)) hK hA (hx n)
  have hcov (i : ℕ) (hi : i < n) :
      L.transpose * ((1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) * L =
        (fieldStepVariance h i : ℝ) • 1 := by
    let k : Fin n := ⟨i, hi⟩
    have he := cavity_finite_projected_innovation rho lam hrho hsum B hB hBE hcomplete g
      (x i) (x (i + 1)) (chainExponent cut i) (hx i) (hx (i + 1))
      (finite_chainExponent_pos cut hcut hfirst i).ne' (S i) (hΔ i)
    change L.transpose * ((1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) * L = _ at he
    rw [he]
    have hv := cavityFieldStep_variance rho lam hrho hsum p cut hcut hfirst hlast
      q hq hq0 hp htop k
    change (fieldStepVariance h i : ℝ) = _ at hv
    rw [hv]
    simp only [x, cavityFiniteDeficitPath, show i = (k : ℕ) from rfl,
      cavityFiniteLevel_castSucc, cavityFiniteLevel_succ]
    rw [chainExponent_apply cut k.isLt]
    rfl
  have hnonneg : 0 ≤ finiteR rho lam hrho hsum (x n) - c := by
    apply sub_nonneg.mpr
    have hc : c = ∑ a, rho a * lam a := by simp [c, finiteR]
    rw [hc]
    exact mean_le_finiteR rho lam hrho hsum (hx n)
  let v : ℝ≥0 := (finiteR rho lam hrho hsum (x n) - c).toNNReal
  have hres : L.transpose * cavityResolvent K (H n) * L = (v : ℝ) • 1 := by
    rw [show (v : ℝ) = finiteR rho lam hrho hsum (x n) - c from Real.coe_toNNReal _ hnonneg]
    exact cavity_finite_projected_residual rho lam hrho hsum B hB hBE hcomplete g (x n) (hx n)
  have hroot : L.transpose * ((1 - H 0 * K)⁻¹ * S₀ * ((1 - H 0 * K)⁻¹).transpose) * L =
      h.height 0 • 1 := by
    have hv := cavityFieldStep_root_variance rho lam hrho hsum p cut hcut hfirst hlast
      q hq.monotone hq0 hp htop
    change h.height 0 = _ at hv
    have hroot := cavity_finite_projected_scaled_root rho lam hrho hsum B hB hBE hcomplete
      g (x 0) (q 0) (hx 0)
    change L.transpose * ((1 - H 0 * K)⁻¹ * S₀ * ((1 - H 0 * K)⁻¹).transpose) * L = _ at hroot
    rw [hroot, hv]
    simp only [x, cavityFiniteDeficitPath, cavityFiniteLevel_zero]
  have he := cavity_full_log_evaluation hN h K H S S₀ hS₀ L c hK hH hS
    (fun i => field_chainExponent_pos h i) hdet hΔ hQ hR hQR v hcov hres hroot
  have heq : (∫ ω, cavityRootedLogNormalizer n K (H n) L (c • 1)
      (uniformSpinPrior N) ω ∂P) =
      Matrix.trace (S₀ * cavityBackwardQuadratic K (H 0)) / 2 -
        (∑ i ∈ Finset.range n, cavityDeterminantStep K H (chainExponent cut) i) -
        Real.log (1 - H n * K).det / 2 + (N : ℝ) * (c + v) / 2 +
        ∫ z, cascadeRecursion h.depth (chainExponent h.cut)
          (fun i => vectorGaussianLaw N (fieldStepVariance h i))
          (fun _ p => p.1 + p.2) (fun y => ∑ i, Real.log (Real.cosh (y i))) z
          ∂(vectorGaussianLaw N (NNReal.mk (h.height 0) (h.nonneg 0)) : Measure _) := he.2
  refine ⟨he.1, ?_⟩
  rw [heq]
  let Hf := fun j : Fin (n + 1) =>
    (finiteInverse rho lam hrho hsum (deficit p (q j)) • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i)))⁻¹
  have hHf (j : Fin (n + 1)) : H j = Hf j := by
    have hl : cavityFiniteLevel n (j : ℕ) = j := by
      apply Fin.ext
      exact min_eq_left (Nat.le_of_lt_succ j.isLt)
    dsimp only [H, cavityFiniteCovariancePath, cavityFiniteCovariance,
      cavityFiniteDeficitPath, Hf]
    rw [hl]
  have hsteps : (∑ i ∈ Finset.range n, cavityDeterminantStep K H (chainExponent cut) i) =
      ∑ i : Fin n, Real.log ((1 - Hf i.castSucc * K).det / (1 - Hf i.succ * K).det) /
        (2 * cut i.castSucc.succ) := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    have hi : H (i : ℕ) = Hf i.castSucc := hHf i.castSucc
    have hj : H ((i : ℕ) + 1) = Hf i.succ := hHf i.succ
    rw [cavityDeterminantStep, chainExponent_apply cut i.isLt, hi, hj]
    rfl
  have hquad := cavity_finite_quadratic_mean rho lam hrho hsum B hB hBE hcomplete
    g counts hcounts_le hcounts hcounts_rho p cut hcut hfirst hlast q hq hp htop
  change cavityFiniteQuadraticMean K Hf S₀ cut = _ at hquad
  unfold cavityFiniteQuadraticMean at hquad
  have hzero : H 0 = Hf 0 := hHf 0
  have hlastH : H n = Hf (Fin.last n) := hHf (Fin.last n)
  rw [hsteps, hzero, hlastH, hquad]
  have hscalar := (field_vector_log_mean N hN h U).2
  rw [(field_vector_log_root_integral N hN h (NNReal.mk (h.height 0) (h.nonneg 0))).2] at hscalar
  have htail := cavityField_residual rho lam hrho hsum p htop.le
    ((finite_overlap_ae_bounds p cut hfirst hlast q hq.monotone hp).mono (fun _ h => h.2))
  change cavityFieldDiagonal rho lam hrho hsum p - h.height (Fin.last h.depth) =
    finiteR rho lam hrho hsum (deficit p (q (Fin.last n))) - c at htail
  have hv : (v : ℝ) = cavityFieldDiagonal rho lam hrho hsum p - h.height (Fin.last h.depth) := by
    rw [show (v : ℝ) = finiteR rho lam hrho hsum (x n) - c from Real.coe_toNNReal _ hnonneg]
    simpa only [x, cavityFiniteDeficitPath, cavityFiniteLevel_last] using htail.symm
  rw [mul_add, mul_add, hscalar, hv]
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hnorm (y : ℝ) : (N : ℝ)⁻¹ * (-((N : ℝ) / 2) * y) = -y / 2 := by
    field_simp
  have hconst (y : ℝ) : (N : ℝ)⁻¹ * ((N : ℝ) * y / 2) = y / 2 := by
    field_simp
  rw [hnorm, hconst]
  have hvalue := cavity_finite_value_identity rho lam hrho hsum p cut hcut hfirst hlast
    q hq.monotone hq0 hp
  change fieldValue h 0 + _ = _ at hvalue
  convert hvalue using 1
  ring

end InvariantIsing

end

end OAI
