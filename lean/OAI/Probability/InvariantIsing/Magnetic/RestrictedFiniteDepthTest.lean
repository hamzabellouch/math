import OAI.Probability.InvariantIsing.Cavity.CavityFiniteSpinTest
import OAI.Probability.InvariantIsing.Magnetic.RestrictedDepthTestEvaluation

namespace OAI

/-! The finite spectral quadratic cavity has the original common-overlap law. -/

noncomputable section
open MeasureTheory ProbabilityTheory Set IsingPerceptron
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators NNReal

namespace InvariantIsing

theorem restricted_cavity_finite_depth_test (hpub : PanchenkoTalagrandRestrictedFieldPairInput)
    {m d N n : ℕ} (hd : 0 < d) (hN : 0 < N) (T : Finset (Spin N)) (hT : T.Nonempty)
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := N) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := N) rho *
      (cavityLimitingStack (n := N) rho).transpose = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, lam b ≤ lam a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1) (Φ : ℝ → ℝ)
    {C : ℝ} (hΦ : ∀ x, |Φ x| ≤ C) :
    let hq0 := fun i => (finite_overlap_value_mem_unit p cut hcut q hp i).1
    let h := cavityFieldStep rho lam hrho hsum p cut hcut hfirst hlast q hq.monotone hq0
    let H := cavityFiniteCovariancePath rho lam hrho hsum g p q
    let S := cavityFiniteNoiseCovariance rho lam hrho hsum g p cut q
    let S₀ := cavityFiniteRootCovariance rho lam hrho hsum g p q
    let K := B.transpose * cavityRepeatedSpectrum (n := N) lam * B -
      Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := N) lam * cavityLimitingStack (n := N) rho
    let c := finiteR rho lam hrho hsum 0
    (∫ σ, cavityRootedDepthTest (fun i => Φ (q (fieldDepthLevel h i))) σ
      ∂((probabilityReplicaKernel
        (cavityRootedFullGibbs n K (H n) L (c • 1) (restrictedSpinPrior T hT))
        (cavityRootedFullGibbs n K (H n) L (c • 1) (restrictedSpinPrior T hT)).measurable)
          ∘ₘ (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
            (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (chainExponent cut)
              (cavityGaussianMarks S) : Measure _))) =
      ∫ t, Φ (p t) ∂pathMeasure := by
  intro hq0 h H S S₀ K L c
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
  have hAtom (i : ℕ) (hi : i < n) :
      NullSingletonClass (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) (S i)) :=
    cavityFiniteNoiseCovariance_atomless rho lam hrho hsum g p cut hcut hfirst hlast
      q hq hp htop hd i hi
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
  have he := restricted_cavity_full_depth_test_evaluation hpub hN T hT h K H S S₀ hS₀ L c hK hH hS
    (fun i => field_chainExponent_pos h i) hdet hΔ hQ hR hQR hAtom v hcov hres
    (fun i => Φ (q (fieldDepthLevel h i))) (fun i => hΦ _)
  apply he.trans
  apply integral_congr_ae
  filter_upwards [ae_finite_overlap_cell cut hfirst hlast] with t ht
  obtain ⟨i, hi⟩ := ht
  have hindex : fieldLevelIndex h t = i := fieldLevelIndex_on_cell h i hi
  rw [hindex]
  have hlev : fieldDepthLevel h i.val = i := by
    apply Fin.ext
    exact min_eq_left (Nat.le_of_lt_succ i.isLt)
  rw [hlev, hp i t hi]

end InvariantIsing

end

end OAI
