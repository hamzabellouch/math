import OAI.Probability.InvariantIsing.Cavity.CavitySchurDerivative
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteRoot
import OAI.Probability.InvariantIsing.Cavity.CavityDeterminantDerivative

namespace OAI

/-! The actual finite-multiplicity logarithmic quadratic factor and its
root trace, evaluated on the limiting special/cavity blocks. -/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
open Filter

namespace InvariantIsing

private lemma cavity_labeled_shift_isUnit {m d : ℕ}
    (lam : Fin m → ℝ) (g : Fin d → Fin m) (b : ℝ) (hb : ∀ a, lam a < b) :
    IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i))).det := by
  have he : b • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i)) = Matrix.diagonal (fun i => b - lam (g i)) := by
    ext i j
    by_cases hij : i = j
    · subst j; simp
    · simp [hij]
  rw [he]
  exact isUnit_iff_ne_zero.mpr
    (Matrix.PosDef.diagonal (fun i => sub_pos.mpr (hb (g i)))).det_pos.ne'

/-- The multiplicity formula with all Schur/invertibility hypotheses
obtained from the actual repeated-spectrum geometry. -/
theorem cavity_finite_tilt_determinant {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (s : Fin m → ℕ) (hs : ∀ a, s a ≤ n)
    (hcounts : ∀ a, (Finset.univ.filter (fun i => g i = a)).card = n - s a)
    (x : ℝ) (hx : 0 < x) :
    (1 - (finiteInverse rho lam hrho hsum x •
      (1 : Matrix (Fin d) (Fin d) ℝ) - Matrix.diagonal (fun i => lam (g i)))⁻¹ *
      (B.transpose * cavityRepeatedSpectrum (n := n) lam * B -
        Matrix.diagonal (fun i => lam (g i)))).det =
      x ^ n * ∏ a, (finiteInverse rho lam hrho hsum x - lam a) ^ s a := by
  let D := cavityRepeatedSpectrum (n := n) lam
  let E := cavityLimitingStack (n := n) rho
  let A := B.transpose * D * B
  let L := B.transpose * D * E
  let C := E.transpose * D * E
  let b := finiteInverse rho lam hrho hsum x
  have hb : ∀ a, lam a < b := (finiteInverse_spec rho lam hrho hsum hx).1
  have hD : (b • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) - D).PosDef := by
    rw [show D = cavityRepeatedSpectrum (n := n) lam from rfl,
      cavityRepeatedSpectrum_shift_eq]
    exact Matrix.PosDef.diagonal (fun i => sub_pos.mpr (hb (finProdFinEquiv.symm i).1))
  have hBinj : Function.Injective B.mulVec := by
    intro u v huv
    have he := congrArg (fun w => B.transpose *ᵥ w) huv
    simpa only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] using he
  have hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det := by
    have hp := hD.conjTranspose_mul_mul_same hBinj
    have he : (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).PosDef := by
      simpa only [A, Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
        Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hB] using hp
    exact isUnit_iff_ne_zero.mpr he.det_pos.ne'
  have hblocks : Matrix.fromBlocks A L L.transpose C = cavitySpecialBlocks D B E := by
    unfold cavitySpecialBlocks
    dsimp only [A, L, C]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      show D.transpose = D from Matrix.diagonal_transpose _]
    simp only [Matrix.mul_assoc]
  have hfull : (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det = ∏ a, (b - lam a) ^ n := by
    rw [hblocks]
    exact cavity_limiting_blocks_determinant rho lam b (fun a => (hrho a).le)
      hsum B hB hBE hcomplete
  have hM : IsUnit (b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C).det := by
    rw [hfull]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr
      (fun a _ => pow_ne_zero n (ne_of_gt (sub_pos.mpr (hb a)))))
  have hcomp : ((b • (1 : Matrix (Fin d ⊕ Fin n) (Fin d ⊕ Fin n) ℝ) -
      Matrix.fromBlocks A L L.transpose C)⁻¹).toBlocks₂₂ = x • 1 := by
    rw [hblocks]
    exact cavity_finiteInverse_blocks_compression rho lam hrho hsum B hB hBE hcomplete x hx
  exact cavity_schur_tilt_det_multiplicity A L C g lam s hs hcounts b x hx.ne'
    hb hA hM hcomp hfull

theorem cavity_finite_tilt_logdet {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (s : Fin m → ℕ) (hs : ∀ a, s a ≤ n)
    (hcounts : ∀ a, (Finset.univ.filter (fun i => g i = a)).card = n - s a)
    (hsrho : ∀ a, (s a : ℝ) = (n : ℝ) * rho a) (x : ℝ) (hx : 0 < x) :
    Real.log (1 - (finiteInverse rho lam hrho hsum x •
      (1 : Matrix (Fin d) (Fin d) ℝ) - Matrix.diagonal (fun i => lam (g i)))⁻¹ *
      (B.transpose * cavityRepeatedSpectrum (n := n) lam * B -
        Matrix.diagonal (fun i => lam (g i)))).det =
      (n : ℝ) * cavitySpectralLogDet rho lam hrho hsum x := by
  rw [cavity_finite_tilt_determinant rho lam hrho hsum B hB hBE hcomplete g s hs hcounts x hx]
  exact cavity_log_multiplicity_product lam rho s n hsrho _ x hx
    (finiteInverse_spec rho lam hrho hsum hx).1

/-- Root contraction after the matrix and scalar log-determinant
calculations. The only multiplicity data are those of the finite model. -/
theorem cavity_finite_root_trace {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (s : Fin m → ℕ) (hs : ∀ a, s a ≤ n)
    (hcounts : ∀ a, (Finset.univ.filter (fun i => g i = a)).card = n - s a)
    (hsrho : ∀ a, (s a : ℝ) = (n : ℝ) * rho a) (x : ℝ) (hx : 0 < x) :
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let K := B.transpose * cavityRepeatedSpectrum (n := n) lam * B - A₀
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    let H' := (1 / finiteSecondResolvent rho lam (finiteInverse rho lam hrho hsum x)) • (H * H)
    Matrix.trace (H' * cavityBackwardQuadratic K H) =
      -(n : ℝ) * x * deriv (finiteR rho lam hrho hsum) x := by
  let A₀ := Matrix.diagonal (fun i => lam (g i))
  let K := B.transpose * cavityRepeatedSpectrum (n := n) lam * B - A₀
  let b := finiteInverse rho lam hrho hsum
  let H := fun t => (b t • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀)⁻¹
  let v := -1 / finiteSecondResolvent rho lam (b x)
  have h0 : IsUnit (b x • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀).det :=
    cavity_labeled_shift_isUnit lam g (b x) (finiteInverse_spec rho lam hrho hsum hx).1
  have hb : HasDerivAt b v x :=
    (hasStrictDerivAt_finiteInverse rho lam hrho hsum hx).hasDerivAt
  have hshift := (hb.smul_const (1 : Matrix (Fin d) (Fin d) ℝ)).sub_const A₀
  have hH := hasDerivAt_cavityMatrixInverse _ _ x hshift h0
  have hH' : HasDerivAt H ((-v) • (H x * H x)) x := by
    convert! hH using 1
    simp only [H, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      neg_smul, smul_neg]
  have hdet : IsUnit (1 - H x * K).det := by
    rw [show (1 - H x * K).det = x ^ n * ∏ a, (b x - lam a) ^ s a from
      cavity_finite_tilt_determinant rho lam hrho hsum B hB hBE hcomplete g s hs hcounts x hx]
    exact isUnit_iff_ne_zero.mpr (mul_ne_zero (pow_ne_zero n hx.ne')
      (Finset.prod_ne_zero_iff.mpr (fun a _ => pow_ne_zero _
        (ne_of_gt (sub_pos.mpr ((finiteInverse_spec rho lam hrho hsum hx).1 a))))))
  have hmat := hasDerivAt_cavityQuadraticLogDet K H ((-v) • (H x * H x)) x hH' hdet
  have hlog : (fun t => Real.log (1 - H t * K).det) =ᶠ[𝓝 x]
      (fun t => (n : ℝ) * cavitySpectralLogDet rho lam hrho hsum t) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    exact cavity_finite_tilt_logdet rho lam hrho hsum B hB hBE hcomplete
      g s hs hcounts hsrho t ht
  have he := (hmat.congr_of_eventuallyEq hlog.symm).unique
    ((hasDerivAt_cavitySpectralLogDet rho lam hrho hsum x hx).const_mul (n : ℝ))
  dsimp only [v] at he
  rw [neg_div, neg_neg] at he
  dsimp only
  linarith

end InvariantIsing

end

end OAI
