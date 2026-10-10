import OAI.Probability.InvariantIsing.Cavity.CavityResolventDerivative
import OAI.Probability.InvariantIsing.Cavity.CavitySchurFiniteR

namespace OAI

/-! The projected root covariance for the actual finite spectral cavity
blocks. All determinant conditions follow from the positive spectral gap. -/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator BigOperators Topology
open Filter

namespace InvariantIsing

private lemma cavity_finite_base_shift_isUnit {m d : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    IsUnit (finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i))).det := by
  have he : finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      Matrix.diagonal (fun i => lam (g i)) =
      Matrix.diagonal (fun i => finiteInverse rho lam hrho hsum x - lam (g i)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  rw [he]
  exact isUnit_iff_ne_zero.mpr
    (Matrix.PosDef.diagonal (fun i => sub_pos.mpr
      ((finiteInverse_spec rho lam hrho hsum hx).1 (g i)))).det_pos.ne'

private lemma cavity_finite_compressed_shift_isUnit {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (x : ℝ) (hx : 0 < x) :
    IsUnit (finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      B.transpose * cavityRepeatedSpectrum (n := n) lam * B).det := by
  have hBinj : Function.Injective B.mulVec := by
    intro u v huv
    have he := congrArg (fun w => B.transpose *ᵥ w) huv
    simpa only [Matrix.mulVec_mulVec, hB, Matrix.one_mulVec] using he
  have hp : (finiteInverse rho lam hrho hsum x •
      (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) -
        cavityRepeatedSpectrum (n := n) lam).PosDef := by
    rw [cavityRepeatedSpectrum_shift_eq]
    exact Matrix.PosDef.diagonal (fun i => sub_pos.mpr
      ((finiteInverse_spec rho lam hrho hsum hx).1 (finProdFinEquiv.symm i).1))
  have hc := hp.conjTranspose_mul_mul_same hBinj
  have he : (finiteInverse rho lam hrho hsum x • (1 : Matrix (Fin d) (Fin d) ℝ) -
      B.transpose * cavityRepeatedSpectrum (n := n) lam * B).PosDef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hB] using hc
  exact isUnit_iff_ne_zero.mpr he.det_pos.ne'

/-- The finite cavity tilt is invertible at every positive deficit. -/
lemma cavity_finite_tilt_isUnit {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    let A := B.transpose * cavityRepeatedSpectrum (n := n) lam * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    IsUnit (1 - H * (A - A₀)).det := by
  dsimp only
  let A := B.transpose * cavityRepeatedSpectrum (n := n) lam * B
  let A₀ := Matrix.diagonal (fun i => lam (g i))
  let b := finiteInverse rho lam hrho hsum x
  have h₀ : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀).det :=
    cavity_finite_base_shift_isUnit rho lam hrho hsum g x hx
  have hA : IsUnit (b • (1 : Matrix (Fin d) (Fin d) ℝ) - A).det :=
    cavity_finite_compressed_shift_isUnit rho lam hrho hsum B hB x hx
  have he : 1 - (b • 1 - A₀)⁻¹ * (A - A₀) =
      (b • 1 - A₀)⁻¹ * (b • 1 - A) := by
    calc
      _ = (b • 1 - A₀)⁻¹ * (b • 1 - A₀) - (b • 1 - A₀)⁻¹ * (A - A₀) := by
        rw [Matrix.nonsing_inv_mul _ h₀]
      _ = _ := by noncomm_ring
  change IsUnit (1 - (b • 1 - A₀)⁻¹ * (A - A₀)).det
  rw [he, Matrix.det_mul]
  exact (Matrix.isUnit_nonsing_inv_det_iff.mpr h₀).mul hA

/-- The projected resolvent of the finite cavity tilt has the prescribed
finite-law scalar field value. -/
lemma cavity_finite_projected_resolvent {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    let D := cavityRepeatedSpectrum (n := n) lam
    let E := cavityLimitingStack (n := n) rho
    let A := B.transpose * D * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * D * E
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    E.transpose * D * E + L.transpose * cavityResolvent (A - A₀) H * L =
      finiteR rho lam hrho hsum x • 1 := by
  dsimp only
  rw [cavityResolvent_spectral_transform _ _ _
    (cavity_finite_base_shift_isUnit rho lam hrho hsum g x hx)
    (cavity_finite_compressed_shift_isUnit rho lam hrho hsum B hB x hx)]
  exact cavity_limiting_field_eq_finiteR rho lam hrho hsum B hB hBE hcomplete x hx

/-- The source root derivative evaluated on the actual repeated-spectrum
special/cavity blocks. The base multiplicity map is arbitrary, so this
also applies after deleting the cavity eigenvectors from each group. -/
theorem cavity_finite_projected_root_covariance {m d n : ℕ}
    (rho lam : Fin m → ℝ) (hrho : ∀ a, 0 < rho a) (hsum : ∑ a, rho a = 1)
    (B : Matrix (Fin (m * n)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (hBE : B.transpose * cavityLimitingStack (n := n) rho = 0)
    (hcomplete : B * B.transpose + cavityLimitingStack (n := n) rho *
      (cavityLimitingStack (n := n) rho).transpose = 1)
    (g : Fin d → Fin m) (x : ℝ) (hx : 0 < x) :
    let A := B.transpose * cavityRepeatedSpectrum (n := n) lam * B
    let A₀ := Matrix.diagonal (fun i => lam (g i))
    let L := B.transpose * cavityRepeatedSpectrum (n := n) lam *
      cavityLimitingStack (n := n) rho
    let K := A - A₀
    let H := (finiteInverse rho lam hrho hsum x • 1 - A₀)⁻¹
    let H' := (1 / finiteSecondResolvent rho lam (finiteInverse rho lam hrho hsum x)) • (H * H)
    L.transpose * ((1 - H * K)⁻¹ * H' * ((1 - H * K)⁻¹).transpose) * L =
      deriv (finiteR rho lam hrho hsum) x • 1 := by
  let D := cavityRepeatedSpectrum (n := n) lam
  let E := cavityLimitingStack (n := n) rho
  let A := B.transpose * D * B
  let A₀ := Matrix.diagonal (fun i => lam (g i))
  let L := B.transpose * D * E
  let C₀ := E.transpose * D * E
  let K := A - A₀
  let b := finiteInverse rho lam hrho hsum
  let H := fun t => (b t • (1 : Matrix (Fin d) (Fin d) ℝ) - A₀)⁻¹
  let v := -1 / finiteSecondResolvent rho lam (b x)
  have h0 (t : ℝ) (ht : 0 < t) : IsUnit (b t • 1 - A₀).det :=
    cavity_finite_base_shift_isUnit rho lam hrho hsum g t ht
  have hA (t : ℝ) (ht : 0 < t) : IsUnit (b t • 1 - A).det :=
    cavity_finite_compressed_shift_isUnit rho lam hrho hsum B hB t ht
  have hAs : A.transpose = A := by
    dsimp only [A, D, cavityRepeatedSpectrum]
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose]
    simp only [Matrix.mul_assoc]
  have hKs : K.transpose = K := by
    simp only [K, A₀, Matrix.transpose_sub, hAs, Matrix.diagonal_transpose]
  have hHs : (H x).transpose = H x := by
    simp only [H, A₀, Matrix.transpose_nonsing_inv, Matrix.transpose_sub,
      Matrix.transpose_smul, Matrix.transpose_one, Matrix.diagonal_transpose]
  have hdet : IsUnit (1 - H x * K).det := by
    have he : 1 - H x * K = H x * (b x • 1 - A) := by
      have hinv := Matrix.nonsing_inv_mul (b x • 1 - A₀) (h0 x hx)
      change H x * (b x • 1 - A₀) = 1 at hinv
      calc
        1 - H x * K = H x * (b x • 1 - A₀) - H x * K := by rw [hinv]
        _ = H x * (b x • 1 - A) := by dsimp only [K]; noncomm_ring
    rw [he, Matrix.det_mul]
    exact (Matrix.isUnit_nonsing_inv_det_iff.mpr (h0 x hx)).mul (hA x hx)
  have hb : HasDerivAt b v x :=
    (hasStrictDerivAt_finiteInverse rho lam hrho hsum hx).hasDerivAt
  have hshift := (hb.smul_const (1 : Matrix (Fin d) (Fin d) ℝ)).sub_const A₀
  have hH := hasDerivAt_cavityMatrixInverse _ _ x hshift (h0 x hx)
  have hH' : HasDerivAt H ((-v) • (H x * H x)) x := by
    convert! hH using 1
    simp only [H, Matrix.neg_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      neg_smul, smul_neg]
  have hscalar : (fun t => C₀ + L.transpose * cavityResolvent K (H t) * L) =ᶠ[𝓝 x]
      (fun t => finiteR rho lam hrho hsum t • (1 : Matrix (Fin n) (Fin n) ℝ)) := by
    filter_upwards [Ioi_mem_nhds hx] with t ht
    rw [show cavityResolvent K (H t) = (b t • 1 - A)⁻¹ from
      cavityResolvent_spectral_transform A A₀ (b t) (h0 t ht) (hA t ht)]
    exact cavity_limiting_field_eq_finiteR rho lam hrho hsum B hB hBE hcomplete t ht
  have hr := (hasStrictDerivAt_finiteR rho lam hrho hsum hx).hasDerivAt
  have he := cavity_projected_root_covariance K H ((-v) • (H x * H x)) L C₀
    (finiteR rho lam hrho hsum) _ x hKs hHs hH' hdet hr hscalar
  rw [hr.deriv]
  simpa only [v, neg_div, neg_neg] using he

end InvariantIsing

end

end OAI
