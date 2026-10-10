import OAI.Probability.InvariantIsing.Cavity.CavityProjectedInnovation

namespace OAI

/-! Differentiating the noncommuting quadratic resolvent. The resulting
compression identifies the common root covariance from the same scalar
Schur identity used at the positive levels. -/

noncomputable section
open scoped Matrix Matrix.Norms.L2Operator Topology
open Filter

namespace InvariantIsing

lemma hasDerivAt_cavityMatrixInverse {d : ℕ}
    (H : ℝ → Matrix (Fin d) (Fin d) ℝ) (H' : Matrix (Fin d) (Fin d) ℝ)
    (x : ℝ) (hH : HasDerivAt H H' x) (hdet : IsUnit (H x).det) :
    HasDerivAt (fun t => (H t)⁻¹) (-(H x)⁻¹ * H' * (H x)⁻¹) x := by
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hdet
  have hi : (↑u⁻¹ : Matrix (Fin d) (Fin d) ℝ) = (H x)⁻¹ := by
    rw [← hu, Matrix.nonsing_inv_eq_ringInverse, Ring.inverse_unit]
  have hd := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hi, hu] at hd
  have hc := hd.comp_hasDerivAt x hH
  simpa only [Function.comp_def, neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, Matrix.nonsing_inv_eq_ringInverse,
    neg_mul] using hc

private lemma cavityResolvent_identity_add {d : ℕ}
    (K H : Matrix (Fin d) (Fin d) ℝ) (hK : K.transpose = K)
    (hH : H.transpose = H) (hdet : IsUnit (1 - H * K).det) :
    1 + K * cavityResolvent K H = ((1 - H * K)⁻¹).transpose := by
  have ht : ((1 - H * K)⁻¹).transpose = (1 - K * H)⁻¹ := by
    rw [Matrix.transpose_nonsing_inv]
    simp only [Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_mul, hK, hH]
  have hdet' : IsUnit (1 - K * H).det := by rwa [Matrix.det_one_sub_mul_comm]
  rw [ht, cavityResolvent_pushThrough K H hdet]
  have he := Matrix.mul_nonsing_inv (1 - K * H) hdet'
  rw [Matrix.sub_mul, Matrix.one_mul] at he
  calc
    1 + K * (H * (1 - K * H)⁻¹) =
        ((1 - K * H)⁻¹ - K * H * (1 - K * H)⁻¹) +
          K * (H * (1 - K * H)⁻¹) := by rw [he]
    _ = (1 - K * H)⁻¹ := by simp only [Matrix.mul_assoc]; abel

/-- The root covariance identity `cav:q-root-covariance` holds without
commuting the covariance path with the quadratic coefficient. -/
theorem hasDerivAt_cavityResolvent {d : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (H' : Matrix (Fin d) (Fin d) ℝ) (x : ℝ)
    (hK : K.transpose = K) (hHx : (H x).transpose = H x)
    (hH : HasDerivAt H H' x) (hdet : IsUnit (1 - H x * K).det) :
    HasDerivAt (fun t => cavityResolvent K (H t))
      ((1 - H x * K)⁻¹ * H' * ((1 - H x * K)⁻¹).transpose) x := by
  have hD : HasDerivAt (fun t => 1 - H t * K) (-(H' * K)) x := by
    simpa only [zero_sub] using (hH.mul_const K).const_sub 1
  have hi := hasDerivAt_cavityMatrixInverse _ _ x hD hdet
  have hf := hi.mul hH
  change HasDerivAt (fun t => cavityResolvent K (H t))
    (-(1 - H x * K)⁻¹ * -(H' * K) * (1 - H x * K)⁻¹ * H x +
      (1 - H x * K)⁻¹ * H') x at hf
  convert! hf using 1
  rw [← cavityResolvent_identity_add K (H x) hK hHx hdet]
  unfold cavityResolvent
  noncomm_ring

/-- Differentiating the scalar Schur field identifies the projected
common-root covariance. The local scalar identity is supplied by the
proved finite spectral Schur evaluation. -/
theorem cavity_projected_root_covariance {d n : ℕ}
    (K : Matrix (Fin d) (Fin d) ℝ) (H : ℝ → Matrix (Fin d) (Fin d) ℝ)
    (H' : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin n) ℝ)
    (C₀ : Matrix (Fin n) (Fin n) ℝ) (R : ℝ → ℝ) (R' x : ℝ)
    (hK : K.transpose = K) (hHx : (H x).transpose = H x)
    (hH : HasDerivAt H H' x) (hdet : IsUnit (1 - H x * K).det)
    (hR : HasDerivAt R R' x)
    (hscalar : (fun t => C₀ + L.transpose * cavityResolvent K (H t) * L) =ᶠ[𝓝 x]
      (fun t => R t • (1 : Matrix (Fin n) (Fin n) ℝ))) :
    L.transpose * ((1 - H x * K)⁻¹ * H' * ((1 - H x * K)⁻¹).transpose) * L =
      R' • 1 := by
  let P : Matrix (Fin d) (Fin d) ℝ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℝ :=
    { toFun := fun M => L.transpose * M * L
      map_add' := by intro M N; rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by intro c M; simp only [Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply] }
  have hf := hasDerivAt_cavityResolvent K H H' x hK hHx hH hdet
  have hp := (P.toContinuousLinearMap.hasFDerivAt).comp_hasDerivAt x hf
  have hs := hp.const_add C₀
  have hr := hR.smul_const (1 : Matrix (Fin n) (Fin n) ℝ)
  have he := (hs.congr_of_eventuallyEq hscalar.symm).unique hr
  exact he

end InvariantIsing

end

end OAI
