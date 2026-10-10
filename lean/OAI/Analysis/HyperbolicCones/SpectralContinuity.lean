import OAI.Analysis.HyperbolicCones.SpectralProjection

namespace OAI

/-! Finite spectral convergence, including eigenvalues equal to zero. -/

noncomputable section
open scoped Matrix.Norms.L2Operator MatrixOrder
open Matrix Filter Topology
universe u

namespace Paper256

theorem matrix_cfc_tendsto {n : ℕ} (A : Mat n ℝ) (hA : A.IsHermitian) {T : Type u} {L : Filter T}
    (f : T → ℝ → ℝ) (g : ℝ → ℝ)
    (hf : ∀ i, Tendsto (fun t => f t (hA.eigenvalues i)) L
      (𝓝 (g (hA.eigenvalues i)))) :
    Tendsto (fun t => cfc (f t) A) L (𝓝 (cfc g A)) := by
  have hcoord : Tendsto (fun t i => f t (hA.eigenvalues i)) L
      (𝓝 (fun i => g (hA.eigenvalues i))) := tendsto_pi_nhds.mpr hf
  have hdiag := (continuous_id.matrix_diagonal.tendsto
    (fun i => g (hA.eigenvalues i))).comp hcoord
  have hprod := ((tendsto_const_nhds (x := (hA.eigenvectorUnitary : Mat n ℝ))).mul hdiag).mul
    (tendsto_const_nhds (x := ((hA.eigenvectorUnitary : Mat n ℝ)ᴴ)))
  simpa only [hA.cfc_eq, Matrix.IsHermitian.cfc,
    Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose,
    Function.comp_def, RCLike.ofReal_real_eq_id, id_eq] using
    (hprod : Tendsto (fun t => (hA.eigenvectorUnitary : Mat n ℝ) *
      diagonal (fun i => f t (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Mat n ℝ)ᴴ) L
      (𝓝 ((hA.eigenvectorUnitary : Mat n ℝ) *
      diagonal (fun i => g (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Mat n ℝ)ᴴ)))

theorem inverse_sqrt_affine_scalar_tendsto (μ : ℝ) (hμ : 0 ≤ μ) :
    Tendsto (fun t : ℝ => (Real.sqrt (1 + (t - 1) * μ))⁻¹) atTop
      (𝓝 (if μ = 0 then 1 else 0)) := by
  by_cases hzero : μ = 0
  · simp [hzero]
  · have hpos : 0 < μ := lt_of_le_of_ne hμ (Ne.symm hzero)
    have haff : Tendsto (fun t : ℝ => 1 + (t - 1) * μ) atTop atTop := by
      have hm := (tendsto_id.const_mul_atTop hpos).atTop_add
        (tendsto_const_nhds (x := 1 - μ))
      convert hm using 1
      ext t
      simp only [id_eq]
      ring
    simpa [hzero, Function.comp_def] using tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp haff)

end Paper256

end

end OAI
