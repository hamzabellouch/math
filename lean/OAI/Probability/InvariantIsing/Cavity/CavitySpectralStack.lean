import OAI.Probability.InvariantIsing.Cavity.CavityComplement
import OAI.Probability.InvariantIsing.Cavity.CavityGaussianContinuity

namespace OAI

/-! The cavity column stack formed from square roots of spectral
compressions. Its columns are orthonormal when the compressions sum to
the identity, and it has the required deterministic limit. -/

noncomputable section
open Filter
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator

namespace InvariantIsing

lemma cavity_sqrt_scalar_identity {n : ℕ} (ρ : ℝ) (hρ : 0 ≤ ρ) :
    CFC.sqrt (ρ • (1 : Matrix (Fin n) (Fin n) ℝ)) = Real.sqrt ρ • 1 := by
  apply CFC.sqrt_unique
    (hb := (Matrix.PosSemidef.one.smul (Real.sqrt_nonneg ρ)).nonneg)
  rw [smul_mul_smul_comm, Matrix.one_mul, Real.mul_self_sqrt hρ]

def cavitySpectralStack {m n : ℕ} (M : Fin m → Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin (m * n)) (Fin n) ℝ := fun i j =>
  CFC.sqrt (M (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2 j

theorem cavitySpectralStack_gram {m n : ℕ}
    (M : Fin m → Matrix (Fin n) (Fin n) ℝ) (hM : ∀ a, (M a).PosSemidef) :
    (cavitySpectralStack M).transpose * cavitySpectralStack M = ∑ a, M a := by
  ext i j
  change (∑ k : Fin (m * n),
      CFC.sqrt (M (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 i *
      CFC.sqrt (M (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2 j) = _
  rw [← Equiv.sum_comp (finProdFinEquiv : Fin m × Fin n ≃ Fin (m * n))]
  simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  have hs : (CFC.sqrt (M a)).transpose = CFC.sqrt (M a) :=
    Matrix.isHermitian_iff_isSymm.mp
      (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg (M a))).isHermitian
  have he := CFC.sqrt_mul_sqrt_self (M a) (hM a).nonneg
  have he' : (CFC.sqrt (M a)).transpose * CFC.sqrt (M a) = M a := by
    rw [hs, he]
  have hentry := congrArg (fun A : Matrix (Fin n) (Fin n) ℝ => A i j) he'
  exact hentry

theorem cavitySpectralStack_tendsto {m n : ℕ}
    (M : ℕ → Fin m → Matrix (Fin n) (Fin n) ℝ) (ρ : Fin m → ℝ)
    (hρ : ∀ a, 0 ≤ ρ a) (hM : ∀ k a, (M k a).PosSemidef)
    (hlim : ∀ a, Tendsto (fun k => M k a) atTop (𝓝 (ρ a • 1))) :
    Tendsto (fun k => cavitySpectralStack (M k)) atTop
      (𝓝 (fun i j => Real.sqrt (ρ (finProdFinEquiv.symm i).1) *
        (1 : Matrix (Fin n) (Fin n) ℝ) (finProdFinEquiv.symm i).2 j)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  let a := (finProdFinEquiv.symm i).1
  let b := (finProdFinEquiv.symm i).2
  have ht := cavity_sqrt_tendsto (fun k => M k a) (ρ a • 1) (fun k => hM k a)
    (Matrix.PosSemidef.one.smul (hρ a)) (hlim a)
  have hc : Continuous (fun A : Matrix (Fin n) (Fin n) ℝ => A b j) :=
    continuous_id.matrix_elem b j
  have he := hc.tendsto (CFC.sqrt (ρ a • 1)) |>.comp ht
  simpa only [Function.comp_def, cavity_sqrt_scalar_identity (ρ a) (hρ a),
    Matrix.smul_apply, smul_eq_mul, cavitySpectralStack, a, b] using he

end InvariantIsing

end

end OAI
