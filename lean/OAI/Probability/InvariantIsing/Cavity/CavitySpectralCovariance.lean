import OAI.Probability.InvariantIsing.Cavity.CavitySpectralTransform
import OAI.Probability.InvariantIsing.Cavity.CavityCovariancePartitionBound
import OAI.Probability.InvariantIsing.Cavity.CavityQuadraticCovariance

namespace OAI

/-! A bound on the covariance in the actual quadratic Gibbs marginal.
The innovation covariances are identified from their defining increments;
their sum is controlled by the overlap partition, not by its number of cells. -/

noncomputable section
open scoped BigOperators Matrix Matrix.Norms.L2Operator

namespace InvariantIsing

theorem cavity_spectral_total_covariance_bound {ι : Type*} [Fintype ι] {d n : ℕ}
    (ρ eig : ι → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (A A₀ : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (hA₀ : A₀.IsHermitian)
    (a : ι) (heig : ∀ i, hA.eigenvalues i ≤ eig a)
    (heig₀ : ∀ i, hA₀.eigenvalues i ≤ eig a)
    (q x b : ℕ → ℝ) (S : ℕ → Matrix (Fin d) (Fin d) ℝ)
    (hq : Monotone q) (hq0 : 0 ≤ q 0) (hx : ∀ i ≤ n, 0 < x i)
    (hb : ∀ i < n, 0 < b i)
    (hgap : ∀ i < n, x i - x (i + 1) = b i * (q (i + 1) - q i))
    (hlast : x n = 1 - q n)
    (hΔ : ∀ i < n,
      cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i) -
        cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x (i + 1)) = b i • S i) :
    let K := A - A₀
    let H := fun i => cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i)
    let S₀ := q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ (x 0)
    ‖((1 - H 0 * K)⁻¹ * S₀ * ((1 - H 0 * K)⁻¹).transpose) +
      ((∑ i : Fin n, (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose) +
        cavityResolvent K (H n))‖ ≤ (ρ a)⁻¹ := by
  intro K H S₀
  let T := cavitySpectralMatrixPath ρ eig hρ hsum A hA
  have hK : K.transpose = K := by
    dsimp only [K]
    rw [Matrix.transpose_sub, Matrix.isHermitian_iff_isSymm.mp hA,
      Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hH (i : ℕ) (hi : i ≤ n) : (H i).transpose = H i := by
    dsimp only [H]
    rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ (hx i hi),
      Matrix.transpose_nonsing_inv, Matrix.transpose_sub, Matrix.transpose_smul,
      Matrix.transpose_one, Matrix.isHermitian_iff_isSymm.mp hA₀]
  have hdet (i : ℕ) (hi : i ≤ n) : IsUnit (1 - H i * K).det :=
    cavity_spectral_tilt_isUnit ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀ (hx i hi)
  have htransform (i : ℕ) (hi : i ≤ n) : cavityResolvent K (H i) = T (x i) :=
    cavity_spectral_transform ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀ (hx i hi)
  have hroot : (1 - H 0 * K)⁻¹ * S₀ * ((1 - H 0 * K)⁻¹).transpose =
      q 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A hA (x 0) := by
    dsimp only [S₀]
    rw [Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    exact cavity_spectral_root_transform ρ eig hρ hsum A A₀ hA hA₀ a heig heig₀
      (hx 0 (Nat.zero_le n))
  have hstep (i : Fin n) :
      (1 - H i * K)⁻¹ * S i * ((1 - H (i + 1) * K)⁻¹).transpose =
        (b i)⁻¹ • (T (x i) - T (x (i + 1))) := by
    have he := cavity_innovation_covariance_mul K (H i) (H (i + 1)) (S i) (b i)
      hK (hH (i + 1) (by omega)) (hdet i (by omega)) (hdet (i + 1) (by omega))
      (hΔ i i.isLt)
    rw [htransform i (by omega), htransform (i + 1) (by omega)] at he
    rw [← he, smul_smul, inv_mul_cancel₀ (hb i i.isLt).ne', one_smul]
  rw [hroot, htransform n le_rfl]
  simp_rw [hstep]
  rw [← add_assoc]
  exact cavity_spectral_covariance_partition_bound ρ eig hρ hsum A hA a heig
    (fun i : Fin (n + 1) => q i) (fun i : Fin (n + 1) => x i)
    (fun i : Fin n => b i) (fun _ _ hij => hq hij) hq0
    (fun i => (hx i (by omega)).le) (hx 0 (Nat.zero_le n))
    (fun i => hb i i.isLt) (fun i => hgap i i.isLt) hlast

end InvariantIsing

end

end OAI
