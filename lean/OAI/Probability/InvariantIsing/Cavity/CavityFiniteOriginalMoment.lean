import OAI.Probability.InvariantIsing.Cavity.CavityFiniteOriginalIntegrability
import OAI.Probability.InvariantIsing.Cavity.CavityFiniteCovarianceBound
import OAI.Probability.InvariantIsing.Cavity.CavitySpectralUpperEigenvalues
import OAI.Probability.InvariantIsing.Cavity.CavitySpectralDensitySquare

namespace OAI

/-! Full tilted radial moments for the actual finite spectral cavity law,
with the spectral upper bounds and covariance identities discharged. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Set
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators

namespace InvariantIsing

theorem cavity_finite_original_moment {m d N n k : ℕ}
    (ρ eig : Fin m → ℝ) (hρ : ∀ a, 0 < ρ a) (hsum : ∑ a, ρ a = 1)
    (B : Matrix (Fin (m * N)) (Fin d) ℝ) (hB : B.transpose * B = 1)
    (g : Fin d → Fin m) (a : Fin m) (ha : ∀ b, eig b ≤ eig a)
    (p : OverlapPath) (cut : Fin (n + 2) → ℝ) (hcut : StrictMono cut)
    (hfirst : cut 0 = 0) (hlast : cut (Fin.last (n + 1)) = 1)
    (q : Fin (n + 1) → ℝ) (hq : StrictMono q)
    (hp : ∀ j s, s ∈ Ioo (cut j.castSucc) (cut j.succ) → p s = q j)
    (htop : q (Fin.last n) < 1)
    (L : Matrix (Fin d) (Fin k) ℝ) (C : Matrix (Fin k) (Fin k) ℝ)
    (π : Measure (Spin k)) [IsProbabilityMeasure π] (ℓ : ℕ) :
    let K := B.transpose * cavityRepeatedSpectrum (n := N) eig * B -
      Matrix.diagonal (fun i => eig (g i))
    let H := cavityFiniteCovariancePath ρ eig hρ hsum g p q
    let S := cavityFiniteNoiseCovariance ρ eig hρ hsum g p cut q
    let S₀ := cavityFiniteRootCovariance ρ eig hρ hsum g p q
    let P := (multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) S₀).prod
      (noiseCascadeLaw (EuclideanSpace ℝ (Fin d)) n (chainExponent cut)
        (cavityGaussianMarks S) : Measure _)
    let ν := fun ω => (cavityRootedPriorKernel n (H n) ω).prod π
    let V := fun z => cavityLogFactor K L C (cavityRootedField n z.1) z.2
    (∀ᵐ ω ∂P, Integrable (fun z => Real.exp (V z)) (ν ω) ∧
      Integrable (fun z => ‖cavityRootedField n z.1‖^ℓ) ((ν ω).tilted V)) ∧
    Integrable (fun ω => ∫ z, ‖cavityRootedField n z.1‖^ℓ ∂(ν ω).tilted V) P ∧
    (∫ ω, ∫ z, ‖cavityRootedField n z.1‖^ℓ ∂(ν ω).tilted V ∂P) ≤
      cavityGaussianLinearMomentBound d ℓ (cavityMatrixMass L + cavityMatrixMass C) (ρ a)⁻¹ := by
  intro K H S S₀ P ν V
  let A := B.transpose * cavityRepeatedSpectrum (n := N) eig * B
  let A₀ := Matrix.diagonal (fun i => eig (g i))
  have hA : A.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    change A.transpose = A
    dsimp only [A, cavityRepeatedSpectrum]
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
  have hA₀ : A₀.IsHermitian := by
    apply Matrix.isHermitian_iff_isSymm.mpr
    exact Matrix.diagonal_transpose _
  have heig := cavity_compressed_eigenvalues_le eig a ha B hB hA
  have heig₀ := cavity_diagonal_eigenvalues_le eig g a ha hA₀
  let x := cavityFiniteDeficitPath p q
  let q' := fun i => q (cavityFiniteLevel n i)
  have hx (i : ℕ) : 0 < x i :=
    cavityFiniteDeficitPath_pos p cut hfirst hlast q hq.monotone hp htop i
  have hpath (i : ℕ) : cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i) = H i := by
    rw [cavitySpectralMatrixPath_pos_eq ρ eig hρ hsum A₀ hA₀ a heig₀ (hx i)]
    rfl
  have hdensity : q' 0 • cavitySpectralMatrixDensity ρ eig hρ hsum A₀ hA₀ (x 0) = S₀ := by
    rw [cavitySpectralMatrixDensity_eq_square ρ eig hρ hsum A₀ hA₀ a heig₀ (hx 0), hpath]
    simp only [q', cavityFiniteLevel_zero]
    rfl
  have hgap (i : ℕ) (hi : i < n) : x i - x (i + 1) =
      chainExponent cut i * (q' (i + 1) - q' i) := by
    have h0 : cavityFiniteLevel n i = (⟨i,hi⟩ : Fin n).castSucc := cavityFiniteLevel_castSucc ⟨i,hi⟩
    have h1 : cavityFiniteLevel n (i + 1) = (⟨i,hi⟩ : Fin n).succ := cavityFiniteLevel_succ ⟨i,hi⟩
    simpa only [x, q', h0, h1] using
      cavityFiniteDeficitPath_step p cut hcut hfirst hlast q hq hp ⟨i,hi⟩
  have ht : x n = 1 - q' n := by
    simp only [x, cavityFiniteDeficitPath, q', cavityFiniteLevel_last]
    exact deficit_eq_one_sub_of_ae_le p
      ((finite_overlap_ae_bounds p cut hfirst hlast q hq.monotone hp).mono (fun _ h => h.2))
  have hS (i : ℕ) : (S i).PosSemidef :=
    cavityFiniteNoiseCovariance_posSemidef ρ eig hρ hsum g p cut hcut hfirst hlast q hq hp htop i
  have hΔ (i : ℕ) : cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x i) -
      cavitySpectralMatrixPath ρ eig hρ hsum A₀ hA₀ (x (i + 1)) = chainExponent cut i • S i := by
    rw [hpath, hpath]
    exact cavityFiniteNoiseCovariance_delta ρ eig hρ hsum g p cut hcut hfirst q i
  have hm := cavity_diagonal_spectral_full_moment ρ eig hρ hsum A A₀ hA hA₀
    (fun i => eig (g i)) rfl a (fun i => ha (g i)) heig heig₀ q' x (chainExponent cut) S
    (hq.monotone.comp (cavityFiniteLevel_monotone n))
    (by simpa only [q', cavityFiniteLevel_zero] using
      (finite_overlap_value_mem_unit p cut hcut q hp 0).1)
    hx (cavityFiniteDeficitPath_antitone p q hq.monotone)
    (chainExponent_admissible hcut hfirst hlast) (finite_chainExponent_pos cut hcut hfirst)
    hgap ht hS hΔ π L C ℓ
  simpa only [hpath, hdensity, Kernel.prod_apply, Kernel.const_apply] using hm

end InvariantIsing

end

end OAI
