import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.CutoffResidualCoefficients

namespace OAI

/-! # Uniform finite jets of the normalized cutoff residual -/

open scoped SchwartzMap Laplacian ContDiff

namespace DefocusingNLS

local notation "E" => EuclideanSpace ℝ (Fin 12)

theorem normalizedPhysicalProfile_fderiv (a L : ℝ) (hL : 0 < L)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (x v : E) :
    fderiv ℝ (normalizedPhysicalProfile a L Q) x v =
      (L ^ (2 * a + 1) : ℝ) * fderiv ℝ Q (L • x) v := by
  have hin : DifferentiableAt ℝ (fun y : E => Q (L • y)) x :=
    (hQ.comp (contDiff_id.const_smul L)).differentiable (by simp) x
  have hp : L ^ (2 * a) * L = L ^ (2 * a + 1) := by
    calc
      _ = L ^ (2 * a) * L ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := (Real.rpow_add hL _ _).symm
  unfold normalizedPhysicalProfile
  rw [fderiv_fun_const_smul hin, fderiv_comp_smul]
  simp only [smul_apply, Complex.real_smul]
  rw [← mul_assoc, ← Complex.ofReal_mul, hp]

private theorem weightedJet_add (ψ φ : 𝓢(E, ℂ)) (N n : ℕ) (x : E) :
    (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n (ψ + φ) x‖ ≤
      (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n ψ x‖ +
      (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n φ x‖ := by
  have h : iteratedFDeriv ℝ n (ψ + φ) x =
      iteratedFDeriv ℝ n ψ x + iteratedFDeriv ℝ n φ x := by
    exact iteratedFDeriv_add_apply (ψ.smooth'.contDiffAt.of_le (by simp))
      (φ.smooth'.contDiffAt.of_le (by simp))
  rw [h, ← mul_add]
  exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)

private theorem weightedJet_sum {ι : Type*} (s : Finset ι) (ψ : ι → 𝓢(E, ℂ))
    (N n : ℕ) (x : E) :
    (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n (∑ j ∈ s, ψ j : 𝓢(E, ℂ)) x‖ ≤
      ∑ j ∈ s, (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n (ψ j) x‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact (weightedJet_add (ψ i) (∑ j ∈ s, ψ j) N n x).trans (add_le_add le_rfl ih)

private theorem weightedJet_two_smul (ψ : 𝓢(E, ℂ)) (N n : ℕ) (x : E) :
    (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n ((2 : ℂ) • ψ) x‖ =
      2 * ((1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n ψ x‖) := by
  have h : iteratedFDeriv ℝ n ((2 : ℂ) • ψ) x =
      (2 : ℂ) • iteratedFDeriv ℝ n ψ x :=
    iteratedFDeriv_const_smul_apply (ψ.smooth'.contDiffAt.of_le (by simp))
  rw [h, norm_smul]
  norm_num
  ring

private theorem weightedJet_assembly (P : Fin 12 → 𝓢(E, ℂ)) (R S : 𝓢(E, ℂ))
    (N n : ℕ) (x : E) (G : Fin 12 → ℝ) (H K : ℝ)
    (hP : ∀ j, (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n (P j) x‖ ≤ G j)
    (hR : (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n R x‖ ≤ H)
    (hS : (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n S x‖ ≤ K) :
    (1 + ‖x‖) ^ N *
      ‖iteratedFDeriv ℝ n (((2 : ℂ) • ∑ j, P j) + R + S : 𝓢(E, ℂ)) x‖ ≤
        2 * (∑ j, G j) + H + K := by
  calc
    _ ≤ ((1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n ((2 : ℂ) • ∑ j, P j) x‖ +
        (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n R x‖) +
        (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n S x‖ :=
      (weightedJet_add _ S N n x).trans (add_le_add (weightedJet_add _ R N n x) le_rfl)
    _ ≤ 2 * (∑ j, G j) + H + K := by
      rw [weightedJet_two_smul]
      exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left
        ((weightedJet_sum Finset.univ P N n x).trans (Finset.sum_le_sum fun j _ => hP j))
        (by norm_num)) hR) hS

section Residual

variable (χ : 𝓢(E, ℝ)) (hχ : HasCompactSupport (χ : E → ℝ))
  (hχone : ∀ x : E, ‖x‖ < 1 / 2 → χ x = 1)
  (hχzero : ∀ x : E, 2 < ‖x‖ → χ x = 0)

include hχone hχzero in
private theorem gradient_compact (j : Fin 12) :
    HasCompactSupport (cutoffGradientCoefficient χ j : E → ℂ) :=
  hasCompactSupport_of_cutoff_annulus _ (cutoffGradientCoefficient_annulus χ hχone hχzero j)

include hχone hχzero in
private theorem laplacian_compact :
    HasCompactSupport (cutoffLaplacianCoefficient χ : E → ℂ) :=
  hasCompactSupport_of_cutoff_annulus _ (cutoffLaplacianCoefficient_annulus χ hχone hχzero)

include hχone hχzero in
private theorem power_compact (m : ℕ) :
    HasCompactSupport (cutoffPowerCoefficient χ hχ m : E → ℂ) :=
  hasCompactSupport_of_cutoff_annulus _ (cutoffPowerCoefficient_annulus χ hχ m hχone hχzero)

noncomputable def normalizedCutoffResidualSchwartz (a L : ℝ) (m : ℕ)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) : 𝓢(E, ℂ) :=
  let f := normalizedPhysicalProfile a L Q
  let hf := normalizedPhysicalProfile_contDiff a L Q hQ
  let hdf := (contDiff_infty_iff_fderiv.mp hf).2
  (2 : ℂ) • (∑ j : Fin 12, annularCoefficientProduct
    (cutoffGradientCoefficient χ j) (gradient_compact χ hχone hχzero j)
    (fun x => fderiv ℝ f x ((EuclideanSpace.basisFun (Fin 12) ℝ) j))
    (hdf.clm_apply contDiff_const)) +
  annularCoefficientProduct (cutoffLaplacianCoefficient χ) (laplacian_compact χ hχone hχzero)
    f hf +
  annularCoefficientProduct (cutoffPowerCoefficient χ hχ m) (power_compact χ hχ hχone hχzero m)
    (fun x => oddPowerNonlinearity m (f x))
    (((contDiff_oddPowerNonlinearity m).of_le (show (∞ : ℕ∞ω) ≤ ⊤ by simp)).comp hf)

theorem normalizedCutoffResidualSchwartz_apply (a L : ℝ) (m : ℕ) (hL : 0 < L)
    (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q) (x : E) :
    normalizedCutoffResidualSchwartz χ hχ hχone hχzero a L m Q hQ x =
      normalizedCutoffResidual a L m χ Q x := by
  simp only [normalizedCutoffResidualSchwartz, add_apply, smul_apply,
    sum_apply, annularCoefficientProduct_apply, cutoffGradientCoefficient_apply,
    cutoffLaplacianCoefficient_apply, cutoffPowerCoefficient_apply,
    normalizedPhysicalProfile_fderiv a L hL Q hQ, normalizedPhysicalProfile,
    Complex.real_smul, normalizedCutoffResidual, smul_eq_mul]

attribute [local irreducible] cutoffGradientCoefficient cutoffLaplacianCoefficient
  cutoffPowerCoefficient annularCoefficientProduct

theorem exists_normalizedCutoffResidual_uniform_jets (a : ℝ) (ha : 0 < a) (m N : ℕ)
    (D : ℝ) (hD : 0 ≤ D) (Q : E → ℂ) (hQ : ContDiff ℝ ∞ Q)
    (hsymbol : ∀ n ≤ N + 1, ∀ y : E, y ≠ 0 →
      ‖iteratedFDeriv ℝ n Q y‖ ≤ D * ‖y‖ ^ (-2 * a - (n : ℝ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (L : ℝ), 1 ≤ L → ∀ n ≤ N, ∀ x : E,
      (1 + ‖x‖) ^ N *
        ‖iteratedFDeriv ℝ n (normalizedCutoffResidualSchwartz χ hχ hχone hχzero a L m Q hQ) x‖ ≤ C := by
  let B := D * (1 / 2 : ℝ) ^ (-2 * a - ((N + 1 : ℕ) : ℝ))
  have hB : 0 ≤ B := mul_nonneg hD (Real.rpow_nonneg (by norm_num) _)
  obtain ⟨A, hA, hAjet⟩ := exists_oddPower_finiteJet_bound m N B hB
  let G (j : Fin 12) := 3 ^ N * homogeneousAnnulusCutoffConstant (cutoffGradientCoefficient χ j) N * B
  let H := 3 ^ N * homogeneousAnnulusCutoffConstant (cutoffLaplacianCoefficient χ) N * B
  let K := 3 ^ N * homogeneousAnnulusCutoffConstant (cutoffPowerCoefficient χ hχ m) N * A
  have hG : ∀ j, 0 ≤ G j := fun j => mul_nonneg (mul_nonneg (by positivity)
    (homogeneousAnnulusCutoffConstant_nonneg _ _)) hB
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg (by positivity)
    (homogeneousAnnulusCutoffConstant_nonneg _ _)) hB
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by positivity)
    (homogeneousAnnulusCutoffConstant_nonneg _ _)) hA
  have hsumG : 0 ≤ ∑ j, G j := Finset.sum_nonneg fun j _ => hG j
  refine ⟨2 * (∑ j, G j) + H + K,
    add_nonneg (add_nonneg (mul_nonneg (by norm_num) hsumG) hH) hK, ?_⟩
  intro L hL n hn x
  let f := normalizedPhysicalProfile a L Q
  have hf := normalizedPhysicalProfile_contDiff a L Q hQ
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  have hLp : 0 < L := by linarith
  have hjets (y : E) (hy : (1 / 2 : ℝ) ≤ ‖y‖) (i : ℕ) (hi : i ≤ N + 1) :
      ‖iteratedFDeriv ℝ i f y‖ ≤ B := by
    apply normalizedPhysicalProfile_annulus_bound a L D ha hLp hD Q hQ (N + 1) i hi y hy
    apply hsymbol i hi
    exact smul_ne_zero hLp.ne' (norm_pos_iff.mp (by linarith))
  let P (j : Fin 12) := annularCoefficientProduct
    (cutoffGradientCoefficient χ j) (gradient_compact χ hχone hχzero j)
    (fun y => fderiv ℝ f y ((EuclideanSpace.basisFun (Fin 12) ℝ) j))
    (hdf.clm_apply contDiff_const)
  let R := annularCoefficientProduct (cutoffLaplacianCoefficient χ) (laplacian_compact χ hχone hχzero) f hf
  let S := annularCoefficientProduct (cutoffPowerCoefficient χ hχ m) (power_compact χ hχ hχone hχzero m)
    (fun y => oddPowerNonlinearity m (f y))
    (((contDiff_oddPowerNonlinearity m).of_le (show (∞ : ℕ∞ω) ≤ ⊤ by simp)).comp hf)
  have hP (j : Fin 12) : (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n (P j) x‖ ≤ G j := by
    apply annularCoefficientProduct_jet_bound _ _ (cutoffGradientCoefficient_annulus χ hχone hχzero j)
      _ _ N B hB _ n hn x
    intro y hy i hi
    have h := norm_iteratedFDeriv_directional_le f hf ((EuclideanSpace.basisFun (Fin 12) ℝ) j) i y
    simpa only [OrthonormalBasis.norm_eq_one, one_mul] using
      h.trans (mul_le_mul_of_nonneg_left (hjets y
        ((cutoffGradientCoefficient_annulus χ hχone hχzero j y hy).1) (i + 1) (by omega)) (norm_nonneg _))
  have hR : (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n R x‖ ≤ H := by
    apply annularCoefficientProduct_jet_bound _ _ (cutoffLaplacianCoefficient_annulus χ hχone hχzero)
      _ _ N B hB _ n hn x
    intro y hy i hi
    exact hjets y ((cutoffLaplacianCoefficient_annulus χ hχone hχzero y hy).1) i (by omega)
  have hS : (1 + ‖x‖) ^ N * ‖iteratedFDeriv ℝ n S x‖ ≤ K := by
    apply annularCoefficientProduct_jet_bound _ _ (cutoffPowerCoefficient_annulus χ hχ m hχone hχzero)
      _ _ N A hA _ n hn x
    intro y hy i hi
    exact hAjet f hf y (fun j hj => hjets y
      ((cutoffPowerCoefficient_annulus χ hχ m hχone hχzero y hy).1) j (by omega)) i hi
  exact weightedJet_assembly P R S N n x G H K hP hR hS

end Residual
end DefocusingNLS

end OAI
