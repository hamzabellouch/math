import OAI.Analysis.LiebThirring.ResolventCalculus

namespace OAI

universe u12 u13 u14 u15

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra


namespace SharpLiebThirring.MatrixProof
open ScalarProof MeasureTheory Set Filter Unitary
open scoped Matrix.Norms.L2Operator NNReal Topology
variable {n : Type u12} [Fintype n] [DecidableEq n]

/-- The Schur action obtained by one Gaussian average. -/
def gaussianSchur (z : n → ℝ) (v h : ℝ) (D : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j ↦ (Real.exp (-v * h * (z i - z j) ^ 2) : ℂ) * D i j

lemma gaussianSchur_eq_average (z : n → ℝ) (D : Matrix n n ℂ) {v h : ℝ}
    (hv : 0 ≤ v) (hh : 0 ≤ h) :
    gaussianSchur z v h D = ∫ t,
      conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D
        ∂ProbabilityTheory.gaussianReal 0 ⟨2 * v * h, by positivity⟩ := by
  ext i j
  have he := (gaussian_phase_average z D (⟨2 * v * h, by positivity⟩ : ℝ≥0) i j).symm
  convert! he using 1
  change (Real.exp (-v * h * (z i - z j) ^ 2) : ℂ) * D i j =
    Complex.exp (-((2 * v * h) * (z i - z j) ^ 2 / 2 : ℝ)) * D i j
  rw [Complex.ofReal_exp]
  congr 2
  push_cast
  ring

lemma gaussianSchur_norm_le (z : n → ℝ) (D : Matrix n n ℂ) {v h : ℝ}
    (hv : 0 ≤ v) (hh : 0 ≤ h) : ‖gaussianSchur z v h D‖ ≤ ‖D‖ := by
  rw [gaussianSchur_eq_average z D hv hh]
  apply (norm_integral_le_integral_norm _).trans
  have he (t : ℝ) :
      ‖conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D‖ = ‖D‖ := by
    change ‖(phaseUnitary z t : Matrix n n ℂ) * D *
      ((star (phaseUnitary z t) : unitary (Matrix n n ℂ)) : Matrix n n ℂ)‖ = ‖D‖
    rw [CStarRing.norm_mul_coe_unitary, CStarRing.norm_coe_unitary_mul]
  simp_rw [he]
  rw [integral_const]
  have hp : (ProbabilityTheory.gaussianReal 0 (⟨2 * v * h, by positivity⟩ : ℝ≥0)).real univ = 1 :=
    @probReal_univ ℝ _ _ (ProbabilityTheory.instIsProbabilityMeasureGaussianReal 0 _)
  erw [hp]
  simp only [one_smul, le_refl]

omit [Fintype n] [DecidableEq n] in
lemma continuous_gaussianSchur (z : n → ℝ) (h : ℝ) (D : Matrix n n ℂ) :
    Continuous (fun v ↦ gaussianSchur z v h D) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  unfold gaussianSchur
  fun_prop

lemma gamma_integrable_gaussianSchur {σ h : ℝ} (hσ : σ < 1) (hh : 0 ≤ h)
    (z : n → ℝ) (D : Matrix n n ℂ) :
    IntegrableOn (fun v ↦ gammaWeight σ v • gaussianSchur z v h D) (Ioi 0) := by
  apply ((gammaWeight_integrable hσ).norm.mul_const ‖D‖).mono'
  · exact (gammaWeight_integrable hσ).aestronglyMeasurable.smul
      (continuous_gaussianSchur z h D).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_left (gaussianSchur_norm_le z D (le_of_lt hv) hh) (norm_nonneg _)

def powerSchur (σ : ℝ) (z : n → ℝ) (h : ℝ) (D : Matrix n n ℂ) : Matrix n n ℂ :=
  fun i j ↦ (((1 + h * (z i - z j) ^ 2) ^ (σ - 1) : ℝ) : ℂ) * D i j

lemma gamma_gaussianSchur_integral {σ h : ℝ} (hσ : σ < 1) (hh : 0 ≤ h)
    (z : n → ℝ) (D : Matrix n n ℂ) :
    (∫ v in Ioi (0 : ℝ), gammaWeight σ v • gaussianSchur z v h D) =
      powerSchur σ z h D := by
  ext i j
  have he := (entryCLM i j).integral_comp_comm (gamma_integrable_gaussianSchur hσ hh z D)
  simp only [entryCLM_apply] at he
  rw [← he]
  simp only [Matrix.smul_apply, gaussianSchur, powerSchur, Complex.real_smul,
    ← mul_assoc, ← Complex.ofReal_mul]
  erw [integral_mul_const, integral_ofReal, gamma_mixture hσ hh]
  rfl

lemma powerSchur_trace_comparison {σ h : ℝ} (hσ : σ < 1) (hh : 0 ≤ h)
    (z : n → ℝ) (M D : Matrix n n ℂ)
    (hpoint : ∀ t : ℝ, 0 ≤ (trace (M * (2 • D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D -
      conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D))).re) :
    (trace (M * powerSchur σ z h D)).re ≤ (trace (M * D)).re := by
  have hi := gamma_integrable_gaussianSchur hσ hh z D
  have hp (v : ℝ) (hv : 0 < v) :
      gammaWeight σ v * (trace (M * gaussianSchur z v h D)).re ≤
        gammaWeight σ v * (trace (M * D)).re := by
    apply mul_le_mul_of_nonneg_left _ (gammaWeight_nonneg hσ hv.le)
    rw [gaussianSchur_eq_average z D hv.le hh]
    exact gaussian_trace_comparison z M D _ hpoint
  have hle := integral_mono_ae ((tracePairCLM M).integrable_comp hi)
    ((gammaWeight_integrable hσ).mul_const ((trace (M * D)).re))
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
        simpa only [map_smul, tracePairCLM_apply, smul_eq_mul] using hp v hv)
  rw [(tracePairCLM M).integral_comp_comm hi, gamma_gaussianSchur_integral hσ hh z D,
    integral_mul_const, gammaWeight_integral hσ, one_mul] at hle
  exact hle

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.MatrixProof
open ScalarProof MeasureTheory Set
open scoped Matrix.Norms.L2Operator
variable {n : Type u13} [Fintype n] [DecidableEq n]

def tangentSchur (σ a : ℝ) (z : n → ℝ) (D : Matrix n n ℂ) : Matrix n n ℂ :=
  ∫ τ in Icc (0 : ℝ) 1, powerSchur σ z (τ * (1 - τ) / a) D

omit [Fintype n] [DecidableEq n] in
lemma continuousOn_powerSchur_tau (σ : ℝ) {a : ℝ} (ha : 0 < a)
    (z : n → ℝ) (D : Matrix n n ℂ) :
    ContinuousOn (fun τ ↦ powerSchur σ z (τ * (1 - τ) / a) D) (Icc (0 : ℝ) 1) := by
  apply continuousOn_pi.2
  intro i
  apply continuousOn_pi.2
  intro j
  apply ContinuousOn.mul _ continuousOn_const
  apply Complex.continuous_ofReal.comp_continuousOn
  apply ContinuousOn.rpow_const (by fun_prop)
  intro τ hτ
  left
  have hp : 0 ≤ τ * (1 - τ) / a * (z i - z j) ^ 2 :=
    mul_nonneg (div_nonneg (mul_nonneg hτ.1 (sub_nonneg.2 hτ.2)) ha.le) (sq_nonneg _)
  linarith

lemma integrable_powerSchur_tau (σ : ℝ) {a : ℝ} (ha : 0 < a)
    (z : n → ℝ) (D : Matrix n n ℂ) :
    IntegrableOn (fun τ ↦ powerSchur σ z (τ * (1 - τ) / a) D) (Icc (0 : ℝ) 1) :=
  (continuousOn_powerSchur_tau σ ha z D).integrableOn_Icc

lemma tangentSchur_trace_comparison {σ a : ℝ} (hσ : σ < 1) (ha : 0 < a)
    (z : n → ℝ) (M D : Matrix n n ℂ)
    (hpoint : ∀ t : ℝ, 0 ≤ (trace (M * (2 • D -
      Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (phaseUnitary z t) D -
      Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) (star (phaseUnitary z t)) D))).re) :
    (trace (M * tangentSchur σ a z D)).re ≤ (trace (M * D)).re := by
  have hi := integrable_powerSchur_tau σ ha z D
  have hle := integral_mono_ae ((tracePairCLM M).integrable_comp hi)
    (integrableOn_const (C := (trace (M * D)).re) (s := Icc (0 : ℝ) 1) (by simp)) (by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact powerSchur_trace_comparison hσ
        (div_nonneg (mul_nonneg hτ.1 (sub_nonneg.2 hτ.2)) ha.le) z M D hpoint)
  rw [(tracePairCLM M).integral_comp_comm hi] at hle
  simpa [tangentSchur, tracePairCLM_apply] using hle

lemma tangentSchur_one (σ a : ℝ) (z : n → ℝ) :
    tangentSchur σ a z 1 = 1 := by
  have he : ∀ τ : ℝ, powerSchur σ z (τ * (1 - τ) / a) (1 : Matrix n n ℂ) = 1 := by
    intro τ
    ext i j
    by_cases hij : i = j
    · subst j; simp [powerSchur]
    · simp [powerSchur, hij]
  simp only [tangentSchur, he]
  simp

lemma tangentSchur_selfAdjoint (σ : ℝ) {a : ℝ} (ha : 0 < a)
    (z : n → ℝ) (D M : Matrix n n ℂ) :
    trace (M * tangentSchur σ a z D) = trace (tangentSchur σ a z M * D) := by
  have he (i j) (A : Matrix n n ℂ) :
      tangentSchur σ a z A i j =
        (∫ τ in Icc (0 : ℝ) 1, (((1 + τ * (1 - τ) / a * (z i - z j) ^ 2) ^
          (σ - 1) : ℝ) : ℂ)) * A i j := by
    have hc := (entryCLM i j).integral_comp_comm (integrable_powerSchur_tau σ ha z A)
    simp only [entryCLM_apply] at hc
    rw [tangentSchur, ← hc]
    simp only [powerSchur]
    exact integral_mul_const _ _
  simp only [Matrix.trace]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change M i j * tangentSchur σ a z D j i = tangentSchur σ a z M i j * D j i
  rw [he, he, show (z j - z i) ^ 2 = (z i - z j) ^ 2 by ring]
  ring

end SharpLiebThirring.MatrixProof


namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u14} [Fintype n] [DecidableEq n]

def quadraticTangent (σ δ d : ℝ) (z : n → ℝ) (Z : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  fun i j ↦ (dividedPrimitive σ δ ((s - z i) ^ 2 + d) ((s - z j) ^ 2 + d) : ℂ) * Z i j

lemma integrable_quadraticTangent {σ δ d : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hd : 0 ≤ d) (z : n → ℝ) (Z : Matrix n n ℂ) :
    Integrable (quadraticTangent σ δ d z Z) := by
  let e : (n → n → ℂ) →L[ℝ] Matrix n n ℂ :=
    ({ toFun := Matrix.of
       map_add' := by intros; rfl
       map_smul' := by intros; rfl } : (n → n → ℂ) →ₗ[ℝ] Matrix n n ℂ).toContinuousLinearMap
  apply e.integrable_comp
  apply integrable_pi_iff.2
  intro i
  apply integrable_pi_iff.2
  intro j
  exact (Complex.ofRealCLM.integrable_comp (integrable_divided_quadratic hσ hδ hd (z i) (z j))).mul_const _

lemma tangentSchur_apply (σ : ℝ) {a : ℝ} (ha : 0 < a) (z : n → ℝ) (Z : Matrix n n ℂ) (i j : n) :
    tangentSchur σ a z Z i j =
      ((∫ τ in Icc (0 : ℝ) 1, (1 + τ * (1 - τ) / a * (z i - z j) ^ 2) ^
        (σ - 1) : ℝ) : ℂ) * Z i j := by
  have he := (entryCLM i j).integral_comp_comm (integrable_powerSchur_tau σ ha z Z)
  simp only [entryCLM_apply] at he
  rw [tangentSchur, ← he]
  simp only [powerSchur]
  rw [integral_mul_const]
  exact congrArg (fun t : ℂ ↦ t * Z i j) (integral_ofReal (f := fun τ : ℝ ↦
    (1 + τ * (1 - τ) / a * (z i - z j) ^ 2) ^ (σ - 1)))

/-- Exact integrated tangent map in any diagonalizing basis, not only simple spectrum. -/
lemma integral_quadraticTangent {σ δ d : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (hd : 0 ≤ d) (z : n → ℝ) (Z : Matrix n n ℂ) :
    fieldNormalization σ • ∫ s : ℝ, quadraticTangent σ δ d z Z s =
      (σ * (d + δ) ^ (σ - 1)) • tangentSchur σ (d + δ) z Z := by
  ext i j
  have he := (entryCLM i j).integral_comp_comm (integrable_quadraticTangent hσ hδ hd z Z)
  simp only [entryCLM_apply] at he
  simp only [Matrix.smul_apply]
  rw [← he, tangentSchur_apply σ (by linarith) z Z i j]
  simp only [quadraticTangent]
  rw [integral_mul_const]
  erw [integral_ofReal (f := fun s : ℝ ↦ dividedPrimitive σ δ
    ((s - z i) ^ 2 + d) ((s - z j) ^ 2 + d))]
  simp only [Complex.real_smul, ← mul_assoc]
  have h := congrArg (fun t : ℝ ↦ (t : ℂ) * Z i j)
    (integral_divided_quadratic hσ hδ hd (z i) (z j))
  push_cast at h
  push_cast
  convert! h using 1


lemma primitive_diagonal_tangent {σ δ d : ℝ} (hσ₀ : 0 < σ) (hσ₁ : σ < 1)
    (hδ : 0 < δ) (hd : 0 ≤ d) (z : n → ℝ) (s : ℝ) {X : Matrix n n ℂ}
    (hX : X.PosSemidef) :
    hX.isHermitian.cfc (regularizedPrimitive σ δ) ≤
      cfc (regularizedPrimitive σ δ) (diagonal (fun i ↦ (((s - z i) ^ 2 + d : ℝ) : ℂ))) +
      quadraticTangent σ δ d z (X - diagonal (fun i ↦ (((s - z i) ^ 2 + d : ℝ) : ℂ))) s := by
  have hY := diagonal_real_posSemidef (fun i ↦ (s - z i) ^ 2 + d)
    (fun i ↦ add_nonneg (sq_nonneg _) hd)
  have ht := primitive_cfc_tangent hX hY hσ₀ hσ₁ hδ
  rw [← hY.isHermitian.cfc_eq, integral_resolventTangent_diagonal hσ₀ hσ₁ hδ _
    (fun i ↦ add_nonneg (sq_nonneg _) hd)] at ht
  exact ht

end SharpLiebThirring.MatrixProof

namespace SharpLiebThirring.ScalarProof

lemma primitive_le_tangent {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ) (x y : ℝ) :
    regularizedPrimitive σ δ y ≤ regularizedPrimitive σ δ x +
      (max x 0 + δ) ^ (σ - 3 / 2) * (y - x) := by
  have hc := (primitive_concave hσ hδ).neg
  have hd := (primitive_hasDerivAt σ hδ x).neg
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · have hs := hc.le_slope_of_hasDerivAt (mem_univ x) (mem_univ y) hxy hd
    rw [slope_def_field] at hs
    have := (le_div_iff₀ (sub_pos.2 hxy)).1 hs
    dsimp at this
    nlinarith
  · simp
  · have hs := hc.slope_le_of_hasDerivAt (mem_univ y) (mem_univ x) hyx hd
    rw [slope_def_field] at hs
    have := (div_le_iff₀ (sub_pos.2 hyx)).1 hs
    dsimp at this
    nlinarith

end SharpLiebThirring.ScalarProof

namespace SharpLiebThirring.MatrixProof
open ScalarProof Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
variable {n : Type u15} [Fintype n] [DecidableEq n]

/-- Scalar Jensen inequality for every positive unital real-linear matrix state.
No assertion of operator concavity on the whole line is used. -/
lemma primitive_state_jensen {σ δ : ℝ} (hσ : σ < 1) (hδ : 0 < δ)
    (φ : Matrix n n ℂ →ₗ[ℝ] ℝ) (hφ : ∀ A, A.PosSemidef → 0 ≤ φ A)
    (hφ₁ : φ 1 = 1) {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    φ (cfc (regularizedPrimitive σ δ) A) ≤ regularizedPrimitive σ δ (φ A) := by
  let f := regularizedPrimitive σ δ
  let x := φ A
  let d := (max x 0 + δ) ^ (σ - 3 / 2)
  have ht : cfc f A ≤ cfc (fun y : ℝ ↦ f x + d * (y - x)) A :=
    cfc_mono (fun y _ ↦ primitive_le_tangent hσ hδ x y)
      (primitive_differentiable σ hδ).continuous.continuousOn (by fun_prop)
  have he : cfc (fun y : ℝ ↦ f x + d * (y - x)) A =
      f x • 1 + d • (A - x • 1) := by
    erw [cfc_const_add (f x) (fun y : ℝ ↦ d * (y - x)) A (by fun_prop) hA,
      cfc_const_mul d (fun y : ℝ ↦ y - x) A (by fun_prop),
      cfc_sub id (fun _ : ℝ ↦ x) A (by fun_prop) (by fun_prop),
      cfc_id ℝ A hA, cfc_const x A hA,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
  rw [he] at ht
  have hp := hφ _ (Matrix.nonneg_iff_posSemidef.1 (sub_nonneg.2 ht))
  simp only [map_sub, map_add, map_smul, hφ₁, smul_eq_mul, mul_one] at hp
  dsimp [x] at hp
  linarith

end SharpLiebThirring.MatrixProof

end
end

end OAI
