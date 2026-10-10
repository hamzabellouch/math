import OAI.Geometry.IsometricImmersion.Coordinates.AffinePushforward
import OAI.Geometry.IsometricImmersion.Assembly.SupportedPerturbations
import Mathlib.Analysis.Calculus.ContDiff.Bounds

namespace OAI

noncomputable section
open Set Function
open scoped ContDiff Topology BigOperators Matrix Matrix.Norms.Elementwise

namespace SmoothLocal.Geometry
open SmoothLocal.Perturbation

private def affineTensorCongruenceValue
    (R A : Matrix (Fin 2) (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ := R⁻¹ᵀ * A * R⁻¹

private theorem affineTensorCongruenceValue_add
    (R A B : Matrix (Fin 2) (Fin 2) ℝ) :
    affineTensorCongruenceValue R (A+B) =
      affineTensorCongruenceValue R A + affineTensorCongruenceValue R B := by
  simp only [affineTensorCongruenceValue, Matrix.mul_add, Matrix.add_mul]

private theorem affineTensorCongruenceValue_smul
    (R A : Matrix (Fin 2) (Fin 2) ℝ) (c : ℝ) :
    affineTensorCongruenceValue R (c • A) = c • affineTensorCongruenceValue R A := by
  simp only [affineTensorCongruenceValue, Matrix.mul_smul, Matrix.smul_mul]

def affineTensorCongruence (R : Matrix (Fin 2) (Fin 2) ℝ) :
    (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → Fin 2 → ℝ) :=
  LinearMap.toContinuousLinearMap
    { toFun := affineTensorCongruenceValue R
      map_add' := affineTensorCongruenceValue_add R
      map_smul' := fun c A => affineTensorCongruenceValue_smul R A c }

theorem affineTensorCongruence_apply (R A : Matrix (Fin 2) (Fin 2) ℝ) :
    affineTensorCongruence R A = R⁻¹ᵀ * A * R⁻¹ := rfl

theorem iteratedFDeriv_comp_affineInverse
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Coord → F} {U : Set Coord} (hf : ContDiffOn ℝ ∞ f U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) {p : Coord}
    (hp : affineInverseCoordinates b R p ∈ U) (n : ℕ) :
    iteratedFDeriv ℝ n (f ∘ affineInverseCoordinates b R) p =
      (iteratedFDeriv ℝ n f (affineInverseCoordinates b R p)).compContinuousLinearMap
        (fun _ : Fin n => matrixContinuousLinear R⁻¹) := by
  let L : Coord →L[ℝ] Coord := matrixContinuousLinear R⁻¹
  change iteratedFDeriv ℝ n (fun x => (f ∘ L) (x-b)) p = _
  rw [iteratedFDeriv_comp_sub]
  have hpre : IsOpen (L ⁻¹' U) := hU.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hf hU.uniqueDiffOn hpre.uniqueDiffOn hp
    (i := n) (WithTop.coe_le_coe.mpr le_top)
  rw [iteratedFDerivWithin_of_isOpen n hpre hp,
    iteratedFDerivWithin_of_isOpen n hU (show L (p-b) ∈ U from hp)] at he
  exact he

theorem iteratedFDeriv_affinePushforwardMetric
    {η : MetricField} {U : Set Coord} (hη : ContDiffOn ℝ ∞ η U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) {p : Coord}
    (hp : affineInverseCoordinates b R p ∈ U) (n : ℕ) :
    iteratedFDeriv ℝ n (affinePushforwardMetric η b R) p =
      (affineTensorCongruence R).compContinuousMultilinearMap
        ((iteratedFDeriv ℝ n η (affineInverseCoordinates b R p)).compContinuousLinearMap
          (fun _ : Fin n => matrixContinuousLinear R⁻¹)) := by
  have hinv := affineInverseCoordinates_contDiff b R
  have hcomp : ContDiffOn ℝ ∞ (η ∘ affineInverseCoordinates b R)
      (affineInverseCoordinates b R ⁻¹' U) :=
    hη.comp hinv.contDiffOn (fun _ hq => hq)
  have hpre := hU.preimage hinv.continuous
  change iteratedFDeriv ℝ n ((affineTensorCongruence R) ∘
    (η ∘ affineInverseCoordinates b R)) p = _
  calc
    _ = (affineTensorCongruence R).compContinuousMultilinearMap
        (iteratedFDeriv ℝ n (η ∘ affineInverseCoordinates b R) p) :=
      (affineTensorCongruence R).iteratedFDeriv_comp_left
        (hcomp.contDiffAt (hpre.mem_nhds hp)) (WithTop.coe_le_coe.mpr le_top)
    _ = _ := congrArg (affineTensorCongruence R).compContinuousMultilinearMap
      (iteratedFDeriv_comp_affineInverse hη hU b R hp n)

theorem iteratedFDeriv_affinePushforwardMetric_apply
    {η : MetricField} {U : Set Coord} (hη : ContDiffOn ℝ ∞ η U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) {p : Coord}
    (hp : affineInverseCoordinates b R p ∈ U) (n : ℕ) (v : Fin n → Coord) :
    iteratedFDeriv ℝ n (affinePushforwardMetric η b R) p v =
      R⁻¹ᵀ * (iteratedFDeriv ℝ n η (affineInverseCoordinates b R p)
        (fun i => R⁻¹ *ᵥ v i)) * R⁻¹ := by
  rw [iteratedFDeriv_affinePushforwardMetric hη hU b R hp n]
  rfl

def affineTensorJetFactor (R : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) : ℝ :=
  ‖affineTensorCongruence R‖ * ‖matrixContinuousLinear R⁻¹‖^n

theorem affineTensorJetFactor_nonneg (R : Matrix (Fin 2) (Fin 2) ℝ) (n : ℕ) :
    0 ≤ affineTensorJetFactor R n := by
  unfold affineTensorJetFactor
  positivity

theorem norm_iteratedFDeriv_affinePushforwardMetric_le
    {η : MetricField} {U : Set Coord} (hη : ContDiffOn ℝ ∞ η U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) {p : Coord}
    (hp : affineInverseCoordinates b R p ∈ U) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (affinePushforwardMetric η b R) p‖ ≤
      affineTensorJetFactor R n * ‖iteratedFDeriv ℝ n η (affineInverseCoordinates b R p)‖ := by
  rw [iteratedFDeriv_affinePushforwardMetric hη hU b R hp n]
  have hright := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ n η (affineInverseCoordinates b R p))
    (fun _ : Fin n => matrixContinuousLinear R⁻¹)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hright
  calc
    _ ≤ ‖affineTensorCongruence R‖ *
      ‖(iteratedFDeriv ℝ n η (affineInverseCoordinates b R p)).compContinuousLinearMap
        (fun _ : Fin n => matrixContinuousLinear R⁻¹)‖ :=
      (affineTensorCongruence R).norm_compContinuousMultilinearMap_le _
    _ ≤ ‖affineTensorCongruence R‖ *
        (‖iteratedFDeriv ℝ n η (affineInverseCoordinates b R p)‖ *
          ‖matrixContinuousLinear R⁻¹‖^n) :=
      mul_le_mul_of_nonneg_left hright (norm_nonneg _)
    _ = _ := by unfold affineTensorJetFactor; ring

theorem affinePushforwardMetric_jet_bound_on
    {η : MetricField} {U S : Set Coord} (hη : ContDiffOn ℝ ∞ η U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (hSU : MapsTo (affineInverseCoordinates b R) S U) (n : ℕ) {B : ℝ}
    (hB : ∀ p ∈ S, ‖iteratedFDeriv ℝ n η (affineInverseCoordinates b R p)‖ ≤ B) :
    ∀ p ∈ S, ‖iteratedFDeriv ℝ n (affinePushforwardMetric η b R) p‖ ≤
      affineTensorJetFactor R n * B := by
  intro p hp
  exact (norm_iteratedFDeriv_affinePushforwardMetric_le hη hU b R (hSU hp) n).trans
    (mul_le_mul_of_nonneg_left (hB p hp) (affineTensorJetFactor_nonneg R n))

theorem supported_affine_tensor_jet_le_seminorm
    (η : SymmetricPerturbation) (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (n : ℕ) (p : Coord) :
    ‖iteratedFDeriv ℝ n (affinePushforwardMetric (perturbationTensor η) b R) p‖ ≤
      affineTensorJetFactor R n * perturbationSeminorm n η := by
  exact (norm_iteratedFDeriv_affinePushforwardMetric_le
    (perturbationTensor_contDiff η).contDiffOn isOpen_univ b R (mem_univ _) n).trans
      (mul_le_mul_of_nonneg_left (perturbation_derivative_norm_le η n _)
        (affineTensorJetFactor_nonneg R n))

def affineTensorOrderFactor (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) : ℝ :=
  1 + ‖affineTensorCongruence R‖ * (1 + ‖matrixContinuousLinear R⁻¹‖)^N

theorem affineTensorOrderFactor_pos (R : Matrix (Fin 2) (Fin 2) ℝ) (N : ℕ) :
    0 < affineTensorOrderFactor R N := by
  unfold affineTensorOrderFactor
  positivity

theorem affineTensorJetFactor_le_orderFactor
    (R : Matrix (Fin 2) (Fin 2) ℝ) {n N : ℕ} (hn : n ≤ N) :
    affineTensorJetFactor R n ≤ affineTensorOrderFactor R N := by
  have hpow : ‖matrixContinuousLinear R⁻¹‖^n ≤ (1+‖matrixContinuousLinear R⁻¹‖)^N :=
    (pow_le_pow_left₀ (norm_nonneg _) (by linarith :
      ‖matrixContinuousLinear R⁻¹‖ ≤ 1+‖matrixContinuousLinear R⁻¹‖) n).trans
        (pow_le_pow_right₀ (by linarith [norm_nonneg (matrixContinuousLinear R⁻¹)]) hn)
  have hmul := mul_le_mul_of_nonneg_left hpow (norm_nonneg (affineTensorCongruence R))
  unfold affineTensorJetFactor affineTensorOrderFactor
  linarith

theorem supported_affine_tensor_finite_jet_le
    (η : SymmetricPerturbation) (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    {n N : ℕ} (hn : n ≤ N) (p : Coord) :
    ‖iteratedFDeriv ℝ n (affinePushforwardMetric (perturbationTensor η) b R) p‖ ≤
      affineTensorOrderFactor R N * perturbationSeminorm n η := by
  have hsemi : 0 ≤ perturbationSeminorm n η :=
    (norm_nonneg _).trans (perturbation_derivative_norm_le η n (0 : Coord))
  exact (supported_affine_tensor_jet_le_seminorm η b R n p).trans
    (mul_le_mul_of_nonneg_right (affineTensorJetFactor_le_orderFactor R hn) hsemi)

def affineTensorEntry (i j : Fin 2) : (Fin 2 → Fin 2 → ℝ) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj j : (Fin 2 → ℝ) →L[ℝ] ℝ).comp
    (ContinuousLinearMap.proj i : (Fin 2 → Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ))

theorem affineTensorEntry_norm_le (i j : Fin 2) : ‖affineTensorEntry i j‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro A
  change ‖A i j‖ ≤ 1*‖A‖
  rw [one_mul]
  exact (norm_le_pi_norm (A i) j).trans (norm_le_pi_norm A i)

theorem norm_iteratedFDeriv_affinePushforwardCoefficient_le
    {η : MetricField} {U : Set Coord} (hη : ContDiffOn ℝ ∞ η U) (hU : IsOpen U)
    (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ) {p : Coord}
    (hp : affineInverseCoordinates b R p ∈ U) (n : ℕ) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun q => affinePushforwardMetric η b R q i j) p‖ ≤
      ‖iteratedFDeriv ℝ n (affinePushforwardMetric η b R) p‖ := by
  have hcomp : ContDiffOn ℝ ∞ (η ∘ affineInverseCoordinates b R)
      (affineInverseCoordinates b R ⁻¹' U) :=
    hη.comp (affineInverseCoordinates_contDiff b R).contDiffOn (fun _ hq => hq)
  have htensor : ContDiffOn ℝ ∞ (affinePushforwardMetric η b R)
      (affineInverseCoordinates b R ⁻¹' U) :=
    (affineTensorCongruence R).contDiff.comp_contDiffOn hcomp
  have hpre := hU.preimage (affineInverseCoordinates_contDiff b R).continuous
  have hleft := (affineTensorEntry i j).norm_iteratedFDeriv_comp_left
    (htensor.contDiffAt (hpre.mem_nhds hp)) (n := n) (WithTop.coe_le_coe.mpr le_top)
  exact hleft.trans ((mul_le_mul_of_nonneg_right (affineTensorEntry_norm_le i j)
    (norm_nonneg _)).trans_eq (one_mul _))

theorem supported_affine_tensor_coefficient_jet_le_seminorm
    (η : SymmetricPerturbation) (b : Coord) (R : Matrix (Fin 2) (Fin 2) ℝ)
    (n : ℕ) (p : Coord) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ n (fun q => affinePushforwardMetric (perturbationTensor η) b R q i j) p‖ ≤
      affineTensorJetFactor R n * perturbationSeminorm n η :=
  (norm_iteratedFDeriv_affinePushforwardCoefficient_le
    (perturbationTensor_contDiff η).contDiffOn isOpen_univ b R (mem_univ _) n i j).trans
      (supported_affine_tensor_jet_le_seminorm η b R n p)

end SmoothLocal.Geometry

end

end OAI
