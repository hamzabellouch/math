import Mathlib
import OAI.Analysis.Conductivity.Variational.DetIdAddRank
import OAI.Analysis.Conductivity.Geometry.SplitJacobian

namespace OAI

noncomputable section

open MeasureTheory
open scoped ENNReal
open Matrix Filter Topology
open Set MeasureTheory Filter Topology
open scoped BigOperators
open Set MeasureTheory Filter Topology
open scoped Manifold
open Set Filter
open scoped Topology
open Set Filter MeasureTheory
open scoped Topology Manifold ENNReal
open Set
namespace ScalarConductivity

section
open Matrix Set
open scoped Matrix.Norms.Elementwise

lemma splitJacobian_det (d : Coord3) (L : Coord3 →L[ℝ] ℝ)
    (hLd : L d = 1) (c z : ℝ) : (splitJacobian d L c z).det = 1 + c*z := by
  rw [splitJacobian, operatorMatrix_det]
  have he : lineShiftGradientOperator d c (z • L) = ((c*z) • L).smulRight d := by
    ext v j
    simp [lineShiftGradientOperator_apply]
    ring
  rw [he, det_id_add_rankOne]
  simp [hLd]

def normalStretch (i : Fin 3) (q : ℝ) : Mat3 :=
  Matrix.diagonal (fun j => if j = i then q else 1)

lemma normalStretch_det (i : Fin 3) (q : ℝ) : (normalStretch i q).det = q := by
  rw [normalStretch, Matrix.det_diagonal]
  simp

lemma normalStretch_push (i : Fin 3) {q : ℝ} (hq : q ≠ 0) (B : DiagonalTriple) :
    (normalStretch i q).det⁻¹ • (normalStretch i q * Matrix.diagonal B *
      (normalStretch i q)ᵀ) = Matrix.diagonal (stretchedDiagonal i q B) := by
  rw [normalStretch_det, normalStretch, Matrix.diagonal_transpose,
    Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_smul]
  congr 1
  ext j
  by_cases hj : j = i
  · simp [stretchedDiagonal, hj]
    field_simp
  · simp [stretchedDiagonal, hj, div_eq_mul_inv]
    ring

lemma normalStretch_eq_splitJacobian (i : Fin 3) (c z : ℝ) :
    normalStretch i (1+c*z) =
      splitJacobian (Pi.single i 1) (ContinuousLinearMap.proj i) c z := by
  ext j k
  simp only [normalStretch, splitJacobian, operatorMatrix, LinearMap.toMatrix'_apply,
    ContinuousLinearMap.coe_coe, _root_.add_apply,
    ContinuousLinearMap.id_apply, lineShiftGradientOperator_apply,
    _root_.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]
  by_cases hj : j = i <;> by_cases hk : k = i <;> by_cases hjk : j = k <;>
    simp_all

lemma preliminary_segment (i : Fin 3) {α β : DiagonalTriple} {θ : ℝ}
    (hα : 0 < α i) (hβ : 0 < β i) (hθ : 0 < θ) (hθ' : θ < 1) (z : ℝ) :
    let A := coordinateJoin i θ α β
    let qp := preliminaryQ i A α
    let qm := preliminaryQ i A β
    let ep := θ / qp
    let em := (1-θ) / qm
    A + z • (preliminaryB i A α - preliminaryB i A β) =
      (z+ep) • preliminaryB i A α + (1-(z+ep)) • preliminaryB i A β ∧
    1+z*(qp-qm) = (z+ep)*qp + (1-(z+ep))*qm ∧ ep+em=1 := by
  let A := coordinateJoin i θ α β
  let qp := preliminaryQ i A α
  let qm := preliminaryQ i A β
  let ep := θ / qp
  let em := (1-θ) / qm
  let P := preliminaryB i A α
  let M := preliminaryB i A β
  change A + z • (P-M) = (z+ep) • P + (1-(z+ep)) • M ∧
    1+z*(qp-qm) = (z+ep)*qp + (1-(z+ep))*qm ∧ ep+em=1
  have hf := preliminary_fractions hα hβ hθ hθ'
  have he : ep+em=1 := by
    simpa [ep, em, qp, qm, A, preliminaryQ, coordinateJoin] using hf.2.2.2.2.1
  have hq : ep*qp + em*qm=1 := by
    simpa [ep, em, qp, qm, A, preliminaryQ, coordinateJoin] using hf.2.2.2.2.2
  have hmeans : ep • P + em • M = A := preliminary_matrix_mean i hα hβ hθ hθ'
  have he' : em = 1-ep := by linarith only [he]
  refine ⟨?_, ?_, he⟩
  · ext j
    have hj := congrFun hmeans j
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hj ⊢
    rw [he'] at hj
    linear_combination -hj
  · rw [he'] at hq
    linear_combination -hq

theorem affine_synchronized_path (i : Fin 3) {α β : DiagonalTriple} {θ : ℝ}
    (hα : 0 < α i) (hβ : 0 < β i) (hθ : 0 < θ) (hθ' : θ < 1) :
    let A := coordinateJoin i θ α β
    let qp := preliminaryQ i A α
    let qm := preliminaryQ i A β
    let ep := θ / qp
    let em := (1-θ) / qm
    ∀ z ∈ Icc (-ep) em,
      0 < 1+z*(qp-qm) ∧ ∃ w ∈ Icc (0 : ℝ) 1,
        stretchedDiagonal i (1+z*(qp-qm))
          (A + z • (preliminaryB i A α - preliminaryB i A β)) =
          coordinateJoin i w α β := by
  dsimp only
  intro z hz
  have he := preliminary_segment i hα hβ hθ hθ' z
  have hτ₀ : 0 ≤ z + θ / preliminaryQ i (coordinateJoin i θ α β) α := by linarith [hz.1]
  have hτ₁ : z + θ / preliminaryQ i (coordinateJoin i θ α β) α ≤ 1 := by
    linarith [hz.2, he.2.2]
  have hp := synchronized_path_is_join i hα hβ hθ hθ' hτ₀ hτ₁
  rw [he.1, he.2.1]
  exact ⟨hp.1, _, ⟨hp.2.1, hp.2.2.1⟩, hp.2.2.2⟩

end

open MeasureTheory Set Filter Topology

lemma measure_image_le_det
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    {f : E → E} {s : Set E} (hs : MeasurableSet s)
    (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) (hinj : InjOn f s)
    {C : ℝ} (hC : ∀ x ∈ s, |(fderiv ℝ f x).det| ≤ C) :
    μ (f '' s) ≤ ENNReal.ofReal C * μ s := by
  rw [← lintegral_abs_det_fderiv_eq_addHaar_image μ hs
    (fun x hx => (hf x hx).hasFDerivAt.hasFDerivWithinAt) hinj]
  calc
    (∫⁻ x in s, ENNReal.ofReal |(fderiv ℝ f x).det| ∂μ) ≤
        ∫⁻ _ in s, ENNReal.ofReal C ∂μ :=
      setLIntegral_mono' hs (fun x hx => ENNReal.ofReal_le_ofReal (hC x hx))
    _ = _ := by simp

lemma chart_impure_measure_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (μ : Measure E) [μ.IsAddHaarMeasure]
    (X : OpenPartialHomeomorph E E) (L : E →L[ℝ] ℝ)
    {V : Set E} (hV : IsOpen V) (hVX : V ⊆ X.source)
    (hXi : DifferentiableOn ℝ X.symm X.target)
    {C : ℝ} (hC : ∀ y ∈ X '' V, |(fderiv ℝ X.symm y).det| ≤ C)
    (θ δ k : ℝ) (hθ : 0 ≤ θ) (hδ : 0 < δ) :
    μ {x | x ∈ V ∧ periodicPulse θ δ (k * L (X x)) ≠ 0 ∧
      periodicPulse θ δ (k * L (X x)) ≠ 1} ≤
    ENNReal.ofReal C * μ {y | y ∈ X '' V ∧ periodicPulse θ δ (k * L y) ≠ 0 ∧
      periodicPulse θ δ (k * L y) ≠ 1} := by
  have hθδ : Continuous (periodicPulse θ δ) := (periodicPulse_smooth hθ hδ).continuous
  let s := {y | y ∈ X '' V ∧ periodicPulse θ δ (k * L y) ≠ 0 ∧
      periodicPulse θ δ (k * L y) ≠ 1}
  have hXV : IsOpen (X '' V) := X.isOpen_image_of_subset_source hV hVX
  have hp : Continuous (fun y => periodicPulse θ δ (k * L y)) :=
    hθδ.comp (continuous_const.mul L.continuous)
  have hs : MeasurableSet s := hXV.measurableSet.inter
    ((isOpen_ne.preimage hp).measurableSet.inter
      (isOpen_ne.preimage hp).measurableSet)
  have hsX : s ⊆ X.target := fun _ hy => by
    obtain ⟨x, hx, rfl⟩ := hy.1
    exact X.map_source (hVX hx)
  have he : X.symm '' s = {x | x ∈ V ∧ periodicPulse θ δ (k * L (X x)) ≠ 0 ∧
      periodicPulse θ δ (k * L (X x)) ≠ 1} := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨z, hz, rfl⟩ := hy.1
      change X.symm (X z) ∈ V ∧
        periodicPulse θ δ (k * L (X (X.symm (X z)))) ≠ 0 ∧
        periodicPulse θ δ (k * L (X (X.symm (X z)))) ≠ 1
      rw [X.left_inv (hVX hz)]
      exact ⟨hz, hy.2⟩
    · intro hx
      exact ⟨X x, ⟨⟨x, hx.1, rfl⟩, hx.2⟩, X.left_inv (hVX hx.1)⟩
  rw [← he]
  exact measure_image_le_det μ hs
    (fun y hy => (hXi y (hsX hy)).differentiableAt (X.open_target.mem_nhds (hsX hy)))
    (X.symm.injOn.mono hsX) (fun y hy => hC y hy.1)

end ScalarConductivity

end

end OAI
