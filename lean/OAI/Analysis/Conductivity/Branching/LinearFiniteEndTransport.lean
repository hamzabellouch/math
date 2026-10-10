import Mathlib
import OAI.Analysis.Conductivity.Geometry.RegularPatch
import OAI.Analysis.Conductivity.Geometry.RegularPatchLinear
import OAI.Analysis.Conductivity.Flux.FiniteEndPhysicalTensor

namespace OAI


noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory Matrix
open scoped Matrix.Norms.Elementwise

local instance linearFiniteEndTransportMeasurableSpace : MeasurableSpace Mat3 :=
  inferInstanceAs (MeasurableSpace (Fin 3 → Fin 3 → ℝ))
local instance linearFiniteEndTransportBorelSpace : BorelSpace Mat3 :=
  inferInstanceAs (BorelSpace (Fin 3 → Fin 3 → ℝ))

def linearTensorPullback (P : Coord3 ≃L[ℝ] Coord3) (A : Coord3 → Mat3) (x : Coord3) : Mat3 :=
  operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3)*A (P x)*
    (operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3))ᵀ

lemma operatorMatrix_equiv_symm_mul (P : Coord3 ≃L[ℝ] Coord3) :
    operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3)*operatorMatrix (P : Coord3 →L[ℝ] Coord3)=1 := by
  rw [←operatorMatrix_comp]
  have he : (P.symm : Coord3 →L[ℝ] Coord3).comp (P : Coord3 →L[ℝ] Coord3)=ContinuousLinearMap.id ℝ Coord3 := by
    ext x i
    exact congrFun (P.symm_apply_apply x) i
  rw [he,operatorMatrix_id]

lemma linearTensorPullback_symmetric (P : Coord3 ≃L[ℝ] Coord3)
    {A : Coord3 → Mat3} (hA : ∀ x,(A x).IsSymm) (x : Coord3) :
    (linearTensorPullback P A x).IsSymm := by
  unfold linearTensorPullback Matrix.IsSymm
  rw [Matrix.transpose_mul,Matrix.transpose_mul,Matrix.transpose_transpose,(hA _).eq]
  simp only [Matrix.mul_assoc]

lemma linearTensorPullback_measurable (P : Coord3 ≃L[ℝ] Coord3)
    {A : Coord3 → Mat3} (hA : Measurable A) : Measurable (linearTensorPullback P A) :=
  measurable_real_matrix_mul (measurable_real_matrix_mul measurable_const
    (hA.comp P.continuous.measurable)) measurable_const

lemma gradientColumns_linearCoordinates {u : Coord3 → Fin 2 → ℝ}
    {x : Coord3} (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (hu : DifferentiableAt ℝ u (P x)) :
    gradientColumns (fderiv ℝ (fun y => Q (u (P y))) x)=
      (operatorMatrix (P : Coord3 →L[ℝ] Coord3))ᵀ*gradientColumns (fderiv ℝ u (P x))*
        (operatorMatrix (Q : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)))ᵀ := by
  change gradientColumns (fderiv ℝ (Q ∘ u ∘ P) x)=_
  rw [(Q.hasFDerivAt.comp x (hu.hasFDerivAt.comp x P.hasFDerivAt)).fderiv]
  change (operatorMatrix ((Q : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)).comp
    ((fderiv ℝ u (P x)).comp (P : Coord3 →L[ℝ] Coord3))))ᵀ=_
  simp only [operatorMatrix_comp,Matrix.transpose_mul,Matrix.mul_assoc]
  rfl

lemma linearTensorPullback_columns (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) (A : Coord3 → Mat3)
    {u : Coord3 → Fin 2 → ℝ} {x : Coord3} (hu : DifferentiableAt ℝ u (P x)) :
    linearTensorPullback P A x*gradientColumns (fderiv ℝ (fun y => Q (u (P y))) x)=
      operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3)*
        (A (P x)*gradientColumns (fderiv ℝ u (P x)))*
        (operatorMatrix (Q : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ)))ᵀ := by
  rw [gradientColumns_linearCoordinates P Q hu]
  have he : (operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3))ᵀ*
      (operatorMatrix (P : Coord3 →L[ℝ] Coord3))ᵀ=1 := by
    have he0 := operatorMatrix_equiv_symm_mul P.symm
    simp only [ContinuousLinearEquiv.symm_symm] at he0
    rw [←Matrix.transpose_mul,he0,Matrix.transpose_one]
  simp only [linearTensorPullback,Matrix.mul_assoc]
  rw [←Matrix.mul_assoc (operatorMatrix (P.symm : Coord3 →L[ℝ] Coord3))ᵀ,he,Matrix.one_mul]

lemma RegularPatch.linearCoordinates {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {O : Set Coord3} (h : RegularPatch u A O) (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) :
    RegularPatch (fun x => Q (u (P x)))
      (fun x => ⟨linearTensorPullback P (fun y => (A y).val) x,
        linearTensorPullback_symmetric P (fun y => (A y).property) x⟩) (P ⁻¹' O) := by
  refine ⟨h.1.preimage P.continuous,?_,?_,h.2.2.2.linearCoordinates h.1 h.2.1 P Q⟩
  · exact Q.contDiff.comp_contDiffOn (h.2.1.comp P.contDiff.contDiffOn (fun _ hx => hx))
  · change ContDiffOn ℝ (↑(⊤ : ℕ∞)) (linearTensorPullback P (fun y => (A y).val)) _
    apply (h.1.preimage P.continuous).contDiffOn_iff.mpr
    intro x hx
    exact contDiffAt_matrix_mul (contDiffAt_matrix_mul contDiffAt_const
      ((h.2.2.1.contDiffAt (h.1.mem_nhds hx)).comp x P.contDiff.contDiffAt)) contDiffAt_const

lemma mem_regularRegion_linearCoordinates {u : Coord3 → Fin 2 → ℝ} {A : Coord3 → Symmetric3}
    {U : Set Coord3} (P : Coord3 ≃L[ℝ] Coord3)
    (Q : (Fin 2 → ℝ) ≃L[ℝ] (Fin 2 → ℝ)) {x : Coord3}
    (h : P x∈regularRegion u A U) :
    x∈regularRegion (fun y => Q (u (P y)))
      (fun y => ⟨linearTensorPullback P (fun z => (A z).val) y,
        linearTensorPullback_symmetric P (fun z => (A z).property) y⟩) (P ⁻¹' U) := by
  obtain ⟨O,hOU,hO,hxO⟩ := mem_regularRegion_iff.mp h
  exact mem_regularRegion_iff.mpr ⟨P ⁻¹' O,preimage_mono hOU,hO.linearCoordinates P Q,hxO⟩

end ScalarConductivity

end

end OAI
