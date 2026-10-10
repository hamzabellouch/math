import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.LineRepresentative
import OAI.Geometry.Borsuk.SphereGeometry.TraceSphere
import OAI.Geometry.Borsuk.Projectors.NegativeQuadratic

namespace OAI

open Set MeasureTheory
namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator
open Set
section RegularPatch
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)
local notation "M" => Matrix (Fin (k+1)) (Fin (k+1)) ℝ
local notation "op" => Matrix.toEuclideanCLM (n := Fin (k+1)) (𝕜 := ℝ)
noncomputable def regularPatch (f : E → ι → ℝ) (I : Finset ι) (w c : E)
    (e : W →ₗᵢ[ℝ] E) (δ : ℝ) : Set (traceSphere (Fin (k+1))) :=
  {A | IsUnit A.val ∧ HasPositiveLine A.val ∧ op A.val⁺ w ≠ 0 ∧
    (∀ i ∈ I, 0 < f (lineRepresentative w A.val) i) ∧
    0 < ⟪c,lineRepresentative w A.val⟫ ∧
    ‖hemisphereInverse c e (lineRepresentative w A.val)‖ < δ ∧
    0 < blockScalar c A.val ∧
    NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A.val))}

end RegularPatch

section RegularPatchContinuity
variable {domainIndices rangeIndices labels : Type*}
  [Fintype domainIndices] [Fintype rangeIndices] [Fintype labels]
  [DecidableEq domainIndices] [DecidableEq rangeIndices]
local notation "E" => EuclideanSpace ℝ rangeIndices
local notation "W" => EuclideanSpace ℝ domainIndices
local notation "op" => Matrix.toEuclideanCLM (n := rangeIndices) (𝕜 := ℝ)

private lemma regularPatch_negative_isOpen (frame : W →ₗᵢ[ℝ] E) :
    IsOpen {point : traceSphere rangeIndices |
      NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress frame point.val))} := by
  have hoperator : Continuous (fun matrix : Matrix domainIndices domainIndices ℝ =>
      Matrix.toEuclideanCLM (𝕜 := ℝ) matrix) :=
    (Matrix.toEuclideanCLM (n := domainIndices) (𝕜 := ℝ)).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  exact negativeQuadratic_isOpen _
    (hoperator.comp ((matrixCompress frame).continuous_of_finiteDimensional.comp continuous_subtype_val))

omit [DecidableEq domainIndices] [DecidableEq rangeIndices] in
private lemma regularPatch_target_isOpen {f : E → labels → ℝ} (hf : Admissible f)
    (indices : Finset labels) (center : E) (frame : W →ₗᵢ[ℝ] E) (radius : ℝ) :
    IsOpen ({vector : E | ∀ index ∈ indices, 0 < f vector index} ∩
      ({vector : E | 0 < ⟪center,vector⟫} ∩
        (fun vector => ‖hemisphereInverse center frame vector‖) ⁻¹' Iio radius)) := by
  have hpos : IsOpen {vector : E | ∀ index ∈ indices, 0 < f vector index} := by
    have he : {vector : E | ∀ index ∈ indices, 0 < f vector index} =
        ⋂ index ∈ indices, {vector : E | 0 < f vector index} := by ext vector; simp
    rw [he]
    exact isOpen_biInter_finset (fun index _ => isOpen_lt continuous_const (hf.smooth index).continuous)
  have hinner : IsOpen {vector : E | 0 < ⟪center,vector⟫} :=
    isOpen_lt continuous_const (continuous_const.inner continuous_id)
  exact hpos.inter ((hemisphereInverse_continuousOn center frame).norm.isOpen_inter_preimage
    hinner (isOpen_Iio : IsOpen (Iio radius)))

private lemma regularPatch_representative_isOpen (vector : E) {target : Set E}
    (htarget : IsOpen target) :
    IsOpen {point : traceSphere rangeIndices | op point.val⁺ vector ≠ 0 ∧
      lineRepresentative vector point.val ∈ target} := by
  have hval : Continuous (fun point : traceSphere rangeIndices => point.val) :=
    continuous_subtype_val
  have hself : ∀ point : traceSphere rangeIndices, IsSelfAdjoint point.val :=
    fun point => point.property.1
  have hmatrix : Continuous (fun matrix : Matrix rangeIndices rangeIndices ℝ => op matrix) :=
    (op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hpositive : Continuous (fun point : traceSphere rangeIndices => point.val⁺) :=
    matrix_posPart_continuousOn.comp_continuous hval hself
  have hoperator : Continuous (fun point : traceSphere rangeIndices => op point.val⁺ vector) :=
    (hmatrix.comp hpositive).clm_apply continuous_const
  exact (lineRepresentative_continuousOn _ hval hself vector).isOpen_inter_preimage
    (isClosed_eq hoperator continuous_const).isOpen_compl htarget

private lemma regularPatch_isOpen_aux {f : E → labels → ℝ} (hf : Admissible f)
    (I : Finset labels) (w c : E) (e : W →ₗᵢ[ℝ] E) (δ : ℝ) :
    IsOpen {A : traceSphere rangeIndices |
      IsUnit A.val ∧ HasPositiveLine A.val ∧ op A.val⁺ w ≠ 0 ∧
      (∀ i ∈ I, 0 < f (lineRepresentative w A.val) i) ∧
      0 < ⟪c,lineRepresentative w A.val⟫ ∧
      ‖hemisphereInverse c e (lineRepresentative w A.val)‖ < δ ∧
      0 < blockScalar c A.val ∧
      NegativeQuadratic (Matrix.toEuclideanCLM (𝕜 := ℝ) (matrixCompress e A.val))} := by
  let T := traceSphere rangeIndices
  have hA : Continuous (fun A : T => A.val) := continuous_subtype_val
  have hSA : ∀ A : T, IsSelfAdjoint A.val := fun A => A.property.1
  have hpre := regularPatch_representative_isOpen w (regularPatch_target_isOpen hf I c e δ)
  have hscalar : IsOpen {A : T | 0 < blockScalar c A.val} :=
    isOpen_lt continuous_const ((blockScalar_continuous c).comp hA)
  have hneg := regularPatch_negative_isOpen e
  apply isOpen_iff_mem_nhds.mpr
  rintro point ⟨hunit,hline,hvector,hlabels,hinner,hnorm,hblock,hquadratic⟩
  filter_upwards [(positive_line_isOpen _ hA hSA).mem_nhds ⟨hunit,hline⟩,
    hpre.mem_nhds ⟨hvector,hlabels,hinner,hnorm⟩,
    hscalar.mem_nhds hblock, hneg.mem_nhds hquadratic]
    with nearby hpositive hrepresentative hscalar hnegative
  exact ⟨hpositive.1,hpositive.2,hrepresentative.1,hrepresentative.2.1,
    hrepresentative.2.2.1,hrepresentative.2.2.2,hscalar,hnegative⟩
end RegularPatchContinuity

section RegularPatch
variable {k : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
local notation "E" => EuclideanSpace ℝ (Fin (k+1))
local notation "W" => EuclideanSpace ℝ (Fin k)

omit [DecidableEq ι] in
lemma Admissible.regularPatch_isOpen {f : E → ι → ℝ} (hf : Admissible f)
    (I : Finset ι) (w c : E) (e : W →ₗᵢ[ℝ] E) (δ : ℝ) : IsOpen (regularPatch f I w c e δ) :=
  regularPatch_isOpen_aux hf I w c e δ
end RegularPatch
end BorsukNine

end OAI
