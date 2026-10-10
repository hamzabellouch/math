import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.LineRepresentative
import OAI.Geometry.Borsuk.SphereGeometry.TraceSphere
import OAI.Geometry.Borsuk.MatrixGeometry.MatrixFibre

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
section NegativeFibre
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

lemma negPart_kernel_of_positiveLine {A : M} {u : E} (hu : ‖u‖ = 1)
    {lam : ℝ} (hl : 0 < lam) (he : A⁺ = lam • rankOne u) : op A⁻ u = 0 := by
  have hz : op A⁻ (op A⁺ u) = 0 := by
    have h := congrArg (fun B : M => op B u) (CFC.negPart_mul_posPart A)
    simpa only [map_mul,map_zero,mul_apply_eq_comp,zero_apply] using h
  rw [he,map_smul,smul_apply,rankOne_action,real_inner_self_eq_norm_sq,
    hu,one_pow,one_smul,map_smul] at hz
  exact (smul_eq_zero.mp hz).resolve_left (ne_of_gt hl)

noncomputable def negativeFibre (A : M) : M := (Matrix.trace A⁻)⁻¹ • A⁻

lemma negativeFibre_mem {A : M} (hA : HasPositiveLine A) {w : E}
    (hAw : op A⁺ w ≠ 0) (hm : 0 < Matrix.trace A⁻) :
    negativeFibre A ∈ matrixFibre (lineRepresentative w A) := by
  have hu := lineRepresentative_norm hAw
  have hl := hasPositiveLine_trace_pos hA
  have he := positive_line_representative hA hAw
  refine ⟨smul_nonneg (inv_nonneg.mpr hm.le) (CFC.negPart_nonneg A),?_,?_⟩
  · rw [negativeFibre,Matrix.trace_smul,smul_eq_mul,inv_mul_cancel₀ (ne_of_gt hm)]
  · rw [negativeFibre,map_smul,smul_apply,
      negPart_kernel_of_positiveLine hu hl he,smul_zero]

omit [Nonempty ν] in
lemma negativeFibre_smul {A : M} (hm : Matrix.trace A⁻ ≠ 0) :
    Matrix.trace A⁻ • negativeFibre A = A⁻ := by
  rw [negativeFibre,smul_smul,mul_inv_cancel₀ hm,one_smul]

omit [Nonempty ν] in
lemma negativeFibre_splitting {A : M} (hSA : IsSelfAdjoint A) (hA : HasPositiveLine A)
    {w : E} (hAw : op A⁺ w ≠ 0) (hm : 0 < Matrix.trace A⁻) :
    A = Matrix.trace A⁺ • rankOne (lineRepresentative w A) - Matrix.trace A⁻ • negativeFibre A := by
  rw [negativeFibre_smul (ne_of_gt hm),← positive_line_representative hA hAw,
    CFC.posPart_sub_negPart A hSA]

omit [Nonempty ν] in
lemma negativeFibre_continuousOn {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) :
    ContinuousOn (fun x => negativeFibre (A x)) {x | Matrix.trace (A x)⁻ ≠ 0} := by
  have hP : Continuous (fun x => (A x)⁻) :=
    matrix_negPart_continuousOn.comp_continuous hA hSA
  exact ((matrix_trace_continuous.comp hP).continuousOn.inv₀ (fun _ hx => hx)).smul hP.continuousOn

omit [Nonempty ν] in
lemma fibre_unit_of_split_unit {u : E} {Q : M} (hQ : 0 ≤ Q)
    (_hQu : op Q u = 0) {lam mu : ℝ} (_hl : 0 < lam) (_hm : 0 < mu)
    (hA : IsUnit (lam • rankOne u - mu • Q)) : IsUnit (rankOne u + Q) := by
  by_contra hn
  obtain ⟨v,hv,huv,hQv⟩ := fibre_boundary_kernel hQ u hn
  have hzero : op (lam • rankOne u - mu • Q) v = 0 := by
    simp only [map_sub,map_smul,sub_apply,smul_apply,
      rankOne_action,huv,zero_smul,hQv,smul_zero,sub_self]
  have huA : IsUnit (op (lam • rankOne u - mu • Q)) := hA.map (op).toMonoidHom
  have hinj := ContinuousLinearMap.isUnit_iff_bijective.mp huA
  have hv0 : v = 0 := hinj.1 (by simpa only [map_zero] using hzero)
  simp [hv0] at hv

end NegativeFibre
end BorsukNine

end OAI
