import Mathlib
import OAI.Geometry.Borsuk.MatrixGeometry.SpectralChart

namespace OAI

namespace BorsukNine
open scoped RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
section LineRepresentative
variable {ν : Type*} [Fintype ν] [DecidableEq ν] [Nonempty ν]
local notation "E" => EuclideanSpace ℝ ν
local notation "M" => Matrix ν ν ℝ
local notation "op" => Matrix.toEuclideanCLM (n := ν) (𝕜 := ℝ)

omit [Fintype ν] [DecidableEq ν] [Nonempty ν] in
lemma rankOne_smul (t : ℝ) (u : E) : rankOne (t • u) = t^2 • rankOne u := by
  ext i j
  simp only [rankOne,PiLp.smul_apply,Matrix.smul_apply,smul_eq_mul]
  ring

omit [DecidableEq ν] [Nonempty ν] in
lemma rankOne_unit_span {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1)
    (hsp : v ∈ Submodule.span ℝ {u}) : rankOne v = rankOne u := by
  obtain ⟨t,ht⟩ := Submodule.mem_span_singleton.mp hsp
  change t • u = v at ht
  have hn : |t| = 1 := by simpa only [← ht,norm_smul,Real.norm_eq_abs,hu,mul_one] using hv
  have hs : t^2 = 1 := by nlinarith [sq_abs t]
  rw [← ht,rankOne_smul,hs,one_smul]

noncomputable def lineRepresentative (w : E) (A : M) : E :=
  ‖op A⁺ w‖⁻¹ • op A⁺ w

def HasPositiveLine (A : M) : Prop :=
  ∃ u : E, ‖u‖ = 1 ∧ ∃ lam : ℝ, 0 < lam ∧ A⁺ = lam • rankOne u

omit [Nonempty ν] in
lemma lineRepresentative_norm {w : E} {A : M} (hAw : op A⁺ w ≠ 0) :
    ‖lineRepresentative w A‖ = 1 := by
  simp [lineRepresentative,norm_smul,norm_inv,hAw]

omit [Nonempty ν] in
lemma hasPositiveLine_trace_pos {A : M} (hA : HasPositiveLine A) :
    0 < Matrix.trace A⁺ := by
  obtain ⟨u,hu,lam,hl,he⟩ := hA
  rwa [he,Matrix.trace_smul,rankOne_trace,hu,one_pow,smul_eq_mul,mul_one]

omit [Nonempty ν] in
lemma positive_line_representative {w : E} {A : M} (hA : HasPositiveLine A)
    (hAw : op A⁺ w ≠ 0) : A⁺ = Matrix.trace A⁺ • rankOne (lineRepresentative w A) := by
  obtain ⟨u,hu,lam,hl,he⟩ := hA
  have hsp : lineRepresentative w A ∈ Submodule.span ℝ {u} := by
    rw [lineRepresentative,he,map_smul,smul_apply,rankOne_action]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _
      (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))))
  have hp := rankOne_unit_span hu (lineRepresentative_norm hAw) hsp
  rw [hp,he,Matrix.trace_smul,rankOne_trace,hu,one_pow,smul_eq_mul,mul_one]

omit [Nonempty ν] in
lemma lineRepresentative_inner_pos {w : E} {A : M} (hA : HasPositiveLine A)
    (hAw : op A⁺ w ≠ 0) : 0 < ⟪w,lineRepresentative w A⟫ := by
  obtain ⟨u,hu,lam,hl,he⟩ := hA
  have hi : ⟪u,w⟫ ≠ 0 := by
    intro hz
    apply hAw
    rw [he,map_smul,smul_apply,rankOne_action,hz,zero_smul,smul_zero]
  have hp : 0 < ⟪w,op A⁺ w⟫ := by
    rw [he,map_smul,smul_apply,rankOne_action,inner_smul_right,
      inner_smul_right,real_inner_comm w u]
    exact mul_pos hl (mul_self_pos.mpr (by simpa only [real_inner_comm] using hi))
  rw [lineRepresentative,inner_smul_right]
  exact mul_pos (inv_pos.mpr (norm_pos_iff.mpr hAw)) hp

omit [Nonempty ν] in
lemma lineRepresentative_continuousOn {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) (w : E) :
    ContinuousOn (fun x => lineRepresentative w (A x)) {x | op (A x)⁺ w ≠ 0} := by
  have hop : Continuous (fun B : M => op B) :=
    (op).toAlgEquiv.toLinearEquiv.toLinearMap.continuous_of_finiteDimensional
  have hP : Continuous (fun x => (A x)⁺) :=
    matrix_posPart_continuousOn.comp_continuous hA hSA
  have hv : Continuous (fun x => op (A x)⁺ w) := (hop.comp hP).clm_apply continuous_const
  exact (hv.norm.continuousOn.inv₀ (fun _ hx => norm_ne_zero_iff.mpr hx)).smul hv.continuousOn

omit [Nonempty ν] in
lemma positive_line_isOpen {X : Type*} [TopologicalSpace X]
    (A : X → M) (hA : Continuous A) (hSA : ∀ x, IsSelfAdjoint (A x)) :
    IsOpen {x | IsUnit (A x) ∧ HasPositiveLine (A x)} := by
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨u,hu,lam,hl,he⟩ := hx.2
  exact positive_line_eventually A hA hSA hx.1 hu hl he

lemma unit_rankOne_inner_nonzero {A : M} (_hA : HasPositiveLine A) {w u : E}
    (hu : ‖u‖ = 1) {lam : ℝ} (hl : 0 < lam) (he : A⁺ = lam • rankOne u)
    (hwu : ⟪w,u⟫ ≠ 0) : op A⁺ w ≠ 0 := by
  rw [he,map_smul,smul_apply,rankOne_action]
  apply smul_ne_zero (ne_of_gt hl)
  apply smul_ne_zero (by simpa only [real_inner_comm] using hwu)
  intro hz
  simp [hz] at hu

end LineRepresentative
end BorsukNine

end OAI
