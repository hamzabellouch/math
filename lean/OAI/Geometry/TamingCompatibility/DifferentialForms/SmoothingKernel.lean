import Mathlib

namespace OAI


noncomputable section
namespace TamingCompatibility.HilbertKernel
open MeasureTheory
open scoped RealInnerProductSpace
variable {H F G A B : Type*}
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

def kernel (E : A → H →L[ℝ] F) (D : B → H →L[ℝ] G) (x : A) (y : B) : G →L[ℝ] F :=
  (E x).comp (D y).adjoint

lemma kernel_inner (E : A → H →L[ℝ] F) (D : B → H →L[ℝ] G)
    (x : A) (y : B) (a : F) (b : G) :
    ⟪a,kernel E D x y b⟫ = ⟪(E x).adjoint a,(D y).adjoint b⟫ := by
  exact (ContinuousLinearMap.adjoint_inner_left (E x) ((D y).adjoint b) a).symm

lemma kernel_adjoint (E : A → H →L[ℝ] F) (D : B → H →L[ℝ] G)
    (x : A) (y : B) : (kernel E D x y).adjoint = kernel D E y x := by
  simp only [kernel,ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

omit [CompleteSpace F] in
lemma kernel_norm_le (E : A → H →L[ℝ] F) (D : B → H →L[ℝ] G) (x : A) (y : B) :
    ‖kernel E D x y‖ ≤ ‖E x‖*‖D y‖ := by
  simpa only [kernel,LinearIsometryEquiv.norm_map] using (E x).opNorm_comp_le (D y).adjoint

omit [CompleteSpace F] in
lemma kernel_continuous [TopologicalSpace A] [TopologicalSpace B]
    {E : A → H →L[ℝ] F} {D : B → H →L[ℝ] G} (hE : Continuous E) (hD : Continuous D) :
    Continuous (fun p : A × B => kernel E D p.1 p.2) :=
  (hE.comp continuous_fst).clm_comp
    ((ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := H) (F := G)).continuous.comp
      (hD.comp continuous_snd))

def regularize [MeasurableSpace A] (μ : Measure A)
    (E : A → H →L[ℝ] F) (v : A → F) : H := ∫ x, (E x).adjoint (v x) ∂μ

lemma regularize_pair [MeasurableSpace A] (μ : Measure A)
    (E : A → H →L[ℝ] F) (v : A → F)
    (hv : Integrable (fun x => (E x).adjoint (v x)) μ) (f : H) :
    ⟪regularize μ E v,f⟫ = ∫ x, ⟪v x,E x f⟫ ∂μ := by
  have h := (innerSL ℝ f).integral_comp_comm hv
  simp only [innerSL_apply_apply] at h
  rw [regularize,real_inner_comm,← h]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [real_inner_comm,ContinuousLinearMap.adjoint_inner_left]

lemma regularize_kernel_pair [MeasurableSpace A] [MeasurableSpace B]
    (μ : Measure A) (ν : Measure B) (E : A → H →L[ℝ] F) (D : B → H →L[ℝ] G)
    (v : A → F) (w : B → G)
    (hv : Integrable (fun x => (E x).adjoint (v x)) μ)
    (hw : Integrable (fun y => (D y).adjoint (w y)) ν) :
    ⟪regularize μ E v,regularize ν D w⟫ =
      ∫ x, ∫ y, ⟪v x,kernel E D x y (w y)⟫ ∂ν ∂μ := by
  rw [regularize_pair μ E v hv]
  apply integral_congr_ae
  filter_upwards [] with x
  have h := ((innerSL ℝ (v x)).comp (E x)).integral_comp_comm hw
  simpa only [regularize,ContinuousLinearMap.comp_apply,innerSL_apply_apply,kernel] using h.symm

lemma regularize_norm_sq [MeasurableSpace A] (μ : Measure A)
    (E : A → H →L[ℝ] F) (v : A → F)
    (hv : Integrable (fun x => (E x).adjoint (v x)) μ) :
    ‖regularize μ E v‖^2 = ∫ x, ∫ y, ⟪v x,kernel E E x y (v y)⟫ ∂μ ∂μ := by
  rw [← real_inner_self_eq_norm_sq,regularize_kernel_pair μ μ E E v v hv hv]
end TamingCompatibility.HilbertKernel

end

end OAI
