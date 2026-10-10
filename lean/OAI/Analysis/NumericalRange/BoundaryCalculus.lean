import OAI.Analysis.NumericalRange.DomainCalculus

namespace OAI

universe u_245 u_246

section
noncomputable section
open Set Filter Metric Complex MeasureTheory
open scoped Topology ComplexConjugate ComplexOrder MatrixOrder Matrix.Norms.L2Operator Kronecker
namespace CompleteCrouzeix
namespace AdmissibleDomain
variable (D : AdmissibleDomain)
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩
def kernel : AnalyticBidiskKernel := actualExteriorKernel D.exterior.radius_gt
  D.exterior.leading_ne D.exterior.analytic_regular D.exterior.injective
  D.exterior.noncritical D.support_circle
lemma outside_imp (t : ℂ) (ht : D.exterior.radius⁻¹ < ‖t‖) (hz : D.G t ∈ D.domain) :
    t ∈ ball (0:ℂ) 1 := (D.exterior.interior_iff t ht).mp hz
lemma inner_maps : MapsTo D.G ({t | D.exterior.radius⁻¹ < ‖t‖} ∩ ball 0 1) (closure D.domain) := by
  intro t ht
  exact subset_closure ((D.exterior.interior_iff t ht.1).mpr ht.2)
variable {n : Type u_245} {m : Type u_246} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
def cauchy : MatrixCircleL2 (m := m) →L[ℂ] MatrixCircleL2 (m := m) := matrixFourier.cauchy D.kernel.matrixM
def trace (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    C(UnitAddCircle,Matrix m m ℂ) :=
  ⟨fun t => v (D.G t.toCircle), (hv.comp D.G_analytic (fun _ ht => (D.G_boundary ht).1)).continuousOn.comp_continuous
    (continuous_subtype_val.comp AddCircle.continuous_toCircle) (fun t => t.toCircle.property)⟩
lemma fourier_cauchy (ij : m × m) (k : ℤ) :
    ∃ (v : ℂ → Matrix m m ℂ) (hv : AnalyticOnNhd ℂ v (closure D.domain)),
      D.cauchy (hsTraceLp (matrixFourierTrace ij k)) = hsTraceLp (D.trace v hv) ∧
      ∀ z ∈ D.domain, ∀ i j, v z i j =
        ∫ t : UnitAddCircle, ((t.toCircle : ℂ)*deriv D.G (t.toCircle : ℂ)) *
          matrixFourierTrace ij k t i j / (D.G t.toCircle-z) ∂AddCircle.haarAddCircle := by
  obtain ⟨v,hv,hvp,hvt⟩ := actualExteriorCauchy_fourier_trace D.exterior.radius_gt
    D.exterior.leading_ne D.exterior.analytic_regular D.exterior.injective
    D.exterior.noncritical D.support_circle D.isOpen D.exterior.boundary_image D.outside_imp k
  let V : ℂ → Matrix m m ℂ := fun z => Matrix.single ij.1 ij.2 (v z)
  have hV : AnalyticOnNhd ℂ V (closure D.domain) := by
    intro z hz
    convert (hv z hz).smul (analyticAt_const : AnalyticAt ℂ
      (fun _ : ℂ => Matrix.single ij.1 ij.2 (1:ℂ)) z) using 1
    ext w i j
    change (if ij.1 = i ∧ ij.2 = j then v w else 0) =
      v w * (if ij.1 = i ∧ ij.2 = j then 1 else 0)
    split_ifs <;> simp
  refine ⟨V,hV,?_,?_⟩
  · rw [cauchy,hsTraceLp_matrixFourierTrace,matrixCauchy_eq_entrywise,entrywise_embedding]
    apply Lp.ext
    filter_upwards [l2Embedding_ae ij (scalarFourier.cauchy D.kernel.scalarM (fourierLp 2 k)),
      hvt,hsTraceLp_ae (D.trace V hV)] with t he ht hvv
    change (scalarFourier.cauchy D.kernel.scalarM (fourierLp 2 k)) t = v (D.G t.toCircle) at ht
    rw [he,ht,hvv]
    apply PiLp.ext
    rintro ⟨i,j⟩
    simp only [PiLp.single_apply,toHS,trace,ContinuousMap.coe_mk,V,Matrix.single_apply]
    rcases ij with ⟨i',j'⟩
    simp only [Prod.mk.injEq,eq_comm]
  · intro z hz i j
    simp only [V,Matrix.single_apply,matrixFourierTrace,ContinuousMap.coe_mk]
    split_ifs with hij
    · rw [hvp hz]
      refine integral_congr_ae (ae_of_all _ fun point => ?_)
      dsimp [physicalCauchy,G]
      ring
    · simp

def resolventField (A : Matrix n n ℂ) (t : UnitAddCircle) : Matrix n n ℂ :=
  ((t.toCircle : ℂ)*deriv D.G (t.toCircle : ℂ)) •
    (D.G t.toCircle • (1:Matrix n n ℂ)-A)⁻¹
lemma curve_continuous : Continuous (fun t : UnitAddCircle => D.G t.toCircle) :=
  D.G_analytic.continuousOn.comp_continuous
    (continuous_subtype_val.comp AddCircle.continuous_toCircle) (fun t => t.toCircle.property)
lemma normal_continuous : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)*deriv D.G t.toCircle) :=
  (continuous_subtype_val.comp AddCircle.continuous_toCircle).mul
    (D.G_analytic.deriv.continuousOn.comp_continuous
      (continuous_subtype_val.comp AddCircle.continuous_toCircle) (fun t => t.toCircle.property))
lemma resolvent_continuous (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain) :
    Continuous (D.resolventField A) :=
  D.normal_continuous.smul (matrix_resolvent_continuous A D.curve_continuous
    (fun t hz => D.G_ne_interior (hA hz) (by simp [Circle.norm_coe]) rfl))
lemma fourier_resolvent_eval (A : Matrix n n ℂ) (hA : spectrum ℂ A ⊆ D.domain)
    (ij : m × m) (k : ℤ) {v : ℂ → Matrix m m ℂ}
    (he : ∀ z ∈ D.domain, ∀ i j, v z i j =
      ∫ t : UnitAddCircle, ((t.toCircle : ℂ)*deriv D.G (t.toCircle : ℂ)) *
        matrixFourierTrace ij k t i j / (D.G t.toCircle-z) ∂AddCircle.haarAddCircle) :
    completeAnalyticEval A v = ∫ t : UnitAddCircle,
      D.resolventField A t ⊗ₖ matrixFourierTrace ij k t ∂AddCircle.haarAddCircle := by
  unfold resolventField
  rw [← complete_cauchy_integral_evaluation (μ := AddCircle.haarAddCircle) A D.curve_continuous D.normal_continuous
    (matrixFourierTrace ij k).continuous D.isOpen hA
    (fun z hz t => D.G_ne_interior hz (by simp [Circle.norm_coe]))]
  apply completeAnalyticEval_eqOn A D.isOpen hA
  intro z hz
  ext i j
  exact he z hz i j
lemma positive_representation [Nonempty n] (A : Matrix n n ℂ)
    (hA : spectrum ℂ A ⊆ D.domain) {v : ℂ → Matrix m m ℂ}
    (hv : AnalyticOnNhd ℂ v (closure D.domain)) :
    completeAnalyticEval A v = ∫ t : UnitAddCircle,
      pulledDiskDensity (matrixAnalyticEval A D.interior.toDisk) D.ψ t ⊗ₖ
        D.trace v hv t ∂AddCircle.haarAddCircle := by
  have hf (z : ℂ) (hz : z ∈ spectrum ℂ A) :=
    D.interior.analytic_to z (D.interior.closure_subset (subset_closure (hA hz)))
  apply interior_coordinate_exterior_representation A D.isOpen hA hf
    (fun z hz => ball_subset_closedBall (D.toDisk_maps (hA hz)))
    (D.interior.analytic_from.mono D.interior.closedDisk_subset)
    (fun z hz => D.interior.left_inverse z (D.interior.closure_subset (subset_closure hz)))
    (hv.mono (by rintro z ⟨w,hw,rfl⟩; exact D.interior.inverse_closed w hw))
    (matrixAnalyticEval_stable A hf (fun z hz => mem_ball_zero_iff.mp (D.toDisk_maps (hA hz))))
    D.ψ_analytic (fun _ ht => D.ψ_boundary ht) (fun _ ht => D.inverse_ψ ht) (fun _ hz => D.ψ_mass hz)
end AdmissibleDomain
end CompleteCrouzeix

end

end

end OAI
