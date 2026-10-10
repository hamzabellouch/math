import OAI.MathematicalPhysics.NavierStokes.ShearFlows.Differential

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators ContDiff Topology

namespace ShearFlows
theorem transverseSum_project_zero {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Space →L[ℝ] E) (f : ι → E → ℝ) (v : ι → Space)
    (hv : ∀ i, P (v i) = 0) (x : Space) :
    P (transverseSum P f v x) = 0 := by
  simp [transverseSum, map_sum, hv]

theorem transverseSum_invariant {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Space →L[ℝ] E) (f : ι → E → ℝ) (v : ι → Space)
    (hv : ∀ i, P (v i) = 0) (x : Space) (a : ℝ) :
    transverseSum P f v (x + a • transverseSum P f v x) = transverseSum P f v x := by
  have hp : P (x + a • transverseSum P f v x) = P x := by
    simp [transverseSum_project_zero P f v hv]
  change (∑ i, f i (P (x + a • transverseSum P f v x)) • v i) = _
  rw [hp]
  rfl

def accumulatedFlow (W : Space → Space) (θ : ℝ → ℝ) (t : ℝ) (a : Space) : Space :=
  a + (θ t - θ 0) • W a

theorem accumulatedFlow_initial (W : Space → Space) (θ : ℝ → ℝ) (a : Space) :
    accumulatedFlow W θ 0 a = a := by simp [accumulatedFlow]

theorem accumulatedFlow_ode {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Space →L[ℝ] E) (f : ι → E → ℝ) (v : ι → Space)
    (hv : ∀ i, P (v i) = 0) {θ b : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (b t) t) (a : Space) (t : ℝ) :
    HasDerivAt (fun s => accumulatedFlow (transverseSum P f v) θ s a)
      (b t • transverseSum P f v (accumulatedFlow (transverseSum P f v) θ t a)) t := by
  simpa only [accumulatedFlow, transverseSum_invariant P f v hv] using
    (((hθ t).sub_const (θ 0)).smul_const (transverseSum P f v a)).const_add a

theorem accumulatedFlow_unique {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (P : Space →L[ℝ] E) (f : ι → E → ℝ) (v : ι → Space)
    (hv : ∀ i, P (v i) = 0) {θ b : ℝ → ℝ}
    (hθ : ∀ t, HasDerivAt θ (b t) t) (a : Space) (γ : ℝ → Space)
    (h₀ : γ 0 = a)
    (hγ : ∀ t, HasDerivAt γ (b t • transverseSum P f v (γ t)) t) :
    ∀ t, γ t = accumulatedFlow (transverseSum P f v) θ t a := by
  have hproj (t : ℝ) : HasDerivAt (P ∘ γ) 0 t := by
    simpa only [map_smul, transverseSum_project_zero P f v hv, smul_zero] using
      P.hasFDerivAt.comp_hasDerivAt t (hγ t)
  have hconst (t : ℝ) : P (γ t) = P a := by
    simpa only [Function.comp_apply, h₀] using
      is_const_of_deriv_eq_zero (fun s => (hproj s).differentiableAt)
        (fun s => (hproj s).deriv) t 0
  have hW (t : ℝ) : transverseSum P f v (γ t) = transverseSum P f v a := by
    simp only [transverseSum, hconst]
  have hd (t : ℝ) :
      HasDerivAt (fun s => γ s - accumulatedFlow (transverseSum P f v) θ s a) 0 t := by
    simpa only [Pi.sub_apply, hW, accumulatedFlow, transverseSum_invariant P f v hv, sub_self] using
      (hγ t).fun_sub (accumulatedFlow_ode P f v hv hθ a t)
  intro t
  have heq := is_const_of_deriv_eq_zero (fun s => (hd s).differentiableAt)
    (fun s => (hd s).deriv) t 0
  simpa only [accumulatedFlow_initial, h₀, sub_self, sub_eq_zero] using heq

end ShearFlows

end

end OAI
