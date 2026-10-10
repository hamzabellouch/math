import OAI.Analysis.TriangularHilbert.JointInsert

namespace OAI

universe uι uE

section
namespace TriangularHilbert.Heat
open MatrixEnergy MeasureTheory
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator ComplexOrder Topology
noncomputable section
variable {ι : Type uι} [Fintype ι] [DecidableEq ι]

lemma measurable_heatPure_param {E : Type uE} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v w : Three) :
    Measurable (fun t => heatPure A h u (p t) (σ t) v w) := by
  have hc : Continuous (fun q : E × ℝ => heatFirst A h u (Function.update (p q.1) w q.2) (σ q.1) v w) :=
    continuous_heatFirst_param A hh u (by fun_prop) (hσ.comp continuous_fst) (fun q a => hpos q.1 a) v w
  have hm := (measurable_deriv_with_param
    (f := fun t q => heatFirst A h u (Function.update (p t) w q) (σ t) v w) hc).comp
    (show Measurable (fun t : E => (t,p t w)) from measurable_id.prodMk (((continuous_apply w).comp hp).measurable))
  convert! hm using 1
  funext t
  exact (heatFirst_hasDerivAt_center A hh u (p t) (hpos t) v w).deriv.symm

lemma measurable_heatCost_param {E : Type uE} [TopologicalSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (A : Three → Matrix ι ι ℂ) {h : ℝ} (hh : 0 < h) (u : ι → ℝ)
    {p σ : E → Three → ℝ} (hp : Continuous p) (hσ : Continuous σ)
    (hpos : ∀ t w, 0 < σ t w) (v w : Three) :
    Measurable (fun t => heatCost A h u (p t) (σ t) v w) := by
  have hm := (measurable_heatPure_param A hh u hp hσ hpos v w).sub
    (continuous_heatSecondGradient_param A hh u hp hσ hpos v w).measurable
  convert! hm using 1
  funext t
  simp [heatPure,heatCost]
end
end TriangularHilbert.Heat
end

end OAI
