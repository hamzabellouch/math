import Mathlib
import OAI.Analysis.Conductivity.Model

namespace OAI

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

def lpFourJetCLM : (Fin 4 → Lp ℝ 2 μ) →L[ℝ] Lp JetFiber 2 μ :=
  ∑ i : Fin 4, (((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i (1:ℝ))).compLpL 2 μ).comp
    (ContinuousLinearMap.proj i)

lemma lpFourJetCLM_ae (f : Fin 4 → Lp ℝ 2 μ) :
    lpFourJetCLM μ f=ᵐ[μ] (fun x => WithLp.toLp 2 (fun i => f i x)) := by
  have he (i : Fin 4) := (((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i (1:ℝ))).coeFn_compLpL (p:=2) (μ:=μ) (f i))
  simp only [lpFourJetCLM,sum_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
    (fun i : Fin 4 => (((ContinuousLinearMap.id ℝ ℝ).smulRight (EuclideanSpace.single i (1:ℝ))).compLpL 2 μ) (f i)),
    ae_all_iff.mpr he] with x hx hi
  rw [hx]
  simp only [hi,ContinuousLinearMap.smulRight_apply,ContinuousLinearMap.id_apply]
  ext j
  simp [Pi.single_apply]

end ScalarConductivity

end

end OAI
