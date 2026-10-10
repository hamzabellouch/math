import Mathlib
import OAI.Geometry.TamingCompatibility.DifferentialForms.ComplexEquiv

namespace OAI

section
section
section

section

noncomputable section
namespace TamingCompatibility.MetricForms
open MetricModel MetricHodge
open scoped ContDiff
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
local instance {k : ℕ} : FiniteDimensional ℝ (ContinuousMultilinearMap ℝ (fun _ : Fin k => E) ℝ) :=
  FiniteDimensional.of_injective (ContinuousMultilinearMap.toMultilinearMapLinear (R' := ℝ))
    ContinuousMultilinearMap.toMultilinearMap_injective
local instance {k : ℕ} : FiniteDimensional ℝ (E [⋀^Fin k]→L[ℝ] ℝ) :=
  FiniteDimensional.of_injective ContinuousAlternatingMap.toContinuousMultilinearMapLinear
    ContinuousAlternatingMap.toContinuousMultilinearMap_injective

local instance {k : ℕ} : NormedAddCommGroup (Form E k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
local instance {k : ℕ} : NormedSpace ℝ (Form E k →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

def pairingCLM (g : Metric E) (k : ℕ) : Form E k →L[ℝ] Form E k →L[ℝ] ℝ :=
  (FormMetric.pairingCLM (E := MetricModel.Model g) (k := k)).bilinearComp
    (formEquiv g k).toContinuousLinearMap (formEquiv g k).toContinuousLinearMap
lemma pairingCLM_apply (g : Metric E) (k : ℕ) (a b : Form E k) :
    pairingCLM g k a b = pairing g a b := rfl

lemma pairingCLM_one_smooth {U : Set D} (g : D → Metric E)
    (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → D → E)
    (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    (hb : ∀ x ∈ U, ∀ i j, (g x).bilinear (b i x) (b j x) = if i=j then 1 else 0) :
    ContDiffOn ℝ ∞ (fun x => pairingCLM (g x) 1) U := by
  apply contDiffOn_clm_apply.mpr
  intro a
  apply contDiffOn_clm_apply.mpr
  intro c
  exact SmoothMetric.contDiffOn_pairing_one_frame g hdim b hbs hb contDiffOn_const contDiffOn_const

lemma pairingCLM_two_smooth {U : Set D} (g : D → Metric E)
    (hdim : Module.finrank ℝ E = 4) (b : Fin 4 → D → E)
    (hbs : ∀ i, ContDiffOn ℝ ∞ (b i) U)
    (hb : ∀ x ∈ U, ∀ i j, (g x).bilinear (b i x) (b j x) = if i=j then 1 else 0) :
    ContDiffOn ℝ ∞ (fun x => pairingCLM (g x) 2) U := by
  apply contDiffOn_clm_apply.mpr
  intro a
  apply contDiffOn_clm_apply.mpr
  intro c
  exact SmoothMetric.contDiffOn_pairing_two_frame g hdim b hbs hb contDiffOn_const contDiffOn_const
end TamingCompatibility.MetricForms

end
end

end
end
end

end OAI
