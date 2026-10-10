import Mathlib
import OAI.Probability.Perceptron.Variational.GlobalContact

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma source_global_contact_density (n k : ℕ) (P : Measure BrownianPath) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (w : Fin (k+1)→ℝ) (q : Fin (k+1)→Time)
    (hw : ∀ i, 0<w i) (hw1 : ∑ i, w i=1) (δ : ℝ) (α : ℝ≥0) (H : ℝ)
    {a : SourceContactParameter n k} (ha : a∈sourceContactCompactDomain n k α H)
    (hmin : IsMinOn (sourceStepContactObjective n k P f p d w q (fun i => (hw i).le) hw1 δ)
      (sourceContactCompactDomain n k α H) a) (ht : 0<a.1) :
    controlValue P f (weightedStepTrial w q (fun i => (hw i).le) hw1)+δ ≤
      sourceDensityIncrement n k f p d a.2.1 (stepCumulative w) a.2.2 a.1 := by
  let V := controlValue P f (weightedStepTrial w q (fun i => (hw i).le) hw1)+δ
  let F : ℝ → ℝ := fun s => -sourceExpectedPressure n k f p d a.2.1 (stepCumulative w)
    s.toNNReal a.2.2+s*V
  have hm : IsMinOn F (Icc 0 (a.1:ℝ)) a.1 := by
    intro s hs
    have hs' : s.toNNReal ≤ α := (Real.toNNReal_le_toNNReal hs.2).trans (by simpa using ha.1.2)
    have he := hmin (show (s.toNNReal,a.2.1,a.2.2)∈sourceContactCompactDomain n k α H from
      ⟨⟨zero_le,hs'⟩,ha.2⟩)
    simp only [mem_ofPred_eq,sourceStepContactObjective,sourceJointPressure] at he
    rw [Real.coe_toNNReal _ hs.1] at he
    change F (a.1:ℝ) ≤ F s
    dsimp [F,V]
    simp only [Real.toNNReal_coe]
    linarith
  have hd : HasDerivAt F (-sourceDensityIncrement n k f p d a.2.1 (stepCumulative w) a.2.2 a.1+V) a.1 := by
    convert
      (sourceExpectedPressure_density_derivative n k f p d a.2.1 (stepCumulative w) a.2.2
      (stepCumulative_strictMono w hw) (stepCumulative_pos w hw) (stepCumulative_lt_one w hw hw1)
      a.1 ht).neg.add ((hasDerivAt_id (a.1:ℝ)).mul_const V) using 1 <;> first | rfl | simp
  have hseg : segment ℝ (a.1:ℝ) 0 ⊆ Icc 0 (a.1:ℝ) := by
    rw [segment_symm,segment_eq_Icc a.1.coe_nonneg]
  have hn := hm.isLocalMinOn.hasFDerivWithinAt_nonneg hd.hasFDerivAt.hasFDerivWithinAt
    (sub_mem_posTangentConeAt_of_segment_subset hseg)
  change 0 ≤ (0-(a.1:ℝ))*(-sourceDensityIncrement n k f p d a.2.1 (stepCumulative w) a.2.2 a.1+V) at hn
  change V ≤ _
  nlinarith [show (0:ℝ)<(a.1:ℝ) from ht]

end SphericalPerceptronFreeEnergy
end

end OAI
