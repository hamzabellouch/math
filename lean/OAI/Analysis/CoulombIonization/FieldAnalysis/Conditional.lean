import Mathlib
import OAI.Analysis.CoulombIonization.RadialBounds.BarrierForgettingBarrier

namespace OAI

noncomputable section

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
open Set Filter MeasureTheory Laplacian Metric ProbabilityTheory
open scoped Topology BigOperators
namespace CoulombBarrier
open CoulombAnalysis CoulombPDE CoulombAtom
variable {Ω D : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
variable [MeasurableSpace D] (P : Measure Ω) [IsProbabilityMeasure P]
variable (X : Ω → D) (hX : Measurable X)

def conditionalField (u : Ω → TFSpace → ℝ) (d : D) (x : TFSpace) : ℝ :=
  ∫ sample, u sample x ∂condDistrib id X P d

lemma conditionalField_measurable {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) :
    Measurable (Function.uncurry (conditionalField P X u)) := by
  have hm : StronglyMeasurable (fun p : (D × TFSpace) × Ω => u p.2 p.1.2) :=
    (hu.comp (measurable_snd.prodMk measurable_fst.snd)).stronglyMeasurable
  exact (hm.integral_kernel_prod_right'
    (κ := (condDistrib id X P).comap Prod.fst measurable_fst)).measurable

lemma conditionalField_bound {u : Ω → TFSpace → ℝ} (hb : DeterministicLocalBound u) :
    DeterministicLocalBound (conditionalField P X u) := by
  intro K hK
  obtain ⟨C,hC⟩ := hb K hK
  refine ⟨C,fun d x hx => ?_⟩
  calc
    _ ≤ ∫ _ : Ω, C ∂condDistrib id X P d := norm_integral_le_of_norm_le (integrable_const C)
      (Eventually.of_forall fun sample => hC sample x hx)
    _ = C := by simp

include hX

lemma conditionalField_continuous {u : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hb : DeterministicLocalBound u)
    (hc : ∀ᵐ sample ∂P, Continuous (u sample)) :
    ∀ᵐ d ∂P.map X, Continuous (conditionalField P X u d) := by
  filter_upwards [conditional_all_properties P hX hc] with d hd
  exact average_continuous hu hb hd

theorem weak_nuclear_conditional {U : Set TFSpace} (Z : ℝ)
    {u g : Ω → TFSpace → ℝ}
    (hu : Measurable (Function.uncurry u)) (hub : DeterministicLocalBound u)
    (huc : ∀ᵐ sample ∂P, Continuous (u sample))
    (hg : Measurable (Function.uncurry g)) (hgb : DeterministicLocalBound g)
    {χ : TFSpace → ℝ} (hχ : Measurable χ) (hχb : ∀ x, ‖χ x‖ ≤ 1) (hχn : ∀ x, 0 ≤ χ x)
    {R k : ℝ} (hR : 0 < R) (hk : 0 ≤ k) (hzero : ∀ x, ‖x‖ < R → χ x = 0)
    (hw : ∀ᵐ sample ∂P, WeakNuclearLowerOn U Z (fun x => nuclearField Z x+u sample x)
      (fun x => g sample x+χ x*reaction k (nuclearField Z x+u sample x))) :
    ∀ᵐ d ∂P.map X, WeakNuclearLowerOn U Z
      (fun x => nuclearField Z x+conditionalField P X u d x)
      (fun x => conditionalField P X g d x+
        χ x*reaction k (nuclearField Z x+conditionalField P X u d x)) := by
  filter_upwards [conditional_all_properties P hX huc,conditional_all_properties P hX hw] with d hc hw
  exact weak_nuclear_average Z hu hub hc hg hgb hχ hχb hχn hR hk hzero hw

end CoulombBarrier

end

end OAI
