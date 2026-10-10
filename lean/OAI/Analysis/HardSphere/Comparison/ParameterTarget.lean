import Mathlib
import OAI.Analysis.HardSphere.Bridges.LocalReference

namespace OAI

section

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace HardSphere.Comparison
open HardSphere.Bridge HardSphere.Wiener HardSphere.GaussianPacking
variable {E : Type*} [MeasurableSpace E]

def parameterTargetKernel {B : Set Point} (hB : volume B ≠ ⊤)
    (A : Set (E×Point)) (hA : MeasurableSet A) : Kernel E Point := by
  letI : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hB.lt_top⟩
  exact parameterSuccessKernel (Kernel.const E (volume.restrict B)) A hA

lemma parameterTargetKernel_apply {B : Set Point} (hB : volume B ≠ ⊤)
    (A : Set (E×Point)) (hA : MeasurableSet A)
    (hAB : ∀e,Prod.mk e ⁻¹' A ⊆ B) (e : E) :
    parameterTargetKernel hB A hA e=targetUniform (Prod.mk e ⁻¹' A) := by
  let : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hB.lt_top⟩
  have hs := hA.preimage (@measurable_prodMk_left E Point _ _ e)
  change ((volume.restrict B) (Prod.mk e ⁻¹' A))⁻¹ •
    (volume.restrict B).restrict (Prod.mk e ⁻¹' A)=_
  rw [Measure.restrict_apply hs,inter_eq_left.mpr (hAB e),
    Measure.restrict_restrict hs,inter_eq_left.mpr (hAB e)]
  rfl

instance parameterTargetKernel_finite {B : Set Point} (hB : volume B ≠ ⊤)
    (A : Set (E×Point)) (hA : MeasurableSet A) :
    IsFiniteKernel (parameterTargetKernel hB A hA) := by
  let : IsFiniteMeasure (volume.restrict B) := ⟨by simpa using hB.lt_top⟩
  exact inferInstanceAs (IsFiniteKernel (parameterSuccessKernel (Kernel.const E (volume.restrict B)) A hA))

lemma parameterTargetKernel_markov {B : Set Point} (hB : volume B ≠ ⊤)
    (A : Set (E×Point)) (hA : MeasurableSet A)
    (hAB : ∀e,Prod.mk e ⁻¹' A ⊆ B)
    (hpos : ∀e,0 < volume (Prod.mk e ⁻¹' A)) :
    IsMarkovKernel (parameterTargetKernel hB A hA) := by
  constructor
  intro e
  rw [parameterTargetKernel_apply hB A hA hAB e]
  exact targetUniform_probability (hpos e).ne'
    (ne_top_of_le_ne_top hB (measure_mono (hAB e)))

end HardSphere.Comparison

end
end

section
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal Topology
namespace HardSphere.Comparison
variable {E U X Y : Type*} [MeasurableSpace E] [MeasurableSpace U]
  [MeasurableSpace X] [MeasurableSpace Y]

lemma probability_inter_98 (μ : Measure U) [IsProbabilityMeasure μ]
    {s t : Set U} (_hs : MeasurableSet s) (ht : MeasurableSet t)
    (hsm : ENNReal.ofReal (99/100:ℝ)≤μ s) (htm : ENNReal.ofReal (99/100:ℝ)≤μ t) :
    ENNReal.ofReal (49/50:ℝ)≤μ (s∩t) := by
  have he := congrArg ENNReal.toReal (measure_union_add_inter (μ:=μ) s ht)
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _),
    ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at he
  have hu : (μ (s∪t)).toReal≤1 := by
    exact_mod_cast ENNReal.toReal_mono ENNReal.one_ne_top (prob_le_one : μ (s∪t)≤1)
  have hsr := ENNReal.toReal_mono (measure_ne_top _ _) hsm
  have htr := ENNReal.toReal_mono (measure_ne_top _ _) htm
  apply (ENNReal.toReal_le_toReal ENNReal.ofReal_ne_top (measure_ne_top _ _)).mp
  norm_num at hsr htr ⊢
  linarith

def accessibleTarget (κ : Kernel (E×U) X) (S : Set ((E×U)×X)) (c : ℝ≥0∞) : Set (E×U) :=
  {p | c≤κ p (Prod.mk p ⁻¹' S)}
lemma accessibleTarget_measurable (κ : Kernel (E×U) X) [IsFiniteKernel κ]
    (S : Set ((E×U)×X)) (hS : MeasurableSet S) (c : ℝ≥0∞) :
    MeasurableSet (accessibleTarget κ S c) :=
  measurableSet_le measurable_const (Kernel.measurable_kernel_prodMk_left hS)

def commonAccessible (κ : Kernel (E×U) X) (η : Kernel (E×U) Y)
    (S : Set ((E×U)×X)) (T : Set ((E×U)×Y)) (c d : ℝ≥0∞) (B : Set U) : Set (E×U) :=
  (univ×ˢB)∩(accessibleTarget κ S c∩accessibleTarget η T d)
lemma commonAccessible_measurable (κ : Kernel (E×U) X) (η : Kernel (E×U) Y)
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set ((E×U)×X)) (T : Set ((E×U)×Y)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (c d : ℝ≥0∞) (B : Set U) (hB : MeasurableSet B) :
    MeasurableSet (commonAccessible κ η S T c d B) :=
  (MeasurableSet.univ.prod hB).inter
    ((accessibleTarget_measurable κ S hS c).inter (accessibleTarget_measurable η T hT d))

lemma commonAccessible_volume (μ : Measure U) (κ : Kernel (E×U) X) (η : Kernel (E×U) Y)
    [IsFiniteKernel κ] [IsFiniteKernel η]
    (S : Set ((E×U)×X)) (T : Set ((E×U)×Y)) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (c d : ℝ≥0∞) (B : Set U) (_hB : MeasurableSet B) (hm : μ B=1) (e : E)
    (hκ : ENNReal.ofReal (99/100:ℝ)≤(μ.restrict B) (Prod.mk e ⁻¹' accessibleTarget κ S c))
    (hη : ENNReal.ofReal (99/100:ℝ)≤(μ.restrict B) (Prod.mk e ⁻¹' accessibleTarget η T d)) :
    ENNReal.ofReal (49/50:ℝ)≤μ (Prod.mk e ⁻¹' commonAccessible κ η S T c d B) := by
  let _ : IsProbabilityMeasure (μ.restrict B) := ⟨by simp [hm]⟩
  have hs := (accessibleTarget_measurable κ S hS c).preimage (@measurable_prodMk_left E U _ _ e)
  have ht := (accessibleTarget_measurable η T hT d).preimage (@measurable_prodMk_left E U _ _ e)
  have hh := probability_inter_98 (μ.restrict B) hs ht hκ hη
  rw [Measure.restrict_apply (hs.inter ht)] at hh
  convert hh using 1
  congr 1
  ext u
  simp [commonAccessible,and_comm]

end HardSphere.Comparison

end
end

end

end OAI
