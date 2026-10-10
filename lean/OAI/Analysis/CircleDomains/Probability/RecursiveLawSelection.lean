import OAI.Analysis.CircleDomains.Probability.RecursiveLawConstruction
import OAI.Analysis.CircleDomains.Selection.FirstUncountableRecursion

namespace OAI

/-! Retaining every predecessor in a well-ordered construction.  The selection
hypothesis is discharged by the positive-law construction in the application. -/

open Set Function MeasureTheory
open scoped ENNReal Topology

noncomputable section
namespace CircleDomainRigidity

attribute [local instance] sphereMetric sphereBorel
local instance : BorelSpace Sphere := ⟨rfl⟩
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

omit [BorelSpace C(PathTime, Sphere)] in
theorem exists_recursive_code_laws {I : Type*} [LinearOrder I] [WellFoundedLT I]
    [∀ i : I, Countable (Iio i)]
    (base : PathCodeData Sphere Sphere) (π : Sphere → Sphere)
    (flags : Set Sphere) (ω : TupleType → ℝ≥0∞) (p : I → Sphere)
    (hfull : ∀ L : RecursiveCodeLaw base π flags ω,
      (support (priorHitMass (codePathLaw L.data L.law : Measure C(PathTime, Sphere)))).Countable)
    (hselect : ∀ (i : I) (μ : ℕ → Measure C(PathTime, Sphere)),
      (∀ n, IsFiniteMeasure (μ n)) →
      (∀ n, (support (priorHitMass (μ n))).Countable) →
      ∃ L : RecursiveCodeLaw base π flags ω,
        L.data.target = p i ∧ L.data.priorLaws = μ) :
    ∃ L : I → RecursiveCodeLaw base π flags ω,
      (∀ i, (L i).data.target = p i) ∧
      ∀ i j, i < j → ∃ n,
        (L j).data.priorLaws n = (codePathLaw (L i).data (L i).law : Measure C(PathTime, Sphere)) := by
  let P (i : I) (g : Iio i → RecursiveCodeLaw base π flags ω)
      (L : RecursiveCodeLaw base π flags ω) : Prop :=
    L.data.target = p i ∧ ∀ j : Iio i, ∃ n,
      L.data.priorLaws n = (codePathLaw (g j).data (g j).law : Measure C(PathTime, Sphere))
  have hP (i : I) (g : Iio i → RecursiveCodeLaw base π flags ω) : ∃ L, P i g L := by
    obtain ⟨μ, hmem, hμ⟩ := exists_countable_enumeration_with_default
      (fun j => (codePathLaw (g j).data (g j).law : Measure C(PathTime, Sphere))) 0
    have hc (n : ℕ) : (support (priorHitMass (μ n))).Countable := by
      rcases hμ n with hn | ⟨j, hn⟩
      · rw [hn]
        have hz : support (priorHitMass (0 : Measure C(PathTime, Sphere))) = ∅ := by
          ext x
          simp [priorHitMass, mem_support]
        rw [hz]
        exact countable_empty
      · rw [hn]
        exact hfull (g j)
    have hf (n : ℕ) : IsFiniteMeasure (μ n) := by
      rcases hμ n with hn | ⟨j, hn⟩
      · rw [hn]
        infer_instance
      · rw [hn]
        infer_instance
    obtain ⟨L, ht, hL⟩ := hselect i μ hf hc
    refine ⟨L, ht, ?_⟩
    intro j
    obtain ⟨n, hn⟩ := hmem j
    exact ⟨n, by rw [hL]; exact hn⟩
  obtain ⟨L, hL⟩ := exists_prior_compatible_family P hP
  exact ⟨L, fun i => (hL i).1, fun i j hij => (hL j).2 ⟨i, hij⟩⟩

end CircleDomainRigidity

end

end OAI
