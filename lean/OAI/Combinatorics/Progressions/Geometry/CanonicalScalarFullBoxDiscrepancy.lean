import OAI.Combinatorics.Progressions.Estimates.UnconditionedTrimmedSliceFamily

namespace OAI

section

namespace Erdos3
open scoped Classical

theorem rectangularScalarDiscrepancy_fullBox {I J : Type*}
    [Fintype I] [Fintype J] [decJ : DecidableEq J]
    (parent : I → ℤ) (H : I → ℕ) (h g : (I → ℤ) → ℂ)
    (epsilon level : ℝ) (parameters : J → ℕ)
    (hparam : ∀ j, (0 : ℤ) < parameters j) (z : Option J × I → ℤ) :
    rectangularScalarDiscrepancy parent H h g epsilon level 1
      0 0 (fun j => (parameters j : ℤ)) hparam z =
      (integerBoxUniformWeights (fun _ : J => (0 : ℤ))
        (fun j => (parameters j : ℤ)) hparam).mean
        (fun t => realZeroExtendFinset (translatedIntegerBox parent H) (fun x => (h x).re)
          (smoothAffineSample (fun j => (t j).val) z) -
          (1 + epsilon) * level *
            realZeroExtendFinset (translatedIntegerBox parent H) (fun x => (g x).re)
              (smoothAffineSample (fun j => (t j).val) z)) := by
  cases Subsingleton.elim decJ (Classical.typeDecidableEq J)
  simp only [rectangularScalarDiscrepancy, Nat.cast_one, one_mul, Pi.zero_apply, zero_add]
  rfl

theorem canonicalScalarFullBox_transfer {Ω I J : Type*}
    [Fintype Ω] [Fintype I] [Fintype J] [decJ : DecidableEq J]
    (outer : FiniteProbabilityWeights Ω) (source : Ω → Option J × I → ℤ)
    (parent : I → ℤ) (H : I → ℕ) (h g : (I → ℤ) → ℂ)
    (epsilon level : ℝ) (parameters : J → ℕ)
    (hparam : ∀ j, (0 : ℤ) < parameters j) (target : ℝ)
    (hplain : outer.eventProbability (fun z => Real.exp (-target) <
      (integerBoxUniformWeights (fun _ : J => (0 : ℤ))
        (fun j => (parameters j : ℤ)) hparam).mean
        (fun t => realZeroExtendFinset (translatedIntegerBox parent H) (fun x => (h x).re)
          (smoothAffineSample (fun j => (t j).val) (source z)) -
          (1 + epsilon) * level *
            realZeroExtendFinset (translatedIntegerBox parent H) (fun x => (g x).re)
              (smoothAffineSample (fun j => (t j).val) (source z)))) ≤ Real.exp (-target)) :
    outer.eventProbability (fun z => Real.exp (-target) <
      rectangularScalarDiscrepancy parent H h g epsilon level 1
        0 0 (fun j => (parameters j : ℤ)) hparam (source z)) ≤ Real.exp (-target) := by
  simpa only [rectangularScalarDiscrepancy_fullBox] using hplain

end Erdos3

end

end OAI
