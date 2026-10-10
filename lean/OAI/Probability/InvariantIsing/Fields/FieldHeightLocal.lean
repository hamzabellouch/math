import OAI.Probability.InvariantIsing.Fields.FieldHeightGradient

namespace OAI

/-! Actual joint derivative data near every strict field-height vector. -/

noncomputable section
open IsingPerceptron Set

namespace InvariantIsing

theorem fieldHeight_local_family (h : FieldStep) (r : Fin (h.depth + 1) → ℝ)
    (hs : r ∈ fieldStrictHeightCone h.depth) :
    ∃ (I : Set (Fin (h.depth + 1) → ℝ)) (_ : IsOpen I), r ∈ I ∧
      ∃ F : FieldFiniteFamily (h.depth + 1) I,
        F.U = fieldFiniteValue (fieldHeightFiniteList h) ∧
        ∀ q ∈ I, ∀ hq : q ∈ fieldStrictHeightCone h.depth, ∀ i,
          F.P i (q, 0) - (if i = Fin.last h.depth then (1 / 2 : ℝ) else 0) =
            -(h.cut i.succ - h.cut i.castSucc) / 2 *
              fieldMagnetizationLevel (fieldStepOfStrictHeights h q hq) i := by
  have hv (av : FieldFiniteStep (h.depth + 1)) (hav : av ∈ fieldHeightFiniteList h) :
      0 < fieldFiniteVariance av.base av.slope r := by
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hav
    change 0 < fieldFiniteVariance 0 (fieldHeightSlope j) r
    rw [fieldHeightSlope_variance]
    exact hs j
  obtain ⟨I, hI, hr, F, hF⟩ := fieldFiniteValue_local_family (fieldHeightFiniteList h) r hv
  exact ⟨I, hI, hr, F, hF, fun q hq hqs i =>
    fieldHeight_gradient_identification h F hF q hq hqs i⟩

end InvariantIsing

end

end OAI
