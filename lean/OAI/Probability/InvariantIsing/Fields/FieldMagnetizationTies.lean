import OAI.Probability.InvariantIsing.Fields.FieldMagnetizationFiber

namespace OAI

/-! A pointwise plateau criterion for the chosen global representative. -/

noncomputable section

namespace InvariantIsing

lemma fieldMagnetizationPath_eq_of_index_height_eq (h : FieldStep) (s t : ℝ)
    (he : h.height (fieldLevelIndex h s) = h.height (fieldLevelIndex h t)) :
    fieldMagnetizationPath h s = fieldMagnetizationPath h t := by
  change fieldMagnetizationLevel h (fieldLevelIndex h s) =
    fieldMagnetizationLevel h (fieldLevelIndex h t)
  exact fieldMagnetizationLevel_eq_of_height_eq h _ _ he

end InvariantIsing

end

end OAI
