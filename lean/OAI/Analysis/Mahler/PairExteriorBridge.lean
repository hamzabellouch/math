import OAI.Analysis.Mahler.PairTransgression

namespace OAI

open Complex ContinuousAlternatingMap

namespace Mahler
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The continuous primitive is the shuffle wedge, with
its two slots kept in their specified order. -/
lemma pairExterior_is_wedge (a b : E →L[ℝ] ℂ) :
    (pairExterior a b).toAlternatingMap =
      (wedge (oneForm (fun _ : E => a) 0).toAlternatingMap
        (oneForm (fun _ : E => b) 0).toAlternatingMap).domDomCongr (prependFinEquiv 1) := by
  rw [← covectorVolume_one a, ← covectorVolume_one b, wedge_covectorVolume,
    covectorVolume_prepend, pairExterior_toAlternatingMap]
  congr 1
  funext i
  fin_cases i <;> rfl

end Mahler

end OAI
