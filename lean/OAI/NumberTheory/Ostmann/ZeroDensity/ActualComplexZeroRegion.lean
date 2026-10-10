import OAI.NumberTheory.Ostmann.ZeroDensity.ActualPageUniqueness
import OAI.NumberTheory.Ostmann.ZeroDensity.ComplexRegionFromPage

namespace OAI

/-! # The full-height zero-free region -/

namespace Ostmann

theorem actualComplexZeroRegion : PublishedComplexZeroRegion actualCharacterZeros := by
  obtain ⟨κ, hκ, hpage⟩ := exists_actual_page_uniqueness
  exact complexZeroRegion_of_page κ hκ hpage

end Ostmann

end OAI
