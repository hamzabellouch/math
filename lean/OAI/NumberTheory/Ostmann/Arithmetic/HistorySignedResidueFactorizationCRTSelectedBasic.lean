import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesLift

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidueFactorization
open Construction HistoryCRTIntegration HistorySignedResidues
variable {l : ℕ}

theorem rootModulus_dvd_comparisonModulus (h k : History l) (outside : List ℕ) (n : ℕ) :
    rootModulus h ∣ comparisonModulus h k outside n := by
  refine ⟨pairModulus h k outside * outsideModulus outside * frequencyModulus h k n *
    representativeModulus h k, ?_⟩
  simp only [comparisonModulus, crtModulus]
  ring

theorem outsideModulus_dvd_comparisonModulus (h k : History l) (outside : List ℕ) (n : ℕ) :
    outside.prod ∣ comparisonModulus h k outside n := by
  refine ⟨pairModulus h k outside * rootModulus h * frequencyModulus h k n *
    representativeModulus h k, ?_⟩
  simp only [comparisonModulus, crtModulus, outsideModulus]
  ring

theorem frequencyModulus_dvd_comparisonModulus (h k : History l) (outside : List ℕ) (n : ℕ) :
    frequencyModulus h k n ∣ comparisonModulus h k outside n := by
  refine ⟨pairModulus h k outside * rootModulus h * outsideModulus outside *
    representativeModulus h k, ?_⟩
  simp only [comparisonModulus, crtModulus]
  ring

theorem representativeModulus_dvd_comparisonModulus (h k : History l) (outside : List ℕ) (n : ℕ) :
    representativeModulus h k ∣ comparisonModulus h k outside n := by
  refine ⟨pairModulus h k outside * rootModulus h * outsideModulus outside *
    frequencyModulus h k n, ?_⟩
  simp only [comparisonModulus, crtModulus]
  ring

end Ostmann.Arithmetic.HistorySignedResidueFactorization

end

end OAI
