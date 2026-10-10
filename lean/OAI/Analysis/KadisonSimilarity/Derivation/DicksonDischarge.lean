import OAI.Analysis.KadisonSimilarity.Derivation.GrothendieckMatrix

namespace OAI

/-! The exact norm-two row and column estimate, with the little Grothendieck
inequality obtained from norm-attaining states and matrix dilation. -/

noncomputable section
namespace KadisonSimilarity

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Dickson (2014), Lemma 2.9, equation (19), for the native rectangular norms. -/
theorem dicksonTwoBound_proved : DicksonTwoBound (A := A) H :=
  dicksonTwoBound_of_littleGrothendieck littleGrothendieck_proved

end KadisonSimilarity

end

end OAI
