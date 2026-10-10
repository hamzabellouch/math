import Mathlib
import OAI.Probability.Ballisticity.Walk.PreBrownianGridMartingale
import OAI.Probability.Ballisticity.Walk.RowProductIntegral
import OAI.Probability.Ballisticity.Stationary.EpisodeFresh
import OAI.Probability.Ballisticity.Stationary.BadArraySampling
import OAI.Probability.Ballisticity.Entropy.BadWindowEntropy
import OAI.Probability.Ballisticity.Stationary.BadArrayElliptic
import OAI.Probability.Ballisticity.Estimates.BadStageMoment
import OAI.Probability.Ballisticity.Estimates.BadDropMoment
import OAI.Probability.Ballisticity.Renewal.PositiveLengthMark
import OAI.Probability.Ballisticity.Stationary.BadFiniteArray
import OAI.Probability.Ballisticity.Stationary.ArrayClassProbability
import OAI.Probability.Ballisticity.Stationary.StationaryProfile2
import OAI.Probability.Ballisticity.Estimates.RapidDecayTail
import OAI.Probability.Ballisticity.Renewal.VelocityWords

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

theorem directional_transience_implies_ballisticity : MainStatement := by
  intro d hd ν hν hue ℓ hℓ htrans
  exact directional_transience_implies_ballisticity_unit hd ν hue ℓ hℓ htrans

end DirectionalTransience

end

end OAI
