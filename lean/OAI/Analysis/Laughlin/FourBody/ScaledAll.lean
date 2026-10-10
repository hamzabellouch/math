import OAI.Analysis.Laughlin.FourBody.All
import OAI.Analysis.Laughlin.FourBody.Scaled

namespace OAI

namespace Laughlin.Certificate

theorem scaled_four_body_certificates (D : ℕ) (hD₁ : 1 ≤ D) (hD₂ : D ≤ 23) :
    (scaledGram D * (certificateDiagonal D-scaledError D) * scaledGram D).PosSemidef :=
  scaled_compression_positive D (four_body_certificates D hD₁ hD₂)

end Laughlin.Certificate

end OAI
