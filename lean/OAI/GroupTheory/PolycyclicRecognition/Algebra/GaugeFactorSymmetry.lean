import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorSystemGauge

namespace OAI

/-! # Symmetries retained when correcting a factor system -/

namespace PolycyclicRecognition
variable {N Q : Type*} [Group N] [Group Q]

theorem gauge_factor_fixed (F : NonabelianFactorSystem N Q) (b : Q → N) (hb : b 1 = 1)
    (T : N →* N) (hact : ∀ q x, T (F.action q x) = F.action q (T x))
    (hfactor : ∀ q r, T (F.factor q r) = F.factor q r) (hTb : ∀ q, T (b q) = b q)
    (q r : Q) : T ((F.gauge b hb).factor q r) = (F.gauge b hb).factor q r := by
  change T (b q * F.action q (b r) * F.factor q r * (b (q * r))⁻¹) =
    b q * F.action q (b r) * F.factor q r * (b (q * r))⁻¹
  rw [map_mul, map_mul, map_mul, map_inv, hTb, hTb, hact, hTb, hfactor]

end PolycyclicRecognition

end OAI
