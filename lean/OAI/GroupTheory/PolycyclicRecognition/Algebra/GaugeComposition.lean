import OAI.GroupTheory.PolycyclicRecognition.Algebra.FactorSystemGauge

namespace OAI

/-! # Composing explicit section corrections -/

namespace PolycyclicRecognition
variable {N Q : Type*} [Group N] [Group Q]

theorem gauge_gauge_factor (F : NonabelianFactorSystem N Q)
    (b c : Q → N) (hb : b 1 = 1) (hc : c 1 = 1)
    (hcb : c 1 * b 1 = 1) (q r : Q) :
    ((F.gauge b hb).gauge c hc).factor q r =
      (F.gauge (fun q => c q * b q) hcb).factor q r := by
  change c q * (b q * F.action q (c r) * (b q)⁻¹) *
    (b q * F.action q (b r) * F.factor q r * (b (q * r))⁻¹) * (c (q * r))⁻¹ =
      (c q * b q) * F.action q (c r * b r) * F.factor q r * (c (q * r) * b (q * r))⁻¹
  rw [map_mul]
  group

theorem gauge_gauge_action (F : NonabelianFactorSystem N Q)
    (b c : Q → N) (hb : b 1 = 1) (hc : c 1 = 1)
    (hcb : c 1 * b 1 = 1) (q : Q) (x : N) :
    ((F.gauge b hb).gauge c hc).action q x =
      (F.gauge (fun q => c q * b q) hcb).action q x := by
  change c q * (b q * F.action q x * (b q)⁻¹) * (c q)⁻¹ =
    (c q * b q) * F.action q x * (c q * b q)⁻¹
  group

end PolycyclicRecognition

end OAI
