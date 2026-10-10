import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationMomentKernels
import OAI.NumberTheory.Ostmann.Arithmetic.HistoryCompensationRepresentativePatternsBasic

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Arithmetic.HistoryCompensationRepresentativePatterns
open Construction Construction.CanonicalOccurrenceTransport HistoryPairRows HistoryPairRepresentatives
open CompensationEqualityPatterns HistorySymbolicEncoding HistoryPairPolynomialKernel
local instance (seed : List SourceSlot) (l : ℕ) : DecidableEq (Internal seed l) := Classical.decEq _

variable (seed : List SourceSlot) {l : ℕ} (h k : History l)
  {V : ℕ → ℕ} {outside : List ℕ} (hs : h.Supported V outside) (ks : k.Supported V outside)
  (hh : TreeSourceLabels seed h) (hk : TreeSourceLabels seed k)
  (p : Pattern (pairedHistoryType seed l)) (b : BlockDraw p ℕ)
  (hv : ∀ i, (slot h k (pairedInternalEquiv seed h k hh hk i)).value = expand p b i)

include hv in

theorem unitKernel_product_le_blocks :
    (∏ r : Representative h k, unitKernel h k hs ks r) ≤ ∏ q : Block p, 2 / (b.val q : ℝ) := by
  calc
    _ ≤ ∏ r : Representative h k, 2 * (prime h k r : ℝ)⁻¹ :=
      Finset.prod_le_prod₀ (fun r _ => (unitKernel_bounds h k hs ks r).1)
        (fun r _ => HistoryCompensationMoment.unitKernel_le_two_div_prime h k hs ks r)
    _ = _ := by
      simpa only [div_eq_mul_inv] using
        representative_product_eq_blocks seed h k hh hk p b hv (fun n => 2 * (n : ℝ)⁻¹)

include hv in

theorem mixedKernel_product_le_blocks :
    (∏ r : Representative h k, mixedKernel h k hs ks r) ≤ ∏ q : Block p, 2 / (b.val q : ℝ) := by
  calc
    _ ≤ ∏ r : Representative h k, 2 * (prime h k r : ℝ)⁻¹ :=
      Finset.prod_le_prod₀ (fun r _ => (mixedKernel_bounds h k hs ks r).1)
        (fun r _ => HistoryCompensationMoment.mixedKernel_le_two_div_prime h k hs ks r)
    _ = _ := by
      simpa only [div_eq_mul_inv] using
        representative_product_eq_blocks seed h k hh hk p b hv (fun n => 2 * (n : ℝ)⁻¹)

end Ostmann.Arithmetic.HistoryCompensationRepresentativePatterns

end

end OAI
