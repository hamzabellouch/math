import OAI.Combinatorics.ProgressionColoring.DigitProduct
import OAI.Combinatorics.ProgressionColoring.UpperBound

namespace OAI

namespace QuantitativeVanDerWaerden

/-- The product of any number of copies of one cyclic Boolean coloring. -/
theorem cyclic_binary_product_lower {N k m : ℕ} {C : ZMod N → Bool}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hC : CyclicAvoids C k) :
    N ^ m < W (2 ^ m) k := by
  exact binary_digit_product_lt_W hN hk hC
    (finite_ramsey (pow_pos (by decide : 0 < (2 : ℕ)) m) (by omega))

theorem cyclic_binary_color_lower {N k r : ℕ} {C : ZMod N → Bool}
    (hN : 2 ≤ N) (hk : 2 ≤ k) (hr : 2 ≤ r) (hC : CyclicAvoids C k) :
    N ^ Nat.log 2 r < W r k := by
  exact binary_digit_product_log_lt_W hN hk hr hC
    (finite_ramsey (by omega) (by omega))

end QuantitativeVanDerWaerden

end OAI
