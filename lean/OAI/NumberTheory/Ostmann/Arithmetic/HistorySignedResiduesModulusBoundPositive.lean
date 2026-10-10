import OAI.NumberTheory.Ostmann.Arithmetic.HistoryPathCoordinates
import OAI.NumberTheory.Ostmann.Arithmetic.HistorySignedResiduesMask

namespace OAI

noncomputable section
namespace Ostmann.Arithmetic.HistorySignedResidues
open Construction

theorem testProduct_ne_zero {l : ℕ} (h : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) : testProduct h ≠ 0 := by
  induction h with
  | leaf a =>
    apply mul_ne_zero (History.supported_root_frequency_ne_zero hs)
    exact_mod_cast (HistoryLinearization.supported_small_product_pos hs).ne'
  | node a p u hp hm left right il ir =>
    have hf : (History.node a p u hp hm left right).frequencies.prod ≠ 0 := by
      apply List.prod_ne_zero
      intro hv
      exact (History.supported_frequency_bounds hs 0 hv).1 rfl
    have ha : ((a.small.map SmallSlot.value).prod:ℤ) ≠ 0 := by
      exact_mod_cast (HistoryLinearization.supported_small_product_pos hs).ne'
    have hu : ((u.map SmallSlot.value).prod:ℤ) ≠ 0 := by
      exact_mod_cast (History.supported_compensation_product_pos hs).ne'
    exact mul_ne_zero (mul_ne_zero hf ha)
      (mul_ne_zero (mul_ne_zero (mul_ne_zero
        (mul_ne_zero (History.supported_root_frequency_ne_zero hs) hu) (pow_ne_zero 2 hu))
        (il (History.supported_left hs))) (ir (History.supported_right hs)))

theorem pairModulus_pos {l : ℕ} (h k : History l) {V : ℕ → ℕ} {outside : List ℕ}
    (hs : h.Supported V outside) (ks : k.Supported V outside)
    (hout : ∀q∈outside,0<q) : 0 < pairModulus h k outside := by
  have ho : (outside.prod:ℤ) ≠ 0 := by
    exact_mod_cast (List.prod_pos hout).ne'
  apply Int.natAbs_pos.mpr
  exact mul_ne_zero (pow_ne_zero l (pairedDivisorProduct_ne_zero h k hs ks))
    (mul_ne_zero (mul_ne_zero (testProduct_ne_zero h hs) (testProduct_ne_zero k ks)) ho)

end Ostmann.Arithmetic.HistorySignedResidues

end

end OAI
