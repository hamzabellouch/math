import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingCommutatorCoefficient

namespace OAI

/-! # The uniform bilinear difference estimate in the expanding norm -/

namespace DefocusingNLS

theorem expandingProduct_difference_norm (a k L : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (q r q' r' : FourierL2) :
    ‖expandingProduct a k L ha ha1 hk hL q r - expandingProduct a k L ha ha1 hk hL q' r'‖ ≤
      expandingAlgebraBound a k * (‖q - q'‖ * ‖r‖ + ‖q'‖ * ‖r - r'‖) := by
  let B := expandingBilinearProduct a k L ha ha1 hk hL
  have he : B q r - B q' r' = B (q - q') r + B q' (r - r') := by
    simp only [map_sub, sub_apply]
    abel
  change ‖B q r - B q' r'‖ ≤ _
  rw [he]
  exact (norm_add_le _ _).trans
    ((add_le_add (expandingProduct_norm_le a k L ha ha1 hk hL _ _)
      (expandingProduct_norm_le a k L ha ha1 hk hL _ _)).trans_eq (by
        unfold expandingAlgebraBound
        ring))

end DefocusingNLS

end OAI
