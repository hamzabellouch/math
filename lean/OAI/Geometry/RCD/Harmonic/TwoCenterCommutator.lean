import OAI.Geometry.RCD.Coordinates.MatrixNormConversion

namespace OAI

/-!
# The two-center commutator estimate

Near-identity radial matrices allow absorption of the commutator error.
The constant coefficient then recovers the coordinate difference between
the two centers with an error proportional to the same defect.
-/

noncomputable section

namespace RegularPointCoordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Near the identity, the commutator appearing in the two-center radial
identities controls the difference of the two normalization matrices. -/
theorem radial_commutator_norm_le (A B : E →L[ℝ] E)
    (hA : ‖A - 1‖ ≤ 1 / 4) {η : ℝ}
    (herror : ‖B * A - (A - 1) * B‖ ≤ η) : ‖B‖ ≤ 2 * η := by
  have hid : B = (B * A - (A - 1) * B) -
      (B * (A - 1) - (A - 1) * B) := by noncomm_ring
  have htriangle : ‖B‖ ≤ ‖B * A - (A - 1) * B‖ +
      (‖B‖ * ‖A - 1‖ + ‖A - 1‖ * ‖B‖) := by
    calc
      ‖B‖ = ‖(B * A - (A - 1) * B) -
          (B * (A - 1) - (A - 1) * B)‖ := congrArg norm hid
      _ ≤ ‖B * A - (A - 1) * B‖ + ‖B * (A - 1) - (A - 1) * B‖ :=
        norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl
        ((norm_sub_le (B * (A - 1)) ((A - 1) * B)).trans
          (add_le_add (norm_mul_le _ _) (norm_mul_le _ _)))
  have hsmall := mul_le_mul_of_nonneg_left hA (norm_nonneg B)
  nlinarith

/-- An approximate identity controls vectors from below without choosing
an inverse. -/
theorem norm_le_two_mul_norm_of_near_id (A : E →L[ℝ] E)
    (hA : ‖A - 1‖ ≤ 1 / 2) (v : E) : ‖v‖ ≤ 2 * ‖A v‖ := by
  have hdiff : v = A v - (A - 1) v := by simp
  have htriangle : ‖v‖ ≤ ‖A v‖ + ‖A - 1‖ * ‖v‖ := by
    calc
      ‖v‖ = ‖A v - (A - 1) v‖ := congrArg norm hdiff
      _ ≤ ‖A v‖ + ‖(A - 1) v‖ := norm_sub_le _ _
      _ ≤ _ := add_le_add le_rfl ((A - 1).le_opNorm v)
  have hsmall := mul_le_mul_of_nonneg_right hA (norm_nonneg v)
  nlinarith

/-- The constant recovered from the radial identities is close to the
actual coordinate difference, with error proportional to the same defect. -/
theorem two_center_constant_recovery (Ax Az : E →L[ℝ] E) (δ c : E)
    (hx : ‖Ax - 1‖ ≤ 1 / 2) (hz : ‖Az - 1‖ ≤ 1 / 4)
    (hc : c = Ax δ) {η M : ℝ} (hM : ‖c‖ ≤ M)
    (hcomm : ‖(Az - Ax) * Az - (Az - 1) * (Az - Ax)‖ ≤ η)
    (hconst : ‖(Az - 1) c‖ ≤ η) :
    ‖Az - Ax‖ ≤ 2 * η ∧ ‖δ - c‖ ≤ 2 * η * (1 + 2 * M) := by
  have hB := radial_commutator_norm_le Az (Az - Ax) hz hcomm
  have hη : 0 ≤ η := (norm_nonneg _).trans hconst
  refine ⟨hB, ?_⟩
  have hid : (Ax - 1) c = (Az - 1) c - (Az - Ax) c := by simp
  have hforce : ‖(Ax - 1) c‖ ≤ η + 2 * η * M := by
    calc
      ‖(Ax - 1) c‖ = ‖(Az - 1) c - (Az - Ax) c‖ := congrArg norm hid
      _ ≤ ‖(Az - 1) c‖ + ‖(Az - Ax) c‖ := norm_sub_le _ _
      _ ≤ η + ‖Az - Ax‖ * ‖c‖ := add_le_add hconst ((Az - Ax).le_opNorm c)
      _ ≤ _ := add_le_add le_rfl (mul_le_mul hB hM (norm_nonneg c) (by positivity))
  have hidentity : Ax (δ - c) = -((Ax - 1) c) := by rw [map_sub, ← hc]; simp
  have hlower := norm_le_two_mul_norm_of_near_id Ax hx (δ - c)
  rw [hidentity, norm_neg] at hlower
  nlinarith

end RegularPointCoordinates

end

end OAI
