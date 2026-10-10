import OAI.Algebra.DepthFive.ImmSecondTrace
import OAI.Algebra.DepthFive.FockLayerProfile

namespace OAI

noncomputable section
open scoped BigOperators

namespace Problem335

/-- The actual finite normalized IMM second trace is bounded by the sum
of the compatible local occupation-polynomial products. This has no
source-validity, moment, or nonempty-index assumptions. -/
theorem immNormalizedMatrix_second_trace_le_localPolynomial_sum
    (n : ℕ) (hn : 0 < n) (side : Fin n → Bool) (a b : ℕ) :
    let A := immNormalizedMatrix n side a b
    let eps := immPathSignedShift n hn (fun x => side x.1)
    ((A.conjTranspose * A) ^ 2).trace.re ≤
      ∑ d : ImmSourceIndex n side a b, ∑ p, ∑ q, ∑ r, ∑ s,
        if eps p - eps q = eps r - eps s then
          ∏ t : Fin n, LocalMoments.localPolynomial (side t) (fun x => d.1 (t, x))
            (FockLayerProfile.immProfile n hn p t)
            (FockLayerProfile.immProfile n hn q t)
            (FockLayerProfile.immProfile n hn r t)
        else 0 := by
  classical
  dsimp only
  rw [immNormalizedMatrix_second_trace n hn side a b]
  apply Finset.sum_le_sum
  intro d hd
  apply Finset.sum_le_sum
  intro p hp
  apply Finset.sum_le_sum
  intro q hq
  apply Finset.sum_le_sum
  intro r hr
  apply Finset.sum_le_sum
  intro s hs
  split_ifs with hmatch
  · exact FockLayerProfile.imm_zeroExtended_amplitude_four_le_local_product
      n hn side (fun d : ImmSourceIndex n side a b => d.1)
      Subtype.val_injective d p q r s hmatch
  · exact le_rfl

end Problem335

end

end OAI
