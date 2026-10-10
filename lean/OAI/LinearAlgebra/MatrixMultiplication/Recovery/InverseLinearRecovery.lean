import OAI.LinearAlgebra.MatrixMultiplication.Recovery.OrbitRecovery
import OAI.LinearAlgebra.MatrixMultiplication.Recovery.RecoveryGrowth

namespace OAI

/-! Finite orbit symmetries, masks and exact recovery operations. -/

open MatrixMultiplication.Foundation

namespace MatrixMultiplication.InverseLinearRecovery

abbrev MaskRectangles (L : ℕ) := Finset (Fin L) × Finset (Fin L) × Finset (Fin L)

def RecoveredBy {K X Y Z : Type*} [CommSemiring K]
    [Fintype X] [Fintype Y] [Fintype Z]
    (Q H : Tensor K X Y Z) (L : ℕ) : Prop :=
  ∃ (a : X → (MaskRectangles L × X) → K)
    (b : Y → (MaskRectangles L × Y) → K)
    (c : Z → (MaskRectangles L × Z) → K),
    Tensor.restrict a b c (Tensor.directSum (fun _ : MaskRectangles L => H)) = Q

theorem repair_inverse_linear
    {K G X Y Z : Type*} [CommSemiring K] [Group G] [Fintype G]
    [MulAction G X] [MulAction G Y] [MulAction G Z]
    [Fintype X] [Fintype Y] [Fintype Z]
    [DecidableEq X] [DecidableEq Y] [DecidableEq Z]
    (Q : Tensor K X Y Z)
    (px : X → Prop) (py : Y → Prop) (pz : Z → Prop)
    [DecidablePred px] [DecidablePred py] [DecidablePred pz]
    (hpreserve : ∀ (g : G) x y z, Q (g • x) (g • y) (g • z) = Q x y z)
    {b C : ℝ} {N : ℕ} (hb : 0 ≤ b) (hC : 0 < C) (hN : 3 * C < (N : ℝ))
    (hsupport : ((@Finset.filter (X × Y × Z)
      (fun p => Q p.1 p.2.1 p.2.2 ≠ 0) (Classical.decPred _) Finset.univ).card : ℝ) ≤
      Real.exp (b * N))
    (hx : ∀ x, (∃ y z, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) x).filter fun v => ¬px v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) x).card ≤ C / N)
    (hy : ∀ y, (∃ x z, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) y).filter fun v => ¬py v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) y).card ≤ C / N)
    (hz : ∀ z, (∃ x y, Q x y z ≠ 0) → (((OrbitCounting.orbitSet (G := G) z).filter fun v => ¬pz v).card : ℝ) /
      (OrbitCounting.orbitSet (G := G) z).card ≤ C / N) :
    RecoveredBy Q (ExactRecovery.delete Q px py pz) (RecoveryGrowth.shiftCount b C N) := by
  classical
  apply OrbitRecovery.repair_from_orbit_loss Q px py pz hpreserve (C / N) hx hy hz
    (RecoveryGrowth.shiftCount b C N) (RecoveryGrowth.shiftCount_pos hb hC hN)
  apply RecoveryGrowth.cardinal_budget hC hN Fintype.card_pos hsupport
  simpa only [mul_div_assoc] using
    OrbitRecovery.floor_loss_fraction (G := G) (C / N)
      (div_nonneg hC.le (Nat.cast_nonneg N))

theorem card_recovery_copies (b C : ℝ) (N : ℕ) :
    Fintype.card (MaskRectangles (RecoveryGrowth.shiftCount b C N)) =
      RecoveryGrowth.replicationCount b C N := by
  simpa only [MaskRectangles, Fintype.card_fin, RecoveryGrowth.replicationCount] using
    (ExactRecovery.card_mask_rectangles (I := Fin (RecoveryGrowth.shiftCount b C N)))

theorem subexponential_copies {b C : ℝ} (hb : 0 < b) (hC : 0 < C) :
    Filter.Tendsto (fun N : ℕ =>
      Real.log (Fintype.card (MaskRectangles (RecoveryGrowth.shiftCount b C N))) / N)
      Filter.atTop (nhds 0) := by
  simp_rw [card_recovery_copies]
  exact RecoveryGrowth.tendsto_log_replicationCount_div_nat hb hC

end MatrixMultiplication.InverseLinearRecovery

end OAI
