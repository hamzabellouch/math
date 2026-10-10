import OAI.Analysis.KadisonKastler.ProjectionPolarRounding
import OAI.Analysis.KadisonKastler.CompleteCommutantDistance

namespace OAI

/-! # Rounding a selfadjoint approximant to an ambient projection -/

namespace KadisonKastler

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

local instance nearbyProjectionRoundingOrder (M : VonNeumannAlgebra H) :
    PartialOrder (Algebra M) := CStarAlgebra.spectralOrder _
local instance nearbyProjectionRoundingStarOrder (M : VonNeumannAlgebra H) :
    StarOrderedRing (Algebra M) := CStarAlgebra.spectralOrderedRing _

theorem exists_projection_near_selfAdjoint_approximant
    (M : VonNeumannAlgebra H) [Nontrivial (Algebra M)]
    (p : H →L[ℂ] H) (hp : IsStarProjection p)
    (a : Algebra M) (ha : IsSelfAdjoint a) {ε : ℝ}
    (hε : 0 ≤ ε) (hsmall : ε < 1 / 64) (hap : ‖a.val - p‖ ≤ ε) :
    ∃ q : Algebra M, IsStarProjection q ∧ ‖q.val - p‖ ≤ 25 * ε := by
  have hpn : ‖p‖ ≤ 1 := hp.norm_le
  have han : ‖a.val‖ ≤ 1 + ε := by
    have h := norm_le_norm_sub_add a.val p
    linarith
  have hd : ‖a.val * a.val - a.val‖ ≤ 4 * ε := by
    have he : a.val * a.val - a.val =
        (a.val - p) * a.val + p * (a.val - p) - (a.val - p) := by
      have hpp := hp.isIdempotentElem.eq
      noncomm_ring [hpp]
    rw [he]
    calc
      _ ≤ ‖(a.val - p) * a.val + p * (a.val - p)‖ + ‖a.val - p‖ := norm_sub_le _ _
      _ ≤ (‖a.val - p‖ * ‖a.val‖ + ‖p‖ * ‖a.val - p‖) + ‖a.val - p‖ :=
        add_le_add (norm_add_le _ _ |>.trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))) le_rfl
      _ ≤ 4 * ε := by
        have h1 := mul_le_mul hap han (norm_nonneg _) hε
        have h2 := mul_le_mul hpn hap (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
        nlinarith
  let x : Algebra M := a + a - 1
  have hx : IsSelfAdjoint x := (ha.add ha).sub (by simp [IsSelfAdjoint])
  have hxn : ‖x‖ ≤ 1 + 16 * ε := by
    have hs : ‖p + p - 1‖ ≤ 1 := by
      have h := projection_reflection_norm_le_one p hp
      have he : p + p - 1 = -(1 - p - p) := by abel
      rwa [he, norm_neg]
    have he : x.val = (a.val - p) + (a.val - p) + (p + p - 1) := by
      change a.val + a.val - 1 = _
      abel
    change ‖x.val‖ ≤ _
    rw [he]
    have h := (norm_add_le ((a.val - p) + (a.val - p)) (p + p - 1)).trans
      (add_le_add (norm_add_le (a.val - p) (a.val - p)) le_rfl)
    linarith
  have hxd : ‖x * x - 1‖ ≤ 16 * ε := by
    have he : x.val * x.val - 1 = (4 : ℕ) • (a.val * a.val - a.val) := by
      change (a.val + a.val - 1) * (a.val + a.val - 1) - 1 = _
      simp only [show (4 : ℕ) = 1 + 1 + 1 + 1 from rfl, add_nsmul, one_nsmul]
      noncomm_ring
    change ‖x.val * x.val - 1‖ ≤ _
    rw [he]
    exact (norm_nsmul_le : ‖(4 : ℕ) • (a.val * a.val - a.val)‖ ≤
      (4 : ℝ) * ‖a.val * a.val - a.val‖).trans (by
        norm_num only [Nat.cast_ofNat]
        linarith)
  obtain ⟨q, hq, hqa⟩ := exists_projection_near_almost_symmetry x hx
    (by positivity : 0 ≤ 16 * ε) (by linarith) hxn hxd
  have hhalf : (1 / 2 : ℝ) • (x + 1) = a := by dsimp [x]; module
  rw [hhalf] at hqa
  refine ⟨q, hq, ?_⟩
  have h := norm_sub_le_norm_sub_add_norm_sub q.val a.val p
  change ‖q.val - a.val‖ ≤ 3 * (16 * ε) / 2 at hqa
  linarith

end

end KadisonKastler

end OAI
