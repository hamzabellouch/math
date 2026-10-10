import OAI.GroupTheory.PolycyclicRecognition.Analysis.CompactSectionVolume
import OAI.GroupTheory.PolycyclicRecognition.Algebra.SubexponentialOperations

namespace OAI

/-! # One compact slice retains subexponential volume -/

noncomputable section

namespace PolycyclicRecognition

open Set Metric MeasureTheory Filter
open scoped Topology

theorem exists_subexponential_compact_sections
    (n k : ℕ) (R : ℝ → ℝ) (hR : ∀ r, 1 ≤ R r)
    (hRupper : HasSubexponentialUpperBound R)
    (K : ℝ → Set ((Fin n → ℝ) × (Fin k → ℝ)))
    (hK : ∀ r, IsCompact (K r))
    (hKR : ∀ r p, p ∈ K r → ‖p.2‖ ≤ R r)
    (hKpos : ∀ r, 0 < (volume (K r)).toReal)
    (hKlower : HasSubexponentialLowerBound (fun r => (volume (K r)).toReal)) :
    ∃ z : ℝ → Fin k → ℝ,
      (∀ r, ‖z r‖ ≤ R r) ∧
      (∀ r, IsCompact {v | (v, z r) ∈ K r}) ∧
      HasSubexponentialLowerBound (fun r => (volume {v | (v, z r) ∈ K r}).toReal) := by
  classical
  let q := fun r => (2 * R r) ^ k
  let t := fun r => (volume (K r)).toReal / (2 * q r)
  have hqpos (r : ℝ) : 0 < q r := by have := hR r; dsimp [q]; positivity
  have htpos (r : ℝ) : 0 < t r := div_pos (hKpos r) (mul_pos (by norm_num) (hqpos r))
  have hs (r : ℝ) : ∃ z ∈ closedBall 0 (R r),
      IsCompact {v | (v, z) ∈ K r} ∧ t r < (volume {v | (v, z) ∈ K r}).toReal := by
    apply exists_compact_section_volume_gt n k (q := q r) (hK r) (isCompact_closedBall _ _)
      (fun p hp => by simpa only [mem_closedBall, dist_zero_right] using hKR r p hp)
      (htpos r).le
    · rw [Real.volume_pi_closedBall _ (by have := hR r; linarith),
        ENNReal.toReal_ofReal (by have := hR r; positivity)]
      simp only [Fintype.card_fin, q, le_refl]
    · have he : t r * q r = (volume (K r)).toReal / 2 := by
        dsimp [t]
        field_simp [ne_of_gt (hqpos r)]
      rw [he]
      linarith [hKpos r]
  choose z hz hzc hmass using hs
  have hqUpper : HasSubexponentialUpperBound q :=
    ((subexponential_upper_const 2).mul hRupper (Eventually.of_forall (by intro r; norm_num))).pow
      (Eventually.of_forall (fun r => by have := hR r; positivity)) k
  have htLower : HasSubexponentialLowerBound t := hKlower.div
    ((subexponential_upper_const 2).mul hqUpper (Eventually.of_forall (by intro r; norm_num)))
    (Eventually.of_forall (fun r => mul_pos (by norm_num) (hqpos r)))
  exact ⟨z, fun r => by simpa only [mem_closedBall, dist_zero_right] using hz r,
    hzc, htLower.mono (Eventually.of_forall (fun r => (hmass r).le))⟩

end PolycyclicRecognition

end

end OAI
