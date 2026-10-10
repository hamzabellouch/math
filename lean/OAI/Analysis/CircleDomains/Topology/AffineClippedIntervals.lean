import OAI.Analysis.CircleDomains.Selection.AffinePhysicalRestriction

namespace OAI

/-! Affine time coordinates commute with clipping to an overlapping
 interval. This permits length estimates across collar junctions. -/

open Set Function
open scoped ENNReal

noncomputable section

namespace CircleDomainRigidity

theorem affine_rescale_eq_clip {a b : PathTime} (hab : a < b) (t : PathTime) :
    affinePathTime a b (rescalePathTime a b t) = timeClip a b t := by
  rcases le_total t a with hta | hat
  · have hr : rescalePathTime a b t = ⊥ := by
      apply Subtype.ext
      rw [rescalePathTime_coe]
      have hq : ((t : ℝ) - a) / ((b : ℝ) - a) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hta) (sub_nonneg.mpr hab.le)
      change max 0 (min 1 _) = 0
      exact max_eq_left ((min_le_right _ _).trans hq)
    rw [hr, affinePathTime_zero]
    change a = max a (min b t)
    exact (max_eq_left ((min_le_right _ _).trans hta)).symm
  · rcases le_total b t with hbt | htb
    · have hr : rescalePathTime a b t = ⊤ := by
        apply Subtype.ext
        rw [rescalePathTime_coe]
        have hq : 1 ≤ ((t : ℝ) - a) / ((b : ℝ) - a) := by
          apply (le_div_iff₀ (sub_pos.mpr (show (a : ℝ) < b from hab))).mpr
          linarith [show (b : ℝ) ≤ t from hbt]
        change max 0 (min 1 _) = 1
        rw [min_eq_left hq]
        norm_num
      rw [hr, affinePathTime_one]
      change b = max a (min b t)
      rw [min_eq_left hbt, max_eq_right hab.le]
    · rw [affine_rescalePathTime hab ⟨hat, htb⟩]
      change t = max a (min b t)
      rw [min_eq_right htb, max_eq_right hat]

theorem timeClip_comp_of_overlap {a b c d : PathTime}
    (hcb : c ≤ b) (t : PathTime) :
    timeClip a b (timeClip c d t) = timeClip (max a c) (min b d) t := by
  change max a (min b (max c (min d t))) = max (max a c) (min (min b d) t)
  rw [min_max_distrib_left, min_eq_right hcb, max_assoc, min_assoc]

/-- The overlap assumption excludes the case of two disjoint clipping intervals. -/
theorem affine_clip_rescaled {a b : PathTime} (hab : a < b) {c d : PathTime}
    (hc : c ≤ b) (hd : a ≤ d) (t : PathTime) :
    affinePathTime a b (timeClip (rescalePathTime a b c) (rescalePathTime a b d) t) =
      timeClip c d (affinePathTime a b t) := by
  rw [affinePathTime_clip hab, affine_rescale_eq_clip hab, affine_rescale_eq_clip hab]
  have hm := affinePathTime_mem_Icc hab.le t
  change max (max a (min b c)) (min (max a (min b d)) _) = max c (min d _)
  rw [min_eq_right hc, min_max_distrib_right, min_eq_left hm.1,
    min_assoc, min_left_comm b d _, min_eq_right hm.2,
    ← max_assoc, max_right_comm a c a, max_self, max_assoc, max_left_comm a c _,
    max_eq_right (le_min hd hm.1)]

theorem rescalePathTime_monotone {a b : PathTime} (hab : a < b) :
    Monotone (rescalePathTime a b) := by
  intro s t hst
  change (rescalePathTime a b s : ℝ) ≤ (rescalePathTime a b t : ℝ)
  simp only [rescalePathTime_coe]
  apply max_le_max le_rfl
  apply min_le_min le_rfl
  exact div_le_div_of_nonneg_right (sub_le_sub_right (show (s : ℝ) ≤ t from hst) _) (sub_nonneg.mpr hab.le)

end CircleDomainRigidity

end

end OAI
