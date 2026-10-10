import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevForwardDuhamel
import OAI.MathematicalPhysics.DefocusingNLS.Nonlinear.MaximalStrongSolution

namespace OAI

/-! # Forward strong solutions are restrictions of the maximal flow

The local backward branch is glued using the right derivative provided by
the endpoint Duhamel identity.  The forward input needs no derivative at zero.
-/

open Filter Topology Set

namespace DefocusingNLS

theorem forwardStrongSobolevSolution_restricts_maximal
    (k : ℝ) (hk : 6 < k) (m : ℕ) (u : ℝ → FourierL2) (T : ℝ) (hT : 0 < T)
    (huc : ContinuousOn u (Icc 0 T))
    (hu : ∀ t ∈ Ioo 0 T, HasDerivAt (fun s => lowerSobolevInclusion (u s))
      (lowerSobolevGenerator (u t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k hk m (u t))) t) :
    Ico 0 T ⊆ maximalSobolevInteractionDomain k hk m (u 0) ∧
      EqOn u (maximalSobolevSchrodingerFlow k hk m (u 0)) (Ico 0 T) := by
  obtain ⟨P⟩ := sobolevInteractionPatch_nonempty k hk m (u 0)
  let v := inverseSchrodingerCurve u
  let w := fun t => if t ≤ 0 then P.curve t else v t
  have hv0 : v 0 = u 0 := by simp [v, inverseSchrodingerCurve]
  have hw0 : w 0 = u 0 := by simp [w, P.initial]
  have hright := hasDerivWithinAt_inverseSchrodingerCurve_zero k hk m u T hT huc hu
  change HasDerivWithinAt v (schrodingerInteractionField k hk m 0 (v 0)) (Ici 0) 0 at hright
  have hwleft : HasDerivWithinAt w
      (schrodingerInteractionField k hk m 0 (u 0)) (Iic 0) 0 := by
    have h := (P.solves 0 ⟨P.left_neg, P.right_pos⟩).hasDerivWithinAt (s := Iic 0)
    rw [P.initial] at h
    apply h.congr_of_mem
    · intro t ht
      change t ≤ 0 at ht
      simp only [w, ite_eq_left ht]
    · simp
  have hwright : HasDerivWithinAt w
      (schrodingerInteractionField k hk m 0 (u 0)) (Ici 0) 0 := by
    rw [hv0] at hright
    apply hright.congr_of_mem
    · intro t ht
      by_cases ht0 : t ≤ 0
      · have he : t = 0 := le_antisymm ht0 ht
        subst t
        simp [w, P.initial, hv0]
      · simp only [w, ite_eq_right ht0]
    · simp
  have hwd0 : HasDerivAt w (schrodingerInteractionField k hk m 0 (u 0)) 0 := by
    simpa only [Iic_union_Ici, hasDerivWithinAt_univ] using hwleft.union hwright
  have hwd : ∀ t ∈ Ioo P.left T, HasDerivAt w
      (schrodingerInteractionField k hk m t (w t)) t := by
    intro t ht
    rcases lt_trichotomy t 0 with hneg | heq | hpos
    · have he : w =ᶠ[𝓝 t] P.curve := by
        filter_upwards [isOpen_Iio.mem_nhds hneg] with s hs
        change s < 0 at hs
        simp only [w, ite_eq_left hs.le]
      rw [show w t = P.curve t by simp only [w, ite_eq_left hneg.le]]
      exact (P.solves t ⟨ht.1, hneg.trans P.right_pos⟩).congr_of_eventuallyEq he
    · subst t
      simpa only [hw0] using hwd0
    · have he : w =ᶠ[𝓝 t] v := by
        filter_upwards [isOpen_Ioi.mem_nhds hpos] with s hs
        change 0 < s at hs
        simp only [w, ite_eq_right (not_le_of_gt hs)]
      rw [show w t = v t by simp only [w, ite_eq_right (not_le_of_gt hpos)]]
      exact (hasDerivAt_inverseSchrodingerCurve k hk m u 0 T t
        (huc.mono Ioo_subset_Icc_self) hu ⟨hpos, ht.2⟩).congr_of_eventuallyEq he
  let Q : SobolevInteractionPatch k hk m (u 0) :=
    { left := P.left
      right := T
      left_neg := P.left_neg
      right_pos := hT
      curve := w
      initial := hw0
      solves := hwd }
  refine ⟨fun t ht => Q.subset_maximalDomain ⟨P.left_neg.trans_le ht.1, ht.2⟩, ?_⟩
  intro t ht
  change u t = schrodingerFlow t (maximalSobolevInteractionFlow k hk m (u 0) t)
  rw [maximalSobolevInteractionFlow_eq_patch Q ⟨P.left_neg.trans_le ht.1, ht.2⟩]
  have hwv : w t = v t := by
    by_cases ht0 : t ≤ 0
    · have he : t = 0 := le_antisymm ht0 ht.1
      subst t
      simp [w, P.initial, hv0]
    · simp only [w, ite_eq_right ht0]
  change u t = schrodingerFlow t (w t)
  rw [hwv]
  simp [v, inverseSchrodingerCurve, ← schrodingerFlow_add]

end DefocusingNLS

end OAI
