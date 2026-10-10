import OAI.MathematicalPhysics.DefocusingNLS.Linear.ExpandingPhysicalEquation
import OAI.MathematicalPhysics.DefocusingNLS.Linear.SobolevForwardMaximal

namespace OAI

/-! # The constructed moving-scale solution belongs to the maximal physical flow -/

open Set Filter Topology

namespace DefocusingNLS

theorem strictMono_expandingFreeTime (L : ℝ) (hL : 0 < L) :
    StrictMono (expandingFreeTime L) := by
  intro s t hst
  unfold expandingFreeTime
  apply mul_lt_mul_of_pos_left _ (Real.rpow_pos_of_pos hL _)
  have he := Real.exp_lt_exp.mpr (neg_lt_neg hst)
  linarith

theorem expanding_clock_denominator_pos (L S t : ℝ) (hL : 0 < L)
    (ht : t ≤ expandingFreeTime L S) : 0 < 1 - L ^ 2 * t := by
  have hc : L ^ 2 * L ^ (-2 : ℝ) = 1 := by
    rw [← Real.rpow_two, ← Real.rpow_add hL]
    norm_num
  have he : 1 - L ^ 2 * expandingFreeTime L S = Real.exp (-S) := by
    unfold expandingFreeTime
    rw [← mul_assoc, hc]
    ring
  have hle := mul_le_mul_of_nonneg_left ht (sq_nonneg L)
  linarith [Real.exp_pos (-S)]

theorem expandingInverseClock_mem_Icc (L S t : ℝ) (hL : 0 < L)
    (ht : t ∈ Icc 0 (expandingFreeTime L S)) : expandingInverseClock L t ∈ Icc 0 S := by
  have hd := expanding_clock_denominator_pos L S t hL ht.2
  have he := expandingFreeTime_inverseClock L t hL hd
  have hm := strictMono_expandingFreeTime L hL
  constructor
  · apply hm.le_iff_le.mp
    rw [he]
    simpa only [expandingFreeTime, neg_zero, Real.exp_zero, sub_self, mul_zero] using ht.1
  · apply hm.le_iff_le.mp
    simpa only [he] using ht.2

theorem expandingInverseClock_mem_Ioo (L S t : ℝ) (hL : 0 < L)
    (ht : t ∈ Ioo 0 (expandingFreeTime L S)) : expandingInverseClock L t ∈ Ioo 0 S := by
  have hd := expanding_clock_denominator_pos L S t hL ht.2.le
  have he := expandingFreeTime_inverseClock L t hL hd
  have hm := strictMono_expandingFreeTime L hL
  constructor
  · apply hm.lt_iff_lt.mp
    rw [he]
    simpa only [expandingFreeTime, neg_zero, Real.exp_zero, sub_self, mul_zero] using ht.1
  · apply hm.lt_iff_lt.mp
    simpa only [he] using ht.2

noncomputable def expandingSchrodingerTrajectory (a b k L S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hS : 0 ≤ S)
    (u : C(Icc (0 : ℝ) S, FourierL2)) (t : ℝ) : FourierL2 :=
  expandingPhysicalAmplitude a b L (expandingInverseClock L t) •
    expandingToSobolev a k ha1 hk
      (expandingPhysicalPath a k L S ha hk hL u (projIcc 0 S hS (expandingInverseClock L t)))

theorem expandingSchrodingerTrajectory_zero (a b k L S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hS : 0 ≤ S)
    (u : C(Icc (0 : ℝ) S, FourierL2)) :
    expandingSchrodingerTrajectory a b k L S ha ha1 hk hL hS u 0 =
      ((L ^ (2 * a) : ℝ) : ℂ) • expandingToSobolev a k ha1 hk
        (expandingInverseTransfer a k L ha hk hL (u ⟨0, le_rfl, hS⟩)) := by
  simp [expandingSchrodingerTrajectory, expandingInverseClock, expandingPhysicalAmplitude,
    expandingFreeAmplitude, expandingPhysicalPath, expandingRadius]

theorem continuousOn_expandingSchrodingerTrajectory (a b k L S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hS : 0 ≤ S)
    (u : C(Icc (0 : ℝ) S, FourierL2)) :
    ContinuousOn (expandingSchrodingerTrajectory a b k L S ha ha1 hk hL hS u)
      (Icc 0 (expandingFreeTime L S)) := by
  have hLp : 0 < L := by linarith
  have hc : ContinuousOn (expandingInverseClock L) (Icc 0 (expandingFreeTime L S)) := by
    have hb : Continuous (fun t : ℝ => 1 - L ^ 2 * t) := by fun_prop
    exact (hb.continuousOn.log (fun t ht =>
      (expanding_clock_denominator_pos L S t hLp ht.2).ne')).neg
  have hA : Continuous (expandingPhysicalAmplitude a b L) :=
    continuous_iff_continuousAt.mpr (fun s =>
      (hasDerivAt_expandingPhysicalAmplitude a b L s).continuousAt)
  have hV : Continuous (fun s => expandingToSobolev a k ha1 hk
      (expandingPhysicalPath a k L S ha hk hL u (projIcc 0 S hS s))) :=
    (expandingToSobolev a k ha1 hk).continuous.comp
      ((expandingPhysicalPath a k L S ha hk hL u).continuous.comp continuous_projIcc)
  exact (hA.comp_continuousOn hc).smul (hV.comp_continuousOn hc)

theorem hasDerivAt_expandingSchrodingerTrajectory (a b k L S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hS : 0 ≤ S)
    (m : ℕ) (ham : 2 * a * m = 1)
    (u : C(Icc (0 : ℝ) S, FourierL2)) (u₀ : FourierL2)
    (hu : u = expandingPicard a b k L S ha hk hL hS
      (expandingNonlinearReaction a k L S ha ha1 hk hL m) u₀ u)
    (t : ℝ) (ht : t ∈ Ioo 0 (expandingFreeTime L S)) :
    HasDerivAt (fun s => lowerSobolevInclusion
      (expandingSchrodingerTrajectory a b k L S ha ha1 hk hL hS u s))
      (lowerSobolevGenerator (expandingSchrodingerTrajectory a b k L S ha ha1 hk hL hS u t) -
        Complex.I • lowerSobolevInclusion (sobolevOddPower k (by linarith) m
          (expandingSchrodingerTrajectory a b k L S ha ha1 hk hL hS u t))) t := by
  have hLp : 0 < L := by linarith
  have hs := expandingInverseClock_mem_Ioo L S t hLp ht
  let v : ℝ → FourierL2 := fun s => expandingToSobolev a k ha1 hk
    (expandingPhysicalPath a k L S ha hk hL u (projIcc 0 S hS s))
  have hv := hasDerivAt_expandingNonlinearMild_sobolev a b k L S ha ha1 hk hL hS m u u₀ hu
    (expandingInverseClock L t) hs
  change HasDerivAt (fun s => lowerSobolevInclusion (v s))
    ((-(a : ℂ) + Complex.I * b) • lowerSobolevInclusion (v (expandingInverseClock L t)) +
      (L ^ (-2 : ℝ) * Real.exp (-expandingInverseClock L t)) •
        lowerSobolevGenerator (v (expandingInverseClock L t)) +
      (-Complex.I) • lowerSobolevInclusion
        (sobolevOddPower k (by linarith) m (v (expandingInverseClock L t))))
    (expandingInverseClock L t) at hv
  have h := hasDerivAt_expandingPhysicalEquation a b k L (by linarith) hLp m ham v t
    (expanding_clock_denominator_pos L S t hLp ht.2.le)
    hv
  exact h

/-- The actual Picard trajectory, after exact time/amplitude/weight conversion,
is the unique maximal Sobolev Schrödinger solution on its forward slab. -/
theorem expandingSchrodingerTrajectory_eq_maximal (a b k L S : ℝ)
    (ha : 0 < a) (ha1 : a < 1) (hk : 8 < k) (hL : 1 ≤ L) (hS : 0 < S)
    (m : ℕ) (ham : 2 * a * m = 1)
    (u : C(Icc (0 : ℝ) S, FourierL2)) (u₀ : FourierL2)
    (hu : u = expandingPicard a b k L S ha hk hL hS.le
      (expandingNonlinearReaction a k L S ha ha1 hk hL m) u₀ u) :
    let U := expandingSchrodingerTrajectory a b k L S ha ha1 hk hL hS.le u
    Ico 0 (expandingFreeTime L S) ⊆ maximalSobolevInteractionDomain k (by linarith) m (U 0) ∧
      EqOn U (maximalSobolevSchrodingerFlow k (by linarith) m (U 0))
        (Ico 0 (expandingFreeTime L S)) := by
  intro U
  have htime : 0 < expandingFreeTime L S := by
    have h := strictMono_expandingFreeTime L (by linarith) hS
    simpa only [expandingFreeTime, neg_zero, Real.exp_zero, sub_self, mul_zero] using h
  exact forwardStrongSobolevSolution_restricts_maximal k (by linarith) m U _ htime
    (continuousOn_expandingSchrodingerTrajectory a b k L S ha ha1 hk hL hS.le u)
    (fun t ht => hasDerivAt_expandingSchrodingerTrajectory a b k L S ha ha1 hk hL hS.le
      m ham u u₀ hu t ht)

end DefocusingNLS

end OAI
