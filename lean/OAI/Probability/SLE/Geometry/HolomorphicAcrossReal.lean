import OAI.Probability.SLE.Geometry.RectangleCauchyBoundary

namespace OAI

/-! A continuous function holomorphic on both sides of the real line is
holomorphic across it, by splitting rectangular Cauchy integrals. -/
noncomputable section
open Complex Set
open scoped Topology Interval

namespace SLEExactGauge

lemma rectangle_differentiable_off_real {U : Set ℂ} {f : ℂ → ℂ} {z w : ℂ}
    (hf : ∀ a∈U, a.im≠0 → DifferentiableAt ℂ f a)
    (hzw : Rectangle z w⊆U)
    (hside : 0≤min z.im w.im ∨ max z.im w.im≤0) :
    DifferentiableOn ℂ f
      (Ioo (min z.re w.re) (max z.re w.re) ×ℂ Ioo (min z.im w.im) (max z.im w.im)) := by
  intro a ha
  have hac : a∈Rectangle z w := by
    change a.re∈Icc (min z.re w.re) (max z.re w.re) ∧
      a.im∈Icc (min z.im w.im) (max z.im w.im)
    exact ⟨⟨ha.1.1.le,ha.1.2.le⟩,⟨ha.2.1.le,ha.2.2.le⟩⟩
  have hane : a.im≠0 := by
    rcases hside with h | h
    · exact ne_of_gt (h.trans_lt ha.2.1)
    · exact ne_of_lt (ha.2.2.trans_le h)
  exact (hf a (hzw hac) hane).differentiableWithinAt

lemma rectangle_wedge_zero_one_side {U : Set ℂ} {f : ℂ → ℂ}
    (hC : ContinuousOn f U) (hf : ∀ a∈U, a.im≠0 → DifferentiableAt ℂ f a)
    {z w : ℂ} (hzw : Rectangle z w⊆U)
    (hside : 0≤min z.im w.im ∨ max z.im w.im≤0) :
    wedgeIntegral z w f+wedgeIntegral w z f=0 :=
  rectangle_wedge_eq_zero (hC.mono hzw) (rectangle_differentiable_off_real hf hzw hside)

theorem differentiableOn_of_continuousOn_off_real {U : Set ℂ} {f : ℂ → ℂ}
    (hU : IsOpen U) (hC : ContinuousOn f U)
    (hf : ∀ a∈U, a.im≠0 → DifferentiableAt ℂ f a) : DifferentiableOn ℂ f U := by
  apply (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp
  refine ⟨?_,hC⟩
  have hord (z w : ℂ) (hzw : Rectangle z w⊆U) (hle : z.im≤w.im) :
      wedgeIntegral z w f+wedgeIntegral w z f=0 := by
    by_cases hz : 0≤z.im
    · exact rectangle_wedge_zero_one_side hC hf hzw (Or.inl (by rwa [min_eq_left hle]))
    by_cases hw : w.im≤0
    · exact rectangle_wedge_zero_one_side hC hf hzw (Or.inr (by rwa [max_eq_right hle]))
    have hzn : z.im≤0 := (lt_of_not_ge hz).le
    have hwp : 0≤w.im := (lt_of_not_ge hw).le
    let zc : ℂ := ⟨z.re,0⟩
    let wc : ℂ := ⟨w.re,0⟩
    have hlow : Rectangle z wc⊆Rectangle z w := by
      intro a ha
      change a.re∈uIcc z.re w.re ∧ a.im∈uIcc z.im 0 at ha
      change a.re∈uIcc z.re w.re ∧ a.im∈uIcc z.im w.im
      rw [uIcc_of_le hzn] at ha
      rw [uIcc_of_le hle]
      exact ⟨ha.1,⟨ha.2.1,ha.2.2.trans hwp⟩⟩
    have hupp : Rectangle zc w⊆Rectangle z w := by
      intro a ha
      change a.re∈uIcc z.re w.re ∧ a.im∈uIcc 0 w.im at ha
      change a.re∈uIcc z.re w.re ∧ a.im∈uIcc z.im w.im
      rw [uIcc_of_le hwp] at ha
      rw [uIcc_of_le hle]
      exact ⟨ha.1,⟨hzn.trans ha.2.1,ha.2.2⟩⟩
    have hl := rectangle_wedge_zero_one_side hC hf (hlow.trans hzw)
      (Or.inr (show max z.im wc.im≤0 from by simpa only [wc,max_le_iff] using And.intro hzn le_rfl))
    have hu := rectangle_wedge_zero_one_side hC hf (hupp.trans hzw)
      (Or.inl (show 0≤min zc.im w.im from by simpa only [zc,le_min_iff] using And.intro le_rfl hwp))
    have hcut : (0:ℝ)∈uIcc z.im w.im := by rw [uIcc_of_le hle]; exact ⟨hzn,hwp⟩
    rw [rectangle_wedge_split_of_continuous (hC.mono hzw) hcut]
    rw [hl,hu,add_zero]
  intro z w hzw
  rw [← add_eq_zero_iff_eq_neg]
  by_cases hle : z.im≤w.im
  · exact hord z w hzw hle
  · have hrev : Rectangle w z⊆U := by
      intro a ha
      apply hzw
      change a.re∈uIcc z.re w.re ∧ a.im∈uIcc z.im w.im
      change a.re∈uIcc w.re z.re ∧ a.im∈uIcc w.im z.im at ha
      simpa only [uIcc_comm] using ha
    simpa only [add_comm] using hord w z hrev (le_of_not_ge hle)

end SLEExactGauge

end

end OAI
