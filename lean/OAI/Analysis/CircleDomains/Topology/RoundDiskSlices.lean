import OAI.Analysis.CircleDomains.Topology.ParallelDiskTolls

namespace OAI

/-!
# Horizontal chords of round complementary disks

The exact real interval cut out by a round disk is used to enumerate the
holes of a chosen crossing segment. The formula includes tangent and
radius-zero disks.
-/

open Set Function Metric

namespace CircleDomainRigidity

noncomputable def horizontalChord (c : ℂ) (r y : ℝ) : ℝ × ℝ :=
  (c.re - Real.sqrt (r ^ 2 - (y - c.im) ^ 2),
   c.re + Real.sqrt (r ^ 2 - (y - c.im) ^ 2))

theorem horizontalChord_nonneg (c : ℂ) {r y : ℝ} (hr : 0 ≤ r)
    (hy : y ∈ Icc (c.im - r) (c.im + r)) :
    0 ≤ r ^ 2 - (y - c.im) ^ 2 := by
  have h : |y - c.im| ≤ r := abs_le.mpr ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hs := (sq_le_sq₀ (abs_nonneg (y - c.im)) hr).mpr h
  nlinarith [sq_abs (y - c.im)]

theorem horizontalChord_valid (c : ℂ) (r y : ℝ) :
    (horizontalChord c r y).1 ≤ (horizontalChord c r y).2 := by
  dsimp [horizontalChord]
  linarith [Real.sqrt_nonneg (r ^ 2 - (y - c.im) ^ 2)]

theorem mem_closedBall_iff_mem_horizontalChord (c : ℂ) {r y x : ℝ}
    (hr : 0 ≤ r) (hy : y ∈ Icc (c.im - r) (c.im + r)) :
    (⟨x, y⟩ : ℂ) ∈ closedBall c r ↔
      x ∈ Icc (horizontalChord c r y).1 (horizontalChord c r y).2 := by
  have hsq := Real.sq_sqrt (horizontalChord_nonneg c hr hy)
  have hsqrt := Real.sqrt_nonneg (r ^ 2 - (y - c.im) ^ 2)
  have hn := Complex.sq_norm ((⟨x, y⟩ : ℂ) - c)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im] at hn
  dsimp only [horizontalChord, Prod.fst, Prod.snd]
  rw [mem_closedBall, dist_eq_norm]
  constructor
  · intro h
    have hnorm := norm_nonneg ((⟨x, y⟩ : ℂ) - c)
    have hbound : (x - c.re) ^ 2 ≤ r ^ 2 - (y - c.im) ^ 2 := by nlinarith
    constructor <;> nlinarith [sq_nonneg (x - c.re - Real.sqrt (r ^ 2 - (y - c.im) ^ 2)),
      sq_nonneg (x - c.re + Real.sqrt (r ^ 2 - (y - c.im) ^ 2))]
  · rintro ⟨hx1, hx2⟩
    have hbound : (x - c.re) ^ 2 ≤ r ^ 2 - (y - c.im) ^ 2 := by nlinarith
    nlinarith [norm_nonneg ((⟨x, y⟩ : ℂ) - c)]

theorem horizontalChord_disjoint {c d : ℂ} {r s y : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hyc : y ∈ Icc (c.im - r) (c.im + r))
    (hyd : y ∈ Icc (d.im - s) (d.im + s))
    (hdisj : Disjoint (closedBall c r) (closedBall d s)) :
    Disjoint (Icc (horizontalChord c r y).1 (horizontalChord c r y).2)
      (Icc (horizontalChord d s y).1 (horizontalChord d s y).2) := by
  apply disjoint_left.mpr
  intro x hxc hxd
  exact disjoint_left.mp hdisj
    ((mem_closedBall_iff_mem_horizontalChord c hr hyc).mpr hxc)
    ((mem_closedBall_iff_mem_horizontalChord d hs hyd).mpr hxd)

theorem horizontalChord_inside_segment {c : ℂ} {r y a b : ℝ}
    (hr : 0 ≤ r) (hy : y ∈ Icc (c.im - r) (c.im + r))
    (ha : (⟨a, y⟩ : ℂ) ∉ closedBall c r)
    (hb : (⟨b, y⟩ : ℂ) ∉ closedBall c r)
    (hinter : (Icc a b ∩ Icc (horizontalChord c r y).1
      (horizontalChord c r y).2).Nonempty) :
    a < (horizontalChord c r y).1 ∧ (horizontalChord c r y).2 < b := by
  rw [mem_closedBall_iff_mem_horizontalChord c hr hy] at ha hb
  obtain ⟨x, hx, hx'⟩ := hinter
  constructor
  · by_contra h
    exact ha ⟨le_of_not_gt h, hx.1.trans hx'.2⟩
  · by_contra h
    exact hb ⟨hx'.1.trans hx.2, le_of_not_gt h⟩

end CircleDomainRigidity

end OAI
