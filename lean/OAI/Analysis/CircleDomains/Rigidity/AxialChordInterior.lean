import OAI.Analysis.CircleDomains.Rigidity.AxialChordGeometry

namespace OAI

/-! Strict disk membership corresponds to the open chord interval. -/
open Set Function Metric
noncomputable section
namespace CircleDomainRigidity

 theorem mem_ball_iff_mem_horizontalChord (c : ℂ) {r y x : ℝ}
    (hr : 0 ≤ r) (hy : y ∈ Icc (c.im-r) (c.im+r)) :
    (⟨x,y⟩ : ℂ) ∈ ball c r ↔
      x ∈ Ioo (horizontalChord c r y).1 (horizontalChord c r y).2 := by
  have hsq := Real.sq_sqrt (horizontalChord_nonneg c hr hy)
  have hsqrt := Real.sqrt_nonneg (r^2-(y-c.im)^2)
  have hn := Complex.sq_norm ((⟨x,y⟩ : ℂ)-c)
  simp only [Complex.normSq_apply,Complex.sub_re,Complex.sub_im] at hn
  dsimp only [horizontalChord,Prod.fst,Prod.snd]
  rw [mem_ball,dist_eq_norm]
  constructor
  · intro h
    have hbound : (x-c.re)^2 < r^2-(y-c.im)^2 := by nlinarith [norm_nonneg ((⟨x,y⟩ : ℂ)-c)]
    constructor <;> nlinarith [sq_nonneg (x-c.re-Real.sqrt (r^2-(y-c.im)^2)),
      sq_nonneg (x-c.re+Real.sqrt (r^2-(y-c.im)^2))]
  · rintro ⟨hx,hx'⟩
    have hbound : (x-c.re)^2 < r^2-(y-c.im)^2 := by
      nlinarith [mul_pos (show 0 < x-c.re+Real.sqrt (r^2-(y-c.im)^2) by linarith)
        (show 0 < Real.sqrt (r^2-(y-c.im)^2)-(x-c.re) by linarith)]
    nlinarith [norm_nonneg ((⟨x,y⟩ : ℂ)-c)]

 theorem mem_ball_iff_mem_axialChord (i : Fin 2) (c : ℂ) {r y x : ℝ}
    (hr : 0 ≤ r) (hy : y ∈ Icc (transverseCoordinate i c-r) (transverseCoordinate i c+r)) :
    complexCoordinateLine i y x ∈ ball c r ↔
      x ∈ Ioo (axialChord i c r y).1 (axialChord i c r y).2 := by
  have hd := axialSwap_dist i (complexCoordinateLine i y x) c
  rw [axialSwap_line] at hd
  change dist (complexCoordinateLine i y x) c < r ↔ _
  rw [← hd]
  exact mem_ball_iff_mem_horizontalChord _ hr (by simpa only [axialSwap_im] using hy)

end CircleDomainRigidity

end

end OAI
