import Mathlib.Topology.Order.Compact
import OAI.Geometry.NodalSets.Elliptic.CorrugationPeriodicCell

namespace OAI

namespace Yau.Geometry
open Real Set Metric
noncomputable section

lemma centered_integer_representative (x : ℝ) :
    |x-(⌊x+(1/2:ℝ)⌋:ℤ)| ≤ 1/2 := by
  have h1 := Int.floor_le (x+(1/2:ℝ))
  have h2 := Int.lt_floor_add_one (x+(1/2:ℝ))
  rw [abs_le]
  constructor <;> linarith

lemma corrugationPeriodicWell_representative (a : ℝ) (z : ℝ × ℝ) :
    ∃ w : ℝ × ℝ, |w.1| ≤ 1/2 ∧ |w.2| ≤ 1/2 ∧
      corrugationPeriodicWell a z = corrugationDiskWell a (1/4) w := by
  let m : ℤ × ℤ := (⌊z.1+(1/2:ℝ)⌋,⌊z.2+(1/2:ℝ)⌋)
  let w : ℝ × ℝ := (z.1-(m.1:ℝ),z.2-(m.2:ℝ))
  have h1 : |w.1| ≤ 1/2 := centered_integer_representative z.1
  have h2 : |w.2| ≤ 1/2 := centered_integer_representative z.2
  refine ⟨w,h1,h2,?_⟩
  have he : (w.1+(m.1:ℝ),w.2+(m.2:ℝ))=z := by dsimp [w]; simp
  rw [← corrugationPeriodicWell_cell a w h1 h2,← corrugationPeriodicWell_periodic a m w,he]

theorem corrugationPeriodicWell_bounded (a : ℝ) :
    ∃ B : ℝ, 0 < B ∧ ∀ z, |corrugationPeriodicWell a z| ≤ B := by
  obtain ⟨B,hB⟩ := ((corrugationDiskWell_smooth a (1/4)).continuous.norm).bddAbove_range_of_hasCompactSupport
    ((corrugationDiskWell_compactSupport a (show (0:ℝ) ≤ 1/4 by norm_num)).norm)
  refine ⟨max B 0+1,by positivity,?_⟩
  intro z
  obtain ⟨w,_,_,hw⟩ := corrugationPeriodicWell_representative a z
  rw [hw]
  have hb := hB ⟨w,rfl⟩
  have hm := le_max_left B 0
  simpa only [Real.norm_eq_abs] using (hb.trans (by linarith : B ≤ max B 0+1))

end
end Yau.Geometry

end OAI
