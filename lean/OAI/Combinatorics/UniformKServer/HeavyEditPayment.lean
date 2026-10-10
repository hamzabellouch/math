import Mathlib
import OAI.Combinatorics.UniformKServer.HeavyRecordGeometry
import OAI.Combinatorics.UniformKServer.HeavyEditRamp

namespace OAI

                                       
section

/-! The literal [9,10] auxiliary potential pays heavy-label edits (§07,
Heavy edits). These are pointwise inequalities before any posterior averaging. -/
noncomputable section
namespace UniformKServer.HeavyRecords
open Finset HeavyEditRamp
open scoped Classical
variable {X Λ : Type*} [Fintype X] [MetricSpace X] [Fintype Λ] {r : ℝ}

def editCharge (S T : State X Λ r) (p : X) : ℝ := if key S p ≠ key T p then r else 0

omit [Fintype X] in
theorem editCharge_bounds (S T : State X Λ r) (hr : 0 ≤ r) (p : X) :
    editCharge S T p ∈ Set.Icc 0 r := by
  unfold editCharge
  split_ifs <;> constructor <;> linarith

omit [Fintype X] in
theorem inner_edit_payment (S : State X Λ r) (hr : 0 < r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present)
    (p : X) (hd : dist p x ≤ 3*r) :
    editCharge S (insert S hr.le x R hR fresh hf) p+
      r*(parameter r (centers (insert S hr.le x R hR fresh hf)) p-parameter r (centers S) p) ≤ 0 := by
  rw [centers_insert,HeavyEditRamp.update_zero r hr _ x p (by linarith)]
  by_cases hc : ∃ c ∈ centers S, dist p c ≤ 10*r
  · obtain ⟨c,hc,hpc⟩ := hc
    obtain ⟨l,hl,rfl⟩ := mem_image.mp hc
    have hcov : covers S l p := by
      refine ⟨hl,?_⟩
      rw [dist_comm] at hpc
      linarith [(S.radius_bounds l hl).1]
    have he := common_region_reused S hr.le x R hR fresh hf p l hcov (by rw [dist_comm]; linarith [hR.1])
    rw [editCharge,ite_eq_right (not_not.mpr he.symm)]
    nlinarith [(parameter_bounds r (centers S) p).1]
  · have ho : parameter r (centers S) p=1 := by
      apply far_one r hr
      intro c hc'
      exact (lt_of_not_ge (fun h => hc ⟨c,hc',h⟩)).le
    rw [ho]
    linarith [(editCharge_bounds S (insert S hr.le x R hR fresh hf) hr.le p).2]

omit [Fintype X] in
theorem stationary_edit_payment (S : State X Λ r) (hr : 0 < r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present) (p : X) :
    editCharge S (insert S hr.le x R hR fresh hf) p+
      r*(parameter r (centers (insert S hr.le x R hR fresh hf)) p-parameter r (centers S) p) ≤
      if 3*r < dist p x ∧ dist p x ≤ 120*r then 2*r else 0 := by
  by_cases hi : dist p x ≤ 3*r
  · rw [ite_eq_right (fun h => (not_lt_of_ge hi) h.1)]
    exact inner_edit_payment S hr x R hR fresh hf p hi
  · by_cases ho : dist p x ≤ 120*r
    · rw [ite_eq_left ⟨lt_of_not_ge hi,ho⟩]
      have hc := (editCharge_bounds S (insert S hr.le x R hR fresh hf) hr.le p).2
      have hp := parameter_bounds r (centers (insert S hr.le x R hR fresh hf)) p
      have hq := parameter_bounds r (centers S) p
      nlinarith [hp.1,hp.2,hq.1,hq.2]
    · rw [ite_eq_right (fun h => ho h.2)]
      have hd : 120*r < dist x p := by rw [dist_comm]; exact lt_of_not_ge ho
      have he := unchanged_far S hr.le x R hR fresh hf p hd
      rw [editCharge,ite_eq_right (not_not.mpr he.symm),centers_insert]
      have hm := HeavyEditRamp.update_far r hr (centers S) x p (by rw [dist_comm] at hd; linarith)
      nlinarith

omit [Fintype X] in
theorem mover_edit_payment (S : State X Λ r) (hr : 0 < r) (x : X) (R : ℝ)
    (hR : R ∈ Set.Icc (16*r) (20*r)) (fresh : Λ) (hf : fresh ∉ S.present) (y : X) :
    editCharge S (insert S hr.le x R hR fresh hf) y+
      r*(parameter r (centers (insert S hr.le x R hR fresh hf)) x-parameter r (centers S) y) ≤
      if 3*r < dist y x then r else 0 := by
  have hz : parameter r (centers (insert S hr.le x R hR fresh hf)) x=0 := by
    rw [centers_insert]
    exact HeavyEditRamp.update_zero r hr _ x x (by rw [dist_self]; positivity)
  by_cases hi : dist y x ≤ 3*r
  · rw [ite_eq_right (not_lt_of_ge hi)]
    have hp := inner_edit_payment S hr x R hR fresh hf y hi
    have hy : parameter r (centers (insert S hr.le x R hR fresh hf)) y=0 := by
      rw [centers_insert]
      exact HeavyEditRamp.update_zero r hr _ x y (by linarith)
    simpa only [hz,hy] using hp
  · rw [ite_eq_left (lt_of_not_ge hi),hz]
    nlinarith [(editCharge_bounds S (insert S hr.le x R hR fresh hf) hr.le y).2,
      (parameter_bounds r (centers S) y).1]

end UniformKServer.HeavyRecords

end


end

end OAI
