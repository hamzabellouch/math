import OAI.Analysis.PlanarPacking.BarrierEndpoints

namespace OAI

namespace SharpPlanar
open Set
lemma dividedP_lower (a : ℕ) (ha : a ∈ residues) {u : ℝ}
    (hu : u ∈ Icc (-leftHalf a) (rightHalf a)) : (17/25:ℝ) ≤ dividedP a u := by
  have hpos := half_pos a ha
  have hend := barrier_endpoints a ha
  have hcenter : (17/25:ℝ) ≤ dividedP a 0 := by
    rw [dividedP_zero a (residue_lt ha)]
    have hh := Q_lower a (by simpa only [Nat.mod_eq_of_lt (residue_lt ha)] using ha)
    linarith
  by_cases hu0 : u ≤ 0
  · have hab : -leftHalf a ≤ (0:ℝ) := by linarith
    have hsub : Icc (-leftHalf a) 0 ⊆ Icc (-leftHalf a) (rightHalf a) := by
      intro v hv
      exact ⟨hv.1, le_trans hv.2 hpos.2.le⟩
    have hc := dividedP_log_concave a ha (convex_Icc _ _) hsub (by simp [interior_Icc])
    apply lower_of_log_concave (v := -leftHalf a) (w := 0) (by norm_num)
    · simpa only [uIcc_of_le hab] using fun v hv => dividedP_pos a ha (hsub hv)
    · simpa only [uIcc_of_le hab] using hc
    · exact hend.1
    · exact hcenter
    · simpa only [uIcc_of_le hab] using show u ∈ Icc (-leftHalf a) 0 from ⟨hu.1,hu0⟩
  · have hab : (0:ℝ) ≤ rightHalf a := hpos.2.le
    have hsub : Icc 0 (rightHalf a) ⊆ Icc (-leftHalf a) (rightHalf a) := by
      intro v hv
      exact ⟨le_trans (by linarith) hv.1,hv.2⟩
    have hc := dividedP_log_concave a ha (convex_Icc _ _) hsub (by simp [interior_Icc])
    apply lower_of_log_concave (v := 0) (w := rightHalf a) (by norm_num)
    · simpa only [uIcc_of_le hab] using fun v hv => dividedP_pos a ha (hsub hv)
    · simpa only [uIcc_of_le hab] using hc
    · exact hcenter
    · exact hend.2
    · simpa only [uIcc_of_le hab] using show u ∈ Icc 0 (rightHalf a) from ⟨by linarith,hu.2⟩


def zeroGrid (m : ℝ) : Prop := ∃ k : ℤ, ∃ a ∈ residues, m=12*(k:ℝ)+(a:ℝ)
lemma zeroGrid_shift {m : ℝ} (hm : zeroGrid m) (j : ℤ) : zeroGrid (12*(j:ℝ)+m) := by
  rcases hm with ⟨k,a,ha,rfl⟩
  refine ⟨j+k,a,ha,?_⟩
  push_cast
  ring
lemma neighboring_zeros (a : ℕ) (ha : a ∈ residues) :
    zeroGrid ((a:ℝ)-2*leftHalf a) ∧ zeroGrid ((a:ℝ)+2*rightHalf a) := by
  simp only [residues,Finset.mem_insert,Finset.mem_singleton] at ha
  rcases ha with rfl|rfl|rfl|rfl|rfl|rfl
  · constructor
    · exact ⟨-1,9,by decide,by norm_num [leftHalf]⟩
    · exact ⟨0,1,by decide,by norm_num [rightHalf]⟩
  · constructor
    · exact ⟨0,0,by decide,by norm_num [leftHalf]⟩
    · exact ⟨0,3,by decide,by norm_num [rightHalf]⟩
  · constructor
    · exact ⟨0,1,by decide,by norm_num [leftHalf]⟩
    · exact ⟨0,4,by decide,by norm_num [rightHalf]⟩
  · constructor
    · exact ⟨0,3,by decide,by norm_num [leftHalf]⟩
    · exact ⟨0,7,by decide,by norm_num [rightHalf]⟩
  · constructor
    · exact ⟨0,4,by decide,by norm_num [leftHalf]⟩
    · exact ⟨0,9,by decide,by norm_num [rightHalf]⟩
  · constructor
    · exact ⟨0,7,by decide,by norm_num [leftHalf]⟩
    · exact ⟨1,0,by decide,by norm_num [rightHalf]⟩


theorem P_nearest_lower (s m : ℝ) (hm : zeroGrid m)
    (hnear : ∀ n : ℝ, zeroGrid n → |s-m| ≤ |s-n|) : (17/25:ℝ)*(s-m)^2 ≤ P s := by
  rcases hm with ⟨k,a,ha,rfl⟩
  have hl := hnear _ (zeroGrid_shift (neighboring_zeros a ha).1 k)
  have hr := hnear _ (zeroGrid_shift (neighboring_zeros a ha).2 k)
  have hls := sq_le_sq.mpr hl
  have hrs := sq_le_sq.mpr hr
  have hp := half_pos a ha
  have hu : s-(12*(k:ℝ)+a) ∈ Icc (-leftHalf a) (rightHalf a) := by
    constructor <;> nlinarith
  have hv := dividedP_lower a ha hu
  have hf := dividedP_factor a ha (s-(12*(k:ℝ)+a))
  have hperiod : P (a+(s-(12*(k:ℝ)+a)))=P s := by
    convert (show Function.Periodic P (12:ℝ) from P_period).sub_int_mul_eq k (x := s) using 1
    congr 1
    ring
  rw [hperiod] at hf
  nlinarith [mul_nonneg (sq_nonneg (s-(12*(k:ℝ)+a))) (sub_nonneg.mpr hv)]
end SharpPlanar

end OAI
