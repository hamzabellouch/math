import OAI.MeasureTheory.Falconer.Estimates.CoarsePlanarRounding

namespace OAI

/-! Incident coarse pencils use a common grid. Their global union is
controlled by thirteen translates of the original coarse grid cover. -/
namespace Falconer
attribute [local instance] Classical.propDecidable

theorem moved_point_residual {δ Δ : ℝ} (hδ : 0 ≤ δ) (_hΔ : 0 < Δ) (hδΔ : δ ≤ Δ)
    (p c l : Space 2) (hc : dist p c ≤ Δ) (hl0 : |l 0| ≤ 1)
    (hi : TubeIncident δ p l) : |c 1-l 0*c 0-l 1| ≤ 4*Δ := by
  have hres := tube_residual_le hδ hl0 hi
  have h0 : |p 0-c 0| ≤ Δ := (show |p 0-c 0| ≤ dist p c by
    simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 0).trans hc
  have h1 : |c 1-p 1| ≤ Δ := by
    rw [abs_sub_comm]
    exact (show |p 1-c 1| ≤ dist p c by simpa only [Real.dist_eq] using PiLp.dist_apply_le p c 1).trans hc
  have h2 : |l 0*(p 0-c 0)| ≤ Δ := by
    rw [abs_mul]
    exact (mul_le_mul hl0 h0 (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)).trans_eq (one_mul _)
  calc
    _ = |(p 1-l 0*p 0-l 1)+(c 1-p 1)+l 0*(p 0-c 0)| := by congr 1; ring
    _ ≤ |(p 1-l 0*p 0-l 1)+(c 1-p 1)|+|l 0*(p 0-c 0)| := abs_add_le _ _
    _ ≤ (|p 1-l 0*p 0-l 1|+|c 1-p 1|)+|l 0*(p 0-c 0)| :=
      add_le_add (abs_add_le _ _) le_rfl
    _ ≤ (2*δ+Δ)+Δ := add_le_add (add_le_add hres h1) h2
    _ ≤ _ := by linarith only [hδΔ]

theorem rounded_incident_near_line {Δ : ℝ} (hΔ : 0 < Δ) (c l : Space 2)
    (hc0 : |c 0| ≤ 1) (hres : |c 1-l 0*c 0-l 1| ≤ 4*Δ) :
    dist l (roundedIncidentLine Δ c (l 0)) ≤ 6*Δ := by
  have hi := roundedIncidentLine_near_strip hΔ c hc0 hres
  have hh := planar_dist_le_coordinate_sum l (roundedIncidentLine Δ c (l 0))
  rw [roundedIncidentLine_fst,roundedIncidentLine_snd] at hh
  rw [abs_sub_comm (l 1)] at hh
  have he := lineGridRound_error hΔ (l 0)
  change |lineGridRound Δ (c 1-lineGridRound Δ (l 0)*c 0)-l 1| ≤ (4+1)*Δ at hi
  linarith only [hi,hh,he,hΔ]

theorem round_lineGridRound {Δ : ℝ} (hΔ : 0 < Δ) (a : ℝ) :
    round (lineGridRound Δ a/Δ) = round (a/Δ) := by
  unfold lineGridRound
  rw [mul_div_cancel_left₀ _ hΔ.ne',round_intCast]

theorem rounded_candidates_coarse {Δ : ℝ} (hΔ : 0 < Δ) (l : Space 2) (L : ℕ) :
    roundedStripCandidates Δ (l 0) (l 1) L =
      roundedStripCandidates Δ (coarsePlanarRound Δ l 0) (coarsePlanarRound Δ l 1) L := by
  simp only [roundedStripCandidates,coarsePlanarRound_zero,coarsePlanarRound_one,round_lineGridRound hΔ]

theorem incident_coarse_union_card {Δ : ℝ} (hΔ : 0 < Δ)
    (C : Finset (Space 2)) (T : Space 2 → Finset (Space 2))
    (hc : ∀ c ∈ C, |c 0| ≤ 1)
    (hres : ∀ c ∈ C, ∀ l ∈ T c, |c 1-l 0*c 0-l 1| ≤ 4*Δ) :
    ((C.biUnion fun c => (T c).image (fun l => roundedIncidentLine Δ c (l 0))).card:ℝ) ≤
      13*(((C.biUnion T).image (coarsePlanarRound Δ)).card:ℝ) := by
  have hh := labelled_line_union_card_le C
    (fun c => (T c).image (fun l => roundedIncidentLine Δ c (l 0)))
    ((C.biUnion T).image (coarsePlanarRound Δ))
    (fun b => roundedStripCandidates Δ (b 0) (b 1) 6)
    (L := 13) (by
      intro c hC a ha
      obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp ha
      refine ⟨coarsePlanarRound Δ l,
        Finset.mem_image_of_mem _ (Finset.mem_biUnion.mpr ⟨c,hC,hl⟩),?_⟩
      rw [← rounded_candidates_coarse hΔ]
      exact roundedIncidentLine_mem_candidates hΔ c (hc c hC) (hres c hC l hl) 6 (by norm_num)) (by
      intro b _
      exact_mod_cast roundedStripCandidates_card_le Δ (b 0) (b 1) 6)
  simpa only [mul_comm] using hh

end Falconer

end OAI
