import OAI.MeasureTheory.Falconer.Geometry.ScalarBallCandidates

namespace OAI

/-! Selecting a maximal-density interval gives uniform local ball
bounds without any continuum optimization. -/
namespace Falconer

 theorem scalar_maximal_density_interval_candidate {δ κ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 ≤ κ) (E : Finset ℝ) (hE : E.Nonempty) (hbound : ∀ x ∈ E, |x| ≤ 1) :
    ∃ z ∈ E, ∃ R : ℝ, δ ≤ R ∧ R ≤ 2 ∧ (z,R) ∈ scalarBallCandidates δ E ∧
      (E.filter fun x => |x-z| ≤ R).Nonempty ∧
      (E.card : ℝ)/2^κ ≤ scalarBallMass E z R/R^κ ∧
      ∀ u r : ℝ, δ ≤ r → scalarBallMass E u r ≤
        2^κ*(r/R)^κ*scalarBallMass E z R := by
  classical
  let f := fun p : ℝ × ℝ => scalarBallMass E p.1 p.2/p.2^κ
  obtain ⟨p,hp,hmax⟩ := (scalarBallCandidates δ E).exists_max_image f
    (scalarBallCandidates_nonempty δ hE)
  obtain ⟨hz,hRδ,hR2⟩ := scalarBallCandidate_bounds hδ1 E hbound hp
  have hR : 0 < p.2 := hδ.trans_le hRδ
  have hne : (E.filter fun x => |x-p.1| ≤ p.2).Nonempty := by
    refine ⟨p.1,Finset.mem_filter.mpr ⟨hz,?_⟩⟩
    simpa only [sub_self,abs_zero] using hR.le
  refine ⟨p.1,hz,p.2,hRδ,hR2,hp,hne,?_,?_⟩
  · obtain ⟨x,hx⟩ := hE
    have hh := hmax (x,2) (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨x,hx,rfl⟩))
    simpa only [f,scalarBallMass_at_two E hbound hx] using hh
  · intro u r hdr
    have hr : 0 < r := hδ.trans_le hdr
    by_cases hnonempty : (E.filter fun x => |x-u| ≤ r).Nonempty
    · obtain ⟨q,hq,hqr,hcount⟩ := scalarBallMass_majorized_candidate hδ hdr E hnonempty
      have hqR : 0 < q.2 := hδ.trans_le (scalarBallCandidate_bounds hδ1 E hbound hq).2.1
      have hqmax := hmax q hq
      change scalarBallMass E q.1 q.2/q.2^κ ≤ scalarBallMass E p.1 p.2/p.2^κ at hqmax
      have hqcount : scalarBallMass E q.1 q.2 ≤
          (scalarBallMass E p.1 p.2/p.2^κ)*q.2^κ :=
        (div_le_iff₀ (Real.rpow_pos_of_pos hqR κ)).1 hqmax
      have hp0 : 0 ≤ scalarBallMass E p.1 p.2/p.2^κ := by
        exact div_nonneg (scalarBallMass_nonneg E _ _) (Real.rpow_nonneg hR.le _)
      calc
        _ ≤ scalarBallMass E q.1 q.2 := hcount
        _ ≤ (scalarBallMass E p.1 p.2/p.2^κ)*q.2^κ := hqcount
        _ ≤ (scalarBallMass E p.1 p.2/p.2^κ)*(2*r)^κ :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hqR.le hqr hκ) hp0
        _ = _ := by
          rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le,
            Real.div_rpow hr.le hR.le]
          ring
    · have he : scalarBallMass E u r = 0 := by
        unfold scalarBallMass
        rw [Finset.not_nonempty_iff_eq_empty.mp hnonempty]
        simp
      rw [he]
      have hm := scalarBallMass_nonneg E p.1 p.2
      positivity

 theorem scalar_maximal_density_interval {δ κ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hκ : 0 ≤ κ) (E : Finset ℝ) (hE : E.Nonempty) (hbound : ∀ x ∈ E, |x| ≤ 1) :
    ∃ z ∈ E, ∃ R : ℝ, δ ≤ R ∧ R ≤ 2 ∧
      (E.filter fun x => |x-z| ≤ R).Nonempty ∧
      (E.card : ℝ)/2^κ ≤ scalarBallMass E z R/R^κ ∧
      ∀ u r : ℝ, δ ≤ r → scalarBallMass E u r ≤
        2^κ*(r/R)^κ*scalarBallMass E z R := by
  obtain ⟨z,hz,R,hRδ,hR2,_,hF,hmax,hlocal⟩ :=
    scalar_maximal_density_interval_candidate hδ hδ1 hκ E hE hbound
  exact ⟨z,hz,R,hRδ,hR2,hF,hmax,hlocal⟩

end Falconer

end OAI
