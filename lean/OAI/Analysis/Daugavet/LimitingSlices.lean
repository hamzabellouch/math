import OAI.Analysis.Daugavet.ClosedUnion

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators

universe uX

namespace ExactModuli

lemma unit_in_nonempty_slice {X : Type uX} [NormedAddCommGroup X] [NormedSpace ℝ X] [Nontrivial X]
    (ell : X →L[ℝ] ℝ) (α : ℝ) (hs : ∃ x : X, ‖x‖ ≤ 1 ∧ α < ell x) :
    ∃ u : X, ‖u‖ = 1 ∧ α < ell u := by
  obtain ⟨x,hxn,hα⟩ := hs
  by_cases hxpos : 0 < ell x
  · have hx0 : x ≠ 0 := by intro hx; simp [hx] at hxpos
    have hnx : 0 < ‖x‖ := norm_pos_iff.mpr hx0
    refine ⟨‖x‖⁻¹ • x,norm_smul_inv_norm hx0,?_⟩
    rw [map_smul, smul_eq_mul]
    exact hα.trans_le (le_mul_of_one_le_left hxpos.le ((one_le_inv₀ hnx).mpr hxn))
  · have hα0 : α < 0 := hα.trans_le (le_of_not_gt hxpos)
    obtain ⟨u,hu⟩ := exists_norm_eq X (by norm_num : (0:ℝ)≤1)
    by_cases hu0 : 0 ≤ ell u
    · exact ⟨u,hu,hα0.trans_le hu0⟩
    · exact ⟨-u,by simpa using hu,by simpa using hα0.trans (neg_pos.mpr (lt_of_not_ge hu0))⟩

end ExactModuli

namespace ExactModuli.KW

lemma constructedSpace_unitSlice : UnitSliceProperty constructedSpace := by
  classical
  let : Nontrivial constructedSpace := Submodule.nontrivial_iff_ne_bot.mpr constructedSpace_nonzero
  intro w hwn ell α hs ρ hρ
  obtain ⟨u,hun,hα⟩ := unit_in_nonempty_slice ell α hs
  let η : ℝ := min (ρ/4) ((ell u - α) / (8 * (‖ell‖ + 1)))
  have hden : 0 < 8 * (‖ell‖ + 1) := by positivity
  have hη : 0 < η := lt_min (by positivity) (div_pos (sub_pos.mpr hα) hden)
  have hηρ : η ≤ ρ/4 := min_le_left _ _
  have hηell : η * (8 * (‖ell‖ + 1)) ≤ ell u - α :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  obtain ⟨N,hN⟩ := stageError_eventually_small hη
  obtain ⟨nu,hnu,us,hus,husn,huus⟩ := constructed_sphere_approx u.property hun hη N
  obtain ⟨nw,hnw,ws,hws,hwsn,hwws⟩ := constructed_sphere_approx w.property hwn hη N
  let b := max nu nw
  have husb : us ∈ stageSpace b := stageSpace_mono (le_max_left _ _) hus
  have hwsb : ws ∈ stageSpace b := stageSpace_mono (le_max_right _ _) hws
  have hb : stageError b < η := hN b (hnu.trans (le_max_left _ _))
  obtain ⟨n,hn,v,hv,husv,hadd⟩ := (step_estimates b).averages us husb husn
  let V : Fin n → constructedSpace := fun j => ⟨v j,stageSpace_le_constructed (b+1) (hv j).1⟩
  let a : constructedSpace := (n : ℝ)⁻¹ • ∑ j, V j
  have haVal : (a : KWL1) = (n : ℝ)⁻¹ • ∑ j, v j := by simp [a,V]
  have hua : ‖u-a‖ ≤ η + 2 * stageError b := by
    change ‖(u : KWL1) - (a : KWL1)‖ ≤ _
    rw [haVal]
    exact (norm_sub_le_norm_sub_add_norm_sub _ us _).trans (add_le_add huus.le husv)
  have hdiff : |ell u - ell a| ≤ ‖ell‖ * (η + 2 * stageError b) := by
    calc
      _ = ‖ell (u-a)‖ := by rw [map_sub, Real.norm_eq_abs]
      _ ≤ ‖ell‖ * ‖u-a‖ := ell.le_opNorm _
      _ ≤ ‖ell‖ * (η + 2 * stageError b) := mul_le_mul_of_nonneg_left hua (norm_nonneg ell)
  have herror : ‖ell‖ * (η + 2 * stageError b) < ell u - α := by
    have he := mul_le_mul_of_nonneg_left (show η + 2 * stageError b ≤ 3*η by linarith) (norm_nonneg ell)
    have hLη : 0 ≤ ‖ell‖ * η := mul_nonneg (norm_nonneg ell) hη.le
    nlinarith
  have haα : α < ell a := by linarith [le_abs_self (ell u - ell a)]
  have hnℝ : (0:ℝ) < n := by exact_mod_cast hn
  have haell : ell a = (∑ j, ell (V j)) / (n:ℝ) := by
    simp [a, map_sum, div_eq_mul_inv, mul_comm]
  have hj : ∃ j, α < ell (V j) := by
    by_contra hh
    push Not at hh
    have hsum : (∑ j, ell (V j)) ≤ (n:ℝ) * α := by
      calc
        _ ≤ ∑ j : Fin n, α := Finset.sum_le_sum (fun j _ => hh j)
        _ = (n:ℝ) * α := by simp
    have hale : ell a ≤ α := by
      rw [haell]
      exact (div_le_iff₀ hnℝ).mpr (by simpa only [mul_comm] using hsum)
    linarith
  obtain ⟨j,hj⟩ := hj
  refine ⟨V j,(hv j).2,hj,?_⟩
  have hnear := hadd ws hwsb hwsn j
  have htri : ‖ws + v j‖ ≤ ‖(w:KWL1)-ws‖ + ‖(w:KWL1)+v j‖ := by
    have ht := norm_add_le (ws-(w:KWL1)) ((w:KWL1)+v j)
    have heq : ws-(w:KWL1)+((w:KWL1)+v j) = ws+v j := by abel
    rw [heq, norm_sub_rev] at ht
    exact ht
  change 2 - ρ ≤ ‖(w:KWL1)+v j‖
  linarith

lemma constructedSpace_daugavet : Daugavet constructedSpace := by
  let : Nontrivial constructedSpace := Submodule.nontrivial_iff_ne_bot.mpr constructedSpace_nonzero
  exact unitSlice_daugavet constructedSpace_unitSlice

end ExactModuli.KW

end

end OAI
