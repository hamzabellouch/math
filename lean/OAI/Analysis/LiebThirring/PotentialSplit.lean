import OAI.Analysis.LiebThirring.SobolevBound

namespace OAI


noncomputable section
namespace SharpLiebThirring.OperatorProof
open MeasureTheory Set Filter
open scoped Topology ENNReal

/-- The only potential-approximation fact needed for the associated operator:
    an Lᵖ potential, p>1, is bounded plus an arbitrarily small L¹ remainder. -/
lemma potential_decomposition {γ : ℝ} {W : ℝ → ℝ} (hγ : 1/2 < γ)
    (hW : Admissible γ W) {ε : ℝ} (hε : 0 < ε) :
    ∃ b : ℝ, 0 ≤ b ∧ ∃ V : ℝ → ℝ, (∀ x, 0 ≤ V x) ∧ Integrable V ∧
      (∫ x, V x) ≤ ε ∧ ∀ x, ‖W x‖ ≤ b+V x := by
  let V : ℕ → ℝ → ℝ := fun n x ↦ max (‖W x‖-((n:ℝ)+1)) 0
  have hm (n : ℕ) : AEStronglyMeasurable (V n) volume :=
    (continuous_id.max continuous_const).comp_aestronglyMeasurable
      (hW.2.aestronglyMeasurable.norm.sub aestronglyMeasurable_const)
  have hpos (n : ℕ) (x : ℝ) : 0 ≤ V n x := le_max_right _ _
  have hd (n : ℕ) (x : ℝ) : ‖V n x‖ ≤ ‖W x‖^(γ+1/2) := by
    rw [Real.norm_of_nonneg (hpos n x)]
    change max (‖W x‖-((n:ℝ)+1)) 0 ≤ ‖W x‖^(γ+1/2)
    apply max_le
    · by_cases hw : 1 ≤ ‖W x‖
      · exact (sub_le_self _ (by positivity)).trans
          (Real.self_le_rpow_of_one_le hw (by linarith))
      · have hp : 0 ≤ ‖W x‖^(γ+1/2) := Real.rpow_nonneg (norm_nonneg _) _
        have hn : (0:ℝ) ≤ n := Nat.cast_nonneg _
        linarith [not_le.mp hw]
    · exact Real.rpow_nonneg (norm_nonneg _) _
  have hdom : Integrable (fun x ↦ ‖W x‖^(γ+1/2)) := by
    have hh := hW.2.integrable_norm_rpow
      (ENNReal.ofReal_pos.mpr (show 0 < γ+1/2 by linarith)).ne' ENNReal.ofReal_ne_top
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ γ+1/2 by linarith)] using hh
  have hV (n : ℕ) : Integrable (V n) := hdom.mono' (hm n) (Eventually.of_forall (hd n))
  have ht (x : ℝ) : Tendsto (fun n ↦ V n x) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    obtain ⟨N,hN⟩ := exists_nat_gt ‖W x‖
    filter_upwards [eventually_ge_atTop N] with n hn
    change 0 = max (‖W x‖-((n:ℝ)+1)) 0
    have hnn : (N:ℝ) ≤ n := Nat.cast_le.mpr hn
    rw [max_eq_right (by linarith)]
  have hlim : Tendsto (fun n ↦ ∫ x, V n x) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence
      (fun x ↦ ‖W x‖^(γ+1/2)) hm hdom (fun n ↦ Eventually.of_forall (hd n))
      (Eventually.of_forall ht)
  obtain ⟨n,hn⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
  refine ⟨(n:ℝ)+1,by positivity,V n,hpos n,hV n,hn.le,?_⟩
  intro x
  change ‖W x‖ ≤ (n:ℝ)+1+max (‖W x‖-((n:ℝ)+1)) 0
  linarith [le_max_left (‖W x‖-((n:ℝ)+1)) 0]

end SharpLiebThirring.OperatorProof

end

end OAI
