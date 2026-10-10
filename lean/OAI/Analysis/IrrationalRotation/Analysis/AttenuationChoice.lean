import Mathlib
import OAI.Analysis.IrrationalRotation.Analysis.FiniteConvolution

namespace OAI

namespace InvariantProjection

theorem exists_attenuation (K : ℕ) (j ε Lprev : ℝ)
    (hj : 0 < j) (hε : 0 < ε) :
    ∃ L : ℝ, 1 ≤ L ∧ Lprev ≤ L ∧
      (2 * (K : ℝ) + 1) * 3 * Real.exp (-L / 10000) ≤ ε / j := by
  have hlim : Filter.Tendsto
      (fun L : ℝ => (2 * (K : ℝ) + 1) * 3 * Real.exp (-L / 10000))
      Filter.atTop (nhds 0) := by
    have hneg : Filter.Tendsto (fun L : ℝ => -L / 10000)
        Filter.atTop Filter.atBot := by
      simpa only [neg_div, Function.comp_def, id_eq] using
        (Filter.tendsto_neg_atTop_atBot.comp
          (Filter.tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 10000)))
    simpa using (Real.tendsto_exp_atBot.comp hneg).const_mul
      ((2 * (K : ℝ) + 1) * 3)
  have herr := hlim.eventually (gt_mem_nhds (div_pos hε hj))
  obtain ⟨L, hL, hp, he⟩ := Filter.Eventually.exists
    ((Filter.eventually_ge_atTop (1 : ℝ)).and
      ((Filter.eventually_ge_atTop Lprev).and herr))
  exact ⟨L, hL, hp, le_of_lt he⟩

theorem exists_sqrt_threshold (κ L : ℝ) (hκ : 0 < κ) :
    ∃ G : ℕ, 1 ≤ G ∧ L ≤ κ * Real.sqrt G := by
  obtain ⟨G, hG⟩ := exists_nat_gt (max 1 (max L 0 / κ) ^ 2)
  have hG1 : 1 ≤ G := by
    have : (1 : ℝ) < G := lt_of_le_of_lt (by nlinarith [le_max_left (1 : ℝ) (max L 0 / κ)]) hG
    exact_mod_cast (le_of_lt this)
  have hx : 0 ≤ max L 0 / κ := div_nonneg (le_max_right _ _) hκ.le
  have hsq : (max L 0 / κ) ^ 2 ≤ (G : ℝ) := by
    refine le_trans ?_ hG.le
    have hmax : max L 0 / κ ≤ max 1 (max L 0 / κ) := le_max_right _ _
    nlinarith [le_max_left (1 : ℝ) (max L 0 / κ)]
  have hsqrt : max L 0 / κ ≤ Real.sqrt (G : ℝ) :=
    (Real.le_sqrt hx (by positivity : (0 : ℝ) ≤ G)).mpr hsq
  refine ⟨G, hG1, ?_⟩
  have hmul := mul_le_mul_of_nonneg_left hsqrt hκ.le
  calc L ≤ max L 0 := le_max_left _ _
       _ = κ * (max L 0 / κ) := by field_simp
       _ ≤ κ * Real.sqrt G := hmul

theorem exists_coefficient_attenuation (K : ℕ) (D j Lprev : ℝ)
    (hj : 0 < j) :
    ∃ ε L : ℝ, ∃ G : ℕ,
      0 < ε ∧ 1 ≤ L ∧ Lprev ≤ L ∧ 1 ≤ G ∧
      (2 * (K : ℝ) + 1) * 3 * Real.exp (-L / 10000) ≤ ε / j ∧
      L ≤ (1 / (100 * (j + 1))) * Real.sqrt G ∧
      ∀ a b : FiniteConvolution.Coefficients K,
        (∀ i, ‖a i‖ ≤ D) → (∀ i, ‖b i‖ ≤ D) →
        1 / j ≤ ‖a (FiniteConvolution.center K)‖ →
        1 / j ≤ ‖b (FiniteConvolution.center K)‖ →
        ∃ n : Fin (2 * K + 1), ε ≤ ‖FiniteConvolution.lowProduct a b n‖ := by
  obtain ⟨ε, hε, hcoeff⟩ :=
    FiniteConvolution.uniform_lower_bound K D (1 / j) (by positivity)
  obtain ⟨L, hL, hprev, hsmall⟩ := exists_attenuation K j ε Lprev hj hε
  obtain ⟨G, hG, hlarge⟩ :=
    exists_sqrt_threshold (1 / (100 * (j + 1))) L (by positivity)
  exact ⟨ε, L, G, hε, hL, hprev, hG, hsmall, hlarge, hcoeff⟩

end InvariantProjection

end OAI
