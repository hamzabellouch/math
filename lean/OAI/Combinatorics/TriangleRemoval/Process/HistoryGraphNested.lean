import Mathlib
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixCodegreeNoiseGood
import OAI.Combinatorics.TriangleRemoval.Process.CompleteEdgePair
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEdgeForcingBound

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma history_graph_nested {n T : ℕ} (ω : History (Graph n) T)
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) T T).support)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ T) :
    ω (historyIndex T j) ⊆ ω (historyIndex T i) := by
  have hp := (historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    T T le_rfl ω hω).2
  induction j, hij using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ k hik ih => exact (step_support_subset (hp k (by omega))).trans (ih (by omega))

lemma densityEdgeSafe_centered_bound {n : ℕ} {p η : ℝ} {G : Graph n}
    (hp : 0 < (n : ℝ)*p^2) (h : densityEdgeSafe n p η G)
    (e : CompleteEdge n) (he : e.val ∈ G) :
    |centeredEdgeVector G ((n : ℝ)*p^2) e| ≤ η := by
  let uv := completeEdgePair e
  have hep : {uv.val.1,uv.val.2} ∈ G := uv.property.2 ▸ he
  have hh := h.2.2 e.val he
  rw [uv.property.2,triangleDegree_eq_codegree h.1 hep] at hh
  change |(currentCodegree G uv.val.1 uv.val.2 : ℝ)/((n : ℝ)*p^2)-1| ≤ η
  rw [show (currentCodegree G uv.val.1 uv.val.2 : ℝ)/((n : ℝ)*p^2)-1 =
    ((currentCodegree G uv.val.1 uv.val.2 : ℝ)-(n : ℝ)*p^2)/((n : ℝ)*p^2) by rw [sub_div,div_self hp.ne']]
  rw [abs_div,abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr hh

lemma densityEdgeSafe_pair_upper {n : ℕ} {p η : ℝ} {G : Graph n}
    (hp : 0 ≤ (n : ℝ)*p^2) (hη : η ≤ 1) (h : densityEdgeSafe n p η G)
    (u v : Fin n) (he : {u,v} ∈ G) :
    (currentCodegree G u v : ℝ) ≤ 2*((n : ℝ)*p^2) := by
  have hh := (abs_le.mp (h.2.2 {u,v} he)).2
  rw [triangleDegree_eq_codegree h.1 he] at hh
  nlinarith only [hh,mul_le_mul_of_nonneg_right hη hp]

lemma initial_centered_edge_bound {n : ℕ} (hn : 2 ≤ n)
    (ω : History (Graph n) (prefixTime n))
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support)
    (e : CompleteEdge n) : |prefixCenteredEdge ω 0 e| ≤ 4/(n : ℝ) := by
  have hi := (historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    (prefixTime n) (prefixTime n) le_rfl ω hω).1
  have hi' : ω (historyIndex (prefixTime n) 0) = completeGraph n := by simpa using hi
  unfold prefixCenteredEdge centeredEdgeVector
  rw [hi',initial_normalized_codegree_error hn _ _ (completeEdgePair e).property.1,
    neg_div,abs_neg,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/((n : ℝ)-1)^2)]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_div_iff₀ (sq_pos_of_ne_zero (by linarith)) (by linarith : (0 : ℝ) < n)).mpr
  nlinarith

lemma prefix_triangle_radius_small : ∀ᶠ n : ℕ in atTop,
    0 ≤ prefixTriangleRadius n ∧ prefixTriangleRadius n ≤ 1/2 := by
  have hl : Tendsto prefixTriangleRadius atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^(-3/80000 : ℝ)) atTop (nhds 0)
    simpa only [Function.comp_def,neg_div] using (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 3/80000)).comp tendsto_natCast_atTop_atTop
  filter_upwards [hl.eventually_le_const (by norm_num : (0 : ℝ) < 1/2)] with n hn
  exact ⟨Real.rpow_nonneg (Nat.cast_nonneg _) _,hn⟩

theorem prefix_edge_coefficient_bounds : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixTriangleNoise n ω → ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    (∀ i < j, 0 ≤ prefixEdgeRate ω i ∧ prefixEdgeRate ω i ≤ 1 ∧
      prefixEdgeRate ω i ≤ 4*(6/(n : ℝ)^2/earlyDensity n i) ∧
      |prefixEdgeScalar ω i| ≤ 8*prefixTriangleRadius n*(6/(n : ℝ)^2/earlyDensity n i)+
        2*(6/(n : ℝ)^2/earlyDensity n i)^2+
        4*(6/(n : ℝ)^2/earlyDensity n i)/earlyTemplateScale 1 2 n i) ∧
    (∑ i ∈ Finset.range j, prefixEdgeRate ω i) ≤ 4*Real.log n := by
  filter_upwards [prefix_triangle_tracking,earlyTemplateScale_regular 1 2,
    earlyTriangleScale_regular,prefix_triangle_radius_small,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (24 : ℕ)] with n htrack hreg htri hr hp hn
  intro ω hω hnoise j hj hsafe
  have hni : 0 < n := by omega
  have hnR : (24 : ℝ) ≤ n := by exact_mod_cast hn
  have hcoeff : ∀ i < j, 0 ≤ prefixEdgeRate ω i ∧ prefixEdgeRate ω i ≤ 1 ∧
      prefixEdgeRate ω i ≤ 4*(6/(n : ℝ)^2/earlyDensity n i) ∧
      |prefixEdgeScalar ω i| ≤ 8*prefixTriangleRadius n*(6/(n : ℝ)^2/earlyDensity n i)+
        2*(6/(n : ℝ)^2/earlyDensity n i)^2+
        4*(6/(n : ℝ)^2/earlyDensity n i)/earlyTemplateScale 1 2 n i := by
    intro i hi
    have hiT : i < prefixTime n := by omega
    have hs := early_codegree_grid hni hp hiT
    have hc := htrack ω hω hnoise i (by omega) (fun k hk => hsafe k (by omega))
    have hb := edge_stability_coefficients (hreg.1 i (by omega)) (hreg.1 (i+1) (by omega))
      (htri.1 i (by omega)) hs.2.2.1 hs.1 (hreg.2.2 i hiT) hs.2.1 hr.2 hc
      (by norm_num : (0 : ℝ) ≤ 1) le_rfl
    have hsmall : 4*(6/(n : ℝ)^2/earlyDensity n i) ≤ 1 := by
      have hh := mul_le_mul_of_nonneg_left hs.2.2.2 (by norm_num : (0 : ℝ) ≤ 4)
      have hi : 4*(6/(n : ℝ)) ≤ 1 := by
        rw [← mul_div_assoc]
        apply (div_le_iff₀ (by linarith : (0 : ℝ) < n)).mpr
        linarith only [hnR]
      exact hh.trans hi
    exact ⟨hb.1.1,hb.1.2.trans hsmall,hb.1.2,hb.2⟩
  refine ⟨hcoeff,?_⟩
  calc
    _ ≤ ∑ i ∈ Finset.range j, 4*(6/(n : ℝ)^2/earlyDensity n i) :=
      Finset.sum_le_sum (fun i hi => (hcoeff i (Finset.mem_range.mp hi)).2.2.1)
    _ = 4*(∑ i ∈ Finset.range j, 6/(n : ℝ)^2/earlyDensity n i) := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (early_grid_sum_bounds hni hp j hj).1 (by norm_num)

theorem prefix_edge_forcing_bound : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω → ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    trajectorySeminorm (fun t => activeLinf (graphActive (ω (historyIndex (prefixTime n) t)))) j
      (prefixEdgeForcing ω) ≤ prefixEdgeForcingBound n := by
  filter_upwards [prefix_edge_coefficient_bounds,prefix_edge_forcing_power,triangle_closure_budget,
    prefix_triangle_radius_small,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (2 : ℕ)] with n hcoeff hF hbud hr hp hn
  intro ω hω htri hnoise j hj hsafe
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  apply trajectorySeminorm_bound _ _ _ hF.1
  intro t ht
  apply activeLinf_bound _ _ hF.1
  intro e he
  have het : e.val ∈ ω (historyIndex (prefixTime n) t) := (mem_graphActive _ _).mp he
  have hep (i : ℕ) (hi : i < t) : e.val ∈ ω (historyIndex (prefixTime n) i) :=
    history_graph_nested ω hω hi.le (ht.trans hj) het
  have hc (i : ℕ) (hi : i < t) :
      0 ≤ prefixCenteredEdge ω i e+1 ∧ prefixCenteredEdge ω i e+1 ≤ 2 := by
    have hpos : 0 < (n : ℝ)*earlyDensity n i^2 := mul_pos hnR (sq_pos_of_pos (early_density_positive hn0 hp (by omega)))
    have hh := densityEdgeSafe_pair_upper hpos.le (show prefixEdgeRadius n ≤ 1 by linarith only [hbud.2.1])
      (hsafe i (by omega)) (completeEdgePair e).val.1 (completeEdgePair e).val.2
      ((completeEdgePair e).property.2 ▸ hep i hi)
    change 0 ≤ (currentCodegree _ _ _ : ℝ)/earlyTemplateScale 1 2 n i-1+1 ∧
      (currentCodegree _ _ _ : ℝ)/earlyTemplateScale 1 2 n i-1+1 ≤ 2
    simp only [sub_add_cancel,earlyTemplateScale,pow_one]
    exact ⟨by positivity,(div_le_iff₀ hpos).mpr hh⟩
  have hnse : |historyNoise (fun _ => step)
      (fun k H => (currentCodegree H (completeEdgePair e).val.1 (completeEdgePair e).val.2 : ℝ)/earlyTemplateScale 1 2 n k)
      (prefixTime n) t ω| < codegreeNoiseRadius n := by
    apply lt_of_not_ge
    intro hx
    apply hnoise (completeEdgePair e).val.1 (completeEdgePair e).val.2
    refine ⟨t,by omega,?_,hx⟩
    intro i hi
    have hpos := mul_pos hnR (sq_pos_of_pos (early_density_positive hn0 hp (by omega : i ≤ prefixTime n)))
    have hh := (hc i hi).2
    change (currentCodegree _ _ _ : ℝ)/earlyTemplateScale 1 2 n i-1+1 ≤ 2 at hh
    simp only [sub_add_cancel,earlyTemplateScale,pow_one] at hh
    simpa only [earlyTemplateScale,pow_one] using (div_le_iff₀ hpos).mp hh
  have hcb := (hcoeff ω hω htri j hj hsafe).1
  have hsumb : |∑ i ∈ Finset.range t, prefixEdgeScalar ω i*(prefixCenteredEdge ω i e+1)| ≤
      16*prefixTriangleRadius n*Real.log n+4/prefixD n+24*Real.log n/(n : ℝ) := by
    have hgrid := early_grid_sum_bounds hn0 hp t (by omega)
    calc
      _ ≤ ∑ i ∈ Finset.range t, |prefixEdgeScalar ω i*(prefixCenteredEdge ω i e+1)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range t,
          (16*prefixTriangleRadius n*(6/(n : ℝ)^2/earlyDensity n i)+
            4*(6/(n : ℝ)^2/earlyDensity n i)^2+
            8*(6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)) := by
        apply Finset.sum_le_sum
        intro i hi
        have hit := Finset.mem_range.mp hi
        rw [abs_mul,abs_of_nonneg (hc i hit).1]
        have hh := (mul_le_mul_of_nonneg_left (hc i hit).2 (abs_nonneg (prefixEdgeScalar ω i))).trans
          (mul_le_mul_of_nonneg_right (hcb i (by omega)).2.2.2 (by norm_num : (0 : ℝ) ≤ 2))
        exact hh.trans_eq (by simp only [earlyTemplateScale,pow_one]; ring)
      _ = 16*prefixTriangleRadius n*(∑ i ∈ Finset.range t, 6/(n : ℝ)^2/earlyDensity n i)+
          4*(∑ i ∈ Finset.range t, (6/(n : ℝ)^2/earlyDensity n i)^2)+
          8*(∑ i ∈ Finset.range t, (6/(n : ℝ)^2/earlyDensity n i)/((n : ℝ)*earlyDensity n i^2)) := by
        simp only [Finset.mul_sum,← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := by
        have h₁ := mul_le_mul_of_nonneg_left hgrid.1 (show 0 ≤ 16*prefixTriangleRadius n by exact mul_nonneg (by norm_num) hr.1)
        have h₂ := mul_le_mul_of_nonneg_left hgrid.2.2 (by norm_num : (0 : ℝ) ≤ 4)
        have h₃ := mul_le_mul_of_nonneg_left hgrid.2.1 (by norm_num : (0 : ℝ) ≤ 8)
        simp only [div_eq_mul_inv,mul_inv_rev] at h₁ h₂ h₃ ⊢
        norm_num at h₃
        nlinarith only [h₁,h₂,h₃]
  have hi := initial_centered_edge_bound hn ω hω e
  unfold prefixEdgeForcing prefixEdgeForcingBound
  calc
    _ ≤ |prefixCenteredEdge ω 0 e|+
        |historyNoise (fun _ => step) (fun k H => (currentCodegree H (completeEdgePair e).val.1 (completeEdgePair e).val.2 : ℝ)/earlyTemplateScale 1 2 n k) (prefixTime n) t ω|+
        |∑ k ∈ Finset.range t, prefixEdgeScalar ω k*(prefixCenteredEdge ω k e+1)| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith only [hi,hnse,hsumb]

end SharpTerminalLeave
end
end

end OAI
