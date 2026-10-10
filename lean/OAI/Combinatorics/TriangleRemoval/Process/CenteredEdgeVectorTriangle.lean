import Mathlib
import OAI.Combinatorics.TriangleRemoval.Stability.MovingResidualForcing
import OAI.Combinatorics.TriangleRemoval.Tracking.PrefixEdgeResidualBounds

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma centeredEdgeVector_eq_triangle {n : ℕ} (G : Graph n) (hG : G ⊆ completeGraph n)
    (s : ℝ) (e : CompleteEdge n) (he : e.val ∈ G) :
    centeredEdgeVector G s e = (triangleDegree G e.val : ℝ)/s-1 := by
  exact congrFun (centeredEdgeVector_restrict G hG s) (⟨e.val,he⟩ : G)

theorem prefix_edge_barrier_improvement : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω →
    ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    trajectorySeminorm (fun t => activeLinf (graphActive (ω (historyIndex (prefixTime n) t)))) j
      (prefixCenteredEdge ω) ≤ prefixEdgeRadius n/2 := by
  obtain ⟨γ,hγ,hdec⟩ := prefixSpectralError_power_decay (by norm_num : (0 : ℝ) < 1/80000)
  obtain ⟨K,hK0,hbudget⟩ := prefix_edge_stability_budget hγ
  filter_upwards [hdec,hbudget,prefix_edge_residual_bounds,prefix_edge_forcing_bound,
    prefix_edge_coefficient_bounds,earlyTemplateScale_regular 1 2] with n hdec hbudget hR hM ha hreg
  intro ω hω hroot hbalanced htri hnoise j hj hsafe
  let active (i : ℕ) := graphActive (ω (historyIndex (prefixTime n) i))
  let a := prefixEdgeRate ω
  let R := prefixEdgeResidual ω hω
  let M := prefixEdgeForcing ω
  let x := prefixCenteredEdge ω
  let S := ∑ i ∈ Finset.range j, a i
  have hcb := ha ω hω htri j hj hsafe
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i hi => (hcb.1 i (Finset.mem_range.mp hi)).1)
  have hS1 : S ≤ 4*Real.log n := hcb.2
  have hnest : ∀ i < j, active (i+1) ⊆ active i := by
    intro i hi
    apply graphActive_nested
    exact history_graph_nested ω hω (Nat.le_succ i) (by omega)
  have hinit : ∀ e ∈ active 0, x 0 e = M 0 e := by
    intro e _
    rw [show M 0 = x 0 from prefixEdgeForcing_zero ω]
  have hstep : ∀ i < j, ∀ e ∈ active (i+1), x (i+1) e = x i e-
      a i*(movingStarLift (fun e : CompleteEdge n => e.val)
        (movingStarMean (fun e : CompleteEdge n => e.val) (active i) (x i)) e+R i (x i) e)+
      (M (i+1) e-M i e) := by
    intro i hi e he
    exact prefix_centered_edge_recurrence ω hω (by omega) (hreg.1 i (by omega)).ne' e he
  have hRinf : ∀ i < j, ∀ z, activeLinf (active i) (R i z) ≤ 6*activeLinf (active i) z := by
    intro i hi z
    exact (hR ω hω hroot hbalanced j hj hsafe i hi z).1
  have hR2 : ∀ i < j, ∀ z, activeL2 (active i) (R i z) ≤ (n : ℝ)^(-γ)*activeL2 (active i) z := by
    intro i hi z
    exact (hR ω hω hroot hbalanced j hj hsafe i hi z).2.trans
      (mul_le_mul_of_nonneg_right hdec (apply_nonneg _ _))
  have hk : ((1+2*S)*S*(n : ℝ)^(-γ))^K*(Fintype.card (CompleteEdge n) : ℝ) ≤ 1/2 := by
    have hc : (Fintype.card (CompleteEdge n) : ℝ) ≤ (n : ℝ)^2 := by exact_mod_cast graphActive_card_le (n := n)
    exact (mul_le_mul_of_nonneg_left hc (by positivity)).trans (hbudget S hS0 hS1).1
  have hm := movingStar_mixed_stability (fun e : CompleteEdge n => e.val)
    (fun e => mem_completeGraph.mp e.property) active a R M x j K hnest
    (fun i hi => ⟨(hcb.1 i hi).1,(hcb.1 i hi).2.1⟩) hinit hstep
    (by norm_num : (0 : ℝ) ≤ 6) (Real.rpow_nonneg (Nat.cast_nonneg n) (-γ)) hRinf hR2 hk
  apply hm.trans
  apply le_trans _ (hbudget S hS0 hS1).2
  apply mul_le_mul_of_nonneg_left (hM ω hω htri hnoise j hj hsafe)
  have ha0 : ∀ i ∈ Finset.range j, 0 ≤ a i := fun i hi => (hcb.1 i (Finset.mem_range.mp hi)).1
  positivity

lemma history_mass_of_alive {n : ℕ} (hn : 0 < n)
    (hp : 1/(n : ℝ) ≤ prefixDensity n) (hη : prefixEdgeRadius n ≤ 1/2)
    (ω : History (Graph n) (prefixTime n))
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support)
    (j : ℕ) (hj : j ≤ prefixTime n)
    (hsafe : historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω) :
    ((ω (historyIndex (prefixTime n) j)).card : ℝ) = (n : ℝ)^2*earlyDensity n j/2 := by
  obtain ⟨hinit,hpath⟩ := historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    (prefixTime n) (prefixTime n) le_rfl ω hω
  cases j with
  | zero =>
    have hi : ω (historyIndex (prefixTime n) 0) = completeGraph n := by simpa using hinit
    rw [hi]
    exact completeGraph_early_mass hn
  | succ i =>
    have hs := hsafe i (Nat.lt_succ_self i)
    have hactive := densityEdgeSafe_triangle_positive hn (early_density_positive hn hp (by omega)) hη hs
    have hc := step_card_of_active hactive (hpath i (by omega))
    have hcR : ((ω (historyIndex (prefixTime n) (i+1))).card : ℝ)+3 = (n : ℝ)^2*earlyDensity n i/2 := by
      rw [← hs.2.1]
      exact_mod_cast hc
    rw [earlyDensity_succ n i] at hcR
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    have he : (n : ℝ)^2*(earlyDensity n (i+1)+6/(n : ℝ)^2)/2 =
        (n : ℝ)^2*earlyDensity n (i+1)/2+3 := by field_simp; ring
    rw [he] at hcR
    linarith only [hcR]

theorem prefix_present_edge_closure : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω →
    ∀ j ≤ prefixTime n, densityEdgeSafe n (earlyDensity n j) (prefixEdgeRadius n)
      (ω (historyIndex (prefixTime n) j)) := by
  filter_upwards [prefix_edge_barrier_improvement,triangle_closure_budget,
    prefixDensity_eventually_inverse_lower,earlyTemplateScale_regular 1 2,
    eventually_ge_atTop (1 : ℕ)] with n hb hη hp hreg hn
  intro ω hω hroot hbalanced htri hnoise j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    have hs : historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω := by
      intro i hi
      exact ih i hi (by omega)
    have hbound := hb ω hω hroot hbalanced htri hnoise j hj hs
    have hG := complete_history_valid ω hω j hj
    refine ⟨hG,history_mass_of_alive (by omega) hp hη.2.1 ω hω j hj hs,?_⟩
    intro e he
    let E : CompleteEdge n := ⟨e,hG he⟩
    have hEa : E ∈ graphActive (ω (historyIndex (prefixTime n) j)) := (mem_graphActive _ _).mpr he
    have hx := (activeLinf_coordinate (graphActive (ω (historyIndex (prefixTime n) j)))
      (prefixCenteredEdge ω j) hEa).trans ((trajectorySeminorm_at
        (fun t => activeLinf (graphActive (ω (historyIndex (prefixTime n) t)))) j
        (prefixCenteredEdge ω) le_rfl).trans hbound)
    change |centeredEdgeVector _ _ E| ≤ _ at hx
    rw [centeredEdgeVector_eq_triangle _ hG _ E he] at hx
    have hpos := hreg.1 j hj
    have heq : (triangleDegree (ω (historyIndex (prefixTime n) j)) e : ℝ)/earlyTemplateScale 1 2 n j-1 =
        ((triangleDegree (ω (historyIndex (prefixTime n) j)) e : ℝ)-earlyTemplateScale 1 2 n j)/earlyTemplateScale 1 2 n j := by field_simp
    change |(triangleDegree (ω (historyIndex (prefixTime n) j)) e : ℝ)/earlyTemplateScale 1 2 n j-1| ≤ _ at hx
    rw [heq,abs_div,abs_of_pos hpos] at hx
    have hh := (div_le_iff₀ hpos).mp hx
    simpa only [earlyTemplateScale,pow_one] using hh.trans (mul_le_mul_of_nonneg_right (by linarith only [hη.1]) hpos.le)

end SharpTerminalLeave
end
end

end OAI
