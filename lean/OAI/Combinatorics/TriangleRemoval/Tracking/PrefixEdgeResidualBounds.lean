import Mathlib
import OAI.Combinatorics.TriangleRemoval.Spectral.DensityGlobalSpectral
import OAI.Combinatorics.TriangleRemoval.Asymptotics.DensityGlobalInfty
import OAI.Combinatorics.TriangleRemoval.Process.HistoryGraphNested

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical Matrix

namespace SharpTerminalLeave

theorem prefix_edge_residual_bounds : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ∀ hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support,
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    ∀ i < j, ∀ z : CompleteEdge n → ℝ,
    activeLinf (graphActive (ω (historyIndex (prefixTime n) i))) (prefixEdgeResidual ω hω i z) ≤
      6*activeLinf (graphActive (ω (historyIndex (prefixTime n) i))) z ∧
    activeL2 (graphActive (ω (historyIndex (prefixTime n) i))) (prefixEdgeResidual ω hω i z) ≤
      (2*prefixSpectralError n (1/80000))*activeL2 (graphActive (ω (historyIndex (prefixTime n) i))) z := by
  filter_upwards [prefix_degree_wheel_tracking,prefixD_eventual_envelope,
    triangle_closure_budget,prefixDensity_eventually_inverse_lower,
    eventually_ge_atTop (1 : ℕ)] with n htrack hD hη hp hn
  intro ω hω hroot hnoise j hj hsafe i hi z
  have hn0 : 0 < n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnR : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hit : i ≤ prefixTime n := by omega
  let G := ω (historyIndex (prefixTime n) i)
  let D := earlyTemplateScale 1 2 n i
  have hG : G ⊆ completeGraph n := history_valid_all ω hω i
  have hs : densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n) G := hsafe i hi
  have hw := htrack ω hω hroot hnoise i hit (fun k hk => hsafe k (by omega))
  have hpi := early_density_positive hn0 hp hit
  have hD0 : 0 < D := by dsimp [D,earlyTemplateScale]; positivity
  have hDmin : 1 ≤ prefixD n := (Real.one_le_rpow hn1 (by norm_num : (0 : ℝ) ≤ 1/1000)).trans hD.1
  have hDle : prefixD n ≤ D := by
    have hp0 := early_density_positive hn0 hp (le_refl (prefixTime n))
    have hh := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hp0.le (earlyDensity_antitone n hit) 2) hnR.le
    simpa only [prefixD,D,earlyTemplateScale,pow_one,earlyDensity_prefix] using hh
  have hw0 : 0 ≤ prefixWheelRadius n := Real.rpow_nonneg hnR.le _
  have hw1 : prefixWheelRadius n ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)
  have hηw : prefixEdgeRadius n ≤ prefixWheelRadius n :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hrow : ∀ u v : Fin n, {u,v} ∈ G →
      |(currentCodegree G u v : ℝ)-D| ≤ (n : ℝ)^(-(1/80000 : ℝ))*D := by
    intro u v he
    have hh := hs.2.2 {u,v} he
    rw [triangleDegree_eq_codegree hG he] at hh
    have hh' : |(currentCodegree G u v : ℝ)-D| ≤ prefixEdgeRadius n*D := by
      simpa only [D,earlyTemplateScale,pow_one] using hh
    simpa only [prefixWheelRadius,neg_div] using hh'.trans (mul_le_mul_of_nonneg_right hηw hD0.le)
  have hcyc : ∀ b, 3 ≤ b → b ≤ 8000 → ∀ u : Fin n,
      |linkCycleCount b G u-D^b| ≤ (n : ℝ)^(-(1/80000 : ℝ))*D^b := by
    intro b hb hb' u
    have hh := hw.2 b hb hb' u
    have hh' : |linkCycleCount b G u/D^b-1| ≤ prefixWheelRadius n/2 := by
      simpa only [D,earlyTemplateScale,pow_one,G] using hh
    have hpow := pow_pos hD0 b
    have he : linkCycleCount b G u/D^b-1 = (linkCycleCount b G u-D^b)/D^b := by field_simp
    rw [he,abs_div,abs_of_pos hpow] at hh'
    have hh'' := (div_le_iff₀ hpow).mp hh'
    simpa only [prefixWheelRadius,neg_div] using hh''.trans (mul_le_mul_of_nonneg_right (by linarith only [hw0] : prefixWheelRadius n/2 ≤ prefixWheelRadius n) hpow.le)
  have hne : ∀ u : Fin n, (neighbors G u).Nonempty := by
    intro u
    have hh := (abs_le.mp (hw.1 u)).1
    have hpos : 0 < (n : ℝ)*earlyDensity n i := mul_pos hnR hpi
    have hc : (0 : ℝ) < currentDegree G u := by
      have hr : 0 < (currentDegree G u : ℝ)/((n : ℝ)*earlyDensity n i) := by linarith only [hh,hw1]
      exact (div_pos_iff.mp hr).resolve_right (by intro h; linarith only [h.2,hpos]) |>.1
    apply Finset.card_pos.mp
    exact_mod_cast hc
  have hrow2 : ∀ u v : Fin n, {u,v} ∈ G → (currentCodegree G u v : ℝ) ≤ 2*D := by
    intro u v he
    have hp0 : 0 ≤ (n : ℝ)*earlyDensity n i^2 := by positivity
    simpa only [D,earlyTemplateScale,pow_one] using densityEdgeSafe_pair_upper hp0 (show prefixEdgeRadius n ≤ 1 by linarith only [hη.2.1]) hs u v he
  constructor
  · open scoped Matrix.Norms.Operator in
    have hh := (graphMatrixLift_linf G hG (D⁻¹ • globalLinkAdjacency G hG-globalStarAverage G) z).trans
      (mul_le_mul_of_nonneg_right (density_residual_infty G hG D hD0 hrow2) (apply_nonneg _ _))
    exact hh
  · open scoped Matrix.Norms.L2Operator in
    have hh := (graphMatrixLift_l2 G hG (D⁻¹ • globalLinkAdjacency G hG-globalStarAverage G) z).trans
      (mul_le_mul_of_nonneg_right (density_global_spectral G hG D (1/80000) hDle hDmin (by simpa only [prefixWheelRadius,neg_div] using hw1) hne hrow hcyc)
        (apply_nonneg _ _))
    exact hh

end SharpTerminalLeave
end
end

end OAI
