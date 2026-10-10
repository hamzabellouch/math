import Mathlib
import OAI.Combinatorics.TriangleRemoval.Asymptotics.DensityEdgeSafeTriangle

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

noncomputable def prefixTriangleRadius (n : ℕ) : ℝ := (n : ℝ)^(-3/80000 : ℝ)

lemma triangle_closure_budget : ∀ᶠ n : ℕ in atTop,
    0 ≤ prefixEdgeRadius n ∧ prefixEdgeRadius n ≤ 1/2 ∧
    4/(n : ℝ)+codegreeNoiseRadius n+12*(prefixEdgeRadius n)^2*Real.log n+
      2/prefixD n+216*Real.log n/(n : ℝ) ≤ prefixTriangleRadius n := by
  have hrad : Tendsto prefixEdgeRadius atTop (nhds 0) := by
    change Tendsto (fun n : ℕ => (n : ℝ)^(-1/40000 : ℝ)) atTop (nhds 0)
    simpa only [Function.comp_def,neg_div] using (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 1/40000)).comp tendsto_natCast_atTop_atTop
  filter_upwards [prefixTemplateFactor_subpower 1 (by norm_num : (0 : ℝ) < 1/80000)
      (by norm_num : (0 : ℝ) < 1/235),prefixD_eventual_envelope,
    hrad.eventually_le_const (by norm_num : (0 : ℝ) < 1/2),
    eventually_ge_atTop (1 : ℕ)] with n hlog hD hrad hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have he : (prefixEdgeRadius n)^2 = (n : ℝ)^(-1/20000 : ℝ) := by
    unfold prefixEdgeRadius
    rw [← Real.rpow_natCast,← Real.rpow_mul hn0.le]
    norm_num
  have hinv : 1/(n : ℝ) ≤ (prefixEdgeRadius n)^2 := by
    rw [he]
    simpa only [Real.rpow_neg_one,one_div] using
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (-1 : ℝ) ≤ -1/20000))
  have hnoise : codegreeNoiseRadius n ≤ (prefixEdgeRadius n)^2 := by
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hdisc : 1/prefixD n ≤ (prefixEdgeRadius n)^2 := by
    rw [he]
    apply (div_le_div_of_nonneg_left zero_le_one (Real.rpow_pos_of_pos hn0 _) hD.1).trans
    rw [one_div,← Real.rpow_neg hn0.le]
    exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hn1
  have hs := mul_le_mul_of_nonneg_right (show 1+Real.log (n : ℝ) ≤
      1/235*(n : ℝ)^(1/80000 : ℝ) by
        simpa only [prefixTemplateFactor,Real.rpow_one] using hlog)
      (show 0 ≤ 235*(prefixEdgeRadius n)^2 by positivity)
  have hprod : (n : ℝ)^(1/80000 : ℝ)*(prefixEdgeRadius n)^2 = prefixTriangleRadius n := by
    rw [he,← Real.rpow_add hn0]
    norm_num [prefixTriangleRadius]
  have hscaled : 235*(1+Real.log (n : ℝ))*(prefixEdgeRadius n)^2 ≤ prefixTriangleRadius n := by
    nlinarith only [hs,hprod]
  refine ⟨Real.rpow_nonneg hn0.le _,hrad,?_⟩
  have hgrid := mul_le_mul_of_nonneg_left hinv (show 0 ≤ 216*Real.log (n : ℝ) by positivity)
  simp only [div_eq_mul_inv,one_mul] at hinv hdisc hgrid ⊢
  nlinarith only [hinv,hnoise,hdisc,hgrid,hscaled,sq_nonneg (prefixEdgeRadius n),
    mul_nonneg (sq_nonneg (prefixEdgeRadius n)) hl]

theorem prefix_triangle_tracking : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixTriangleNoise n ω → ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    |(triangles (ω (historyIndex (prefixTime n) j))).card/earlyTriangleScale n j-1| ≤
      prefixTriangleRadius n := by
  filter_upwards [triangle_closure_budget,earlyTriangleScale_regular,
    prefixDensity_eventually_inverse_lower,eventually_ge_atTop (2 : ℕ)] with n hb hr hp hn
  intro ω hω hnse j hj hsafe
  have hn0 : 0 < n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hi := (historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    (prefixTime n) (prefixTime n) le_rfl ω hω).1
  have hi' : ω (historyIndex (prefixTime n) 0) = completeGraph n := by
    simpa only [PMF.mem_support_pure_iff] using hi
  have hloads : pastRelativeCopyLoadsSafe (triangleRequired (n := n)) (triangleNoiseLoad n)
      (prefixTime n) j ω := by
    intro i hit
    have hij : i < j := lt_of_lt_of_le hit (Nat.min_le_left _ _)
    have hh := densityEdgeSafe_triangle_load (early_density_positive hn0 hp (by omega)).le
      (show prefixEdgeRadius n ≤ 1 by linarith only [hb.2.1]) (hsafe i hij)
    simpa only [triangleNoiseLoad,earlyTemplateScale,pow_one] using hh
  have hcap : ∀ i < j, copyCount (triangleRequired (n := n)) (ω (historyIndex (prefixTime n) i)) ≤
      2*earlyTriangleScale n i := by
    intro i hij
    rw [triangle_copyCount]
    have hh := (densityEdgeSafe_triangle_bounds (hsafe i hij)).2
    have hS : 0 ≤ earlyTriangleScale n i := (hr.1 i (by omega)).le
    change _ ≤ earlyTriangleScale n i*(1+prefixEdgeRadius n) at hh
    have ht := mul_le_mul_of_nonneg_right hb.2.1 hS
    linarith only [hh,ht,hS]
  have hnoise : |historyNoise (fun _ => step)
      (fun i G => ((triangles G).card : ℝ)/earlyTriangleScale n i) (prefixTime n) j ω| < codegreeNoiseRadius n := by
    apply lt_of_not_ge
    intro hcross
    apply hnse
    refine ⟨j,hj,hloads,hcap,?_⟩
    simpa only [triangle_copyCount] using hcross
  have hd := early_triangle_drift_bound (prefixEdgeRadius n) hn0 hp hb.1 hb.2.1
    hr.2.2.1 j hj ω hsafe
  have hinit : |(triangles (ω (historyIndex (prefixTime n) 0))).card/earlyTriangleScale n 0-1| ≤ 4/(n : ℝ) := by
    rw [hi',initial_triangle_relative_error hn,neg_div,abs_neg,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/((n : ℝ)-1)^2)]
    apply (div_le_div_iff₀ (sq_pos_of_ne_zero (by linarith)) (by linarith : (0 : ℝ) < n)).mpr
    nlinarith
  have ht := (abs_add_le
    (((triangles (ω (historyIndex (prefixTime n) j))).card : ℝ)/earlyTriangleScale n j-
      (triangles (ω (historyIndex (prefixTime n) 0))).card/earlyTriangleScale n 0-
      historyNoise (fun _ => step) (fun i G => ((triangles G).card : ℝ)/earlyTriangleScale n i) (prefixTime n) j ω)
    (historyNoise (fun _ => step) (fun i G => ((triangles G).card : ℝ)/earlyTriangleScale n i) (prefixTime n) j ω))
  have ht' := abs_add_le
    (((triangles (ω (historyIndex (prefixTime n) j))).card : ℝ)/earlyTriangleScale n j-
      (triangles (ω (historyIndex (prefixTime n) 0))).card/earlyTriangleScale n 0)
    (((triangles (ω (historyIndex (prefixTime n) 0))).card : ℝ)/earlyTriangleScale n 0-1)
  simp only [sub_add_cancel] at ht
  simp only [sub_add_sub_cancel] at ht'
  linarith only [ht,ht',hd,hnoise,hinit,hb.2.2]

end SharpTerminalLeave
end
end

end OAI
