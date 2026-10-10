import Mathlib
import OAI.Combinatorics.TriangleRemoval.Process.CenteredEdgeVectorTriangle
import OAI.Combinatorics.TriangleRemoval.Process.CenteredNeighborSumBound

namespace OAI

section
noncomputable section
open scoped BigOperators
open Filter Classical

namespace SharpTerminalLeave

lemma prefix_pair_closure_budget : ∀ᶠ n : ℕ in atTop,
    prefixEdgeForcingBound n+16*prefixEdgeRadius n*Real.log n ≤ prefixWheelRadius n/2 ∧
      prefixWheelRadius n ≤ 1 := by
  filter_upwards [prefix_edge_forcing_power,
    prefixTemplateFactor_subpower 1 (by norm_num : (0 : ℝ) < 1/80000)
      (by norm_num : (0 : ℝ) < 1/130),eventually_ge_atTop (1 : ℕ)] with n hF hlog hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le zero_lt_one hn1
  have hl := Real.log_nonneg hn1
  have hη : 0 ≤ prefixEdgeRadius n := Real.rpow_nonneg hn0.le _
  have hr : prefixTriangleRadius n ≤ prefixEdgeRadius n :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)
  have hlog' : 1+Real.log (n : ℝ) ≤ 1/130*(n : ℝ)^(1/80000 : ℝ) := by
    simpa only [prefixTemplateFactor,Real.rpow_one] using hlog
  have he : (n : ℝ)^(1/80000 : ℝ)*prefixEdgeRadius n = prefixWheelRadius n := by
    unfold prefixEdgeRadius prefixWheelRadius
    rw [← Real.rpow_add hn0]
    congr 1
    norm_num
  refine ⟨?_,Real.rpow_le_one_of_one_le_of_nonpos hn1 (by norm_num)⟩
  calc
    _ ≤ 49*(1+Real.log (n : ℝ))*prefixEdgeRadius n+16*prefixEdgeRadius n*Real.log n := by
      exact add_le_add (hF.2.trans (mul_le_mul_of_nonneg_left hr (by positivity))) le_rfl
    _ ≤ 65*(1+Real.log (n : ℝ))*prefixEdgeRadius n := by nlinarith only [hη]
    _ ≤ 65*(1/130*(n : ℝ)^(1/80000 : ℝ))*prefixEdgeRadius n := by gcongr
    _ = prefixWheelRadius n/2 := by rw [show 65*(1/130*(n : ℝ)^(1/80000 : ℝ))*prefixEdgeRadius n =
        ((n : ℝ)^(1/80000 : ℝ)*prefixEdgeRadius n)/2 by ring,he]

lemma initial_normalized_pair_bound {n : ℕ} (hn : 2 ≤ n)
    (ω : History (Graph n) (prefixTime n))
    (hω : ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support)
    (u v : Fin n) (huv : u ≠ v) :
    |prefixNormalizedCodegree u v 0 (ω (historyIndex (prefixTime n) 0))-1| ≤ 4/(n : ℝ) := by
  have hi := (historyLaw_path_support (PMF.pure (completeGraph n)) (fun _ => step)
    (prefixTime n) (prefixTime n) le_rfl ω hω).1
  have hi' : ω (historyIndex (prefixTime n) 0) = completeGraph n := by simpa using hi
  unfold prefixNormalizedCodegree
  rw [hi',initial_normalized_codegree_error hn u v huv,
    neg_div,abs_neg,abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1/((n : ℝ)-1)^2)]
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_div_iff₀ (sq_pos_of_ne_zero (by linarith)) (by linarith : (0 : ℝ) < n)).mpr
  nlinarith

theorem prefix_pair_barrier_improvement : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω → ∀ j ≤ prefixTime n,
    historyAlive (fun i => densityEdgeSafe n (earlyDensity n i) (prefixEdgeRadius n)) (prefixTime n) j ω →
    ∀ u v : Fin n, u ≠ v →
    (∀ i < j, (currentCodegree (ω (historyIndex (prefixTime n) i)) u v : ℝ) ≤ 2*earlyTemplateScale 1 2 n i) →
    |prefixNormalizedCodegree u v j (ω (historyIndex (prefixTime n) j))-1| ≤ prefixWheelRadius n/2 := by
  filter_upwards [prefix_pair_compensator_bound,prefix_pair_closure_budget,
    eventually_ge_atTop (2 : ℕ)] with n hcomp hbudget hn
  intro ω hω htri hnoise j hj hsafe u v huv hcap
  have hc := hcomp ω hω htri j hj hsafe u v huv hcap
  have hnse : |historyNoise (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω| < codegreeNoiseRadius n := by
    apply lt_of_not_ge
    intro hx
    exact hnoise u v ⟨j,hj,hcap,hx⟩
  have hi := initial_normalized_pair_bound hn ω hω u v huv
  have he := history_noise_compensator (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j hj ω
  have he' : prefixNormalizedCodegree u v j (ω (historyIndex (prefixTime n) j))-1 =
      (prefixNormalizedCodegree u v 0 (ω (historyIndex (prefixTime n) 0))-1)+
      historyNoise (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω+
      historyCompensator (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω := by linarith only [he]
  rw [he']
  apply le_trans _ hbudget.1
  have hab := (abs_add_le ((prefixNormalizedCodegree u v 0 (ω (historyIndex (prefixTime n) 0))-1)+
      historyNoise (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω)
      (historyCompensator (fun _ => step) (prefixNormalizedCodegree u v) (prefixTime n) j ω)).trans
    (add_le_add (abs_add_le _ _) le_rfl)
  apply hab.trans
  unfold prefixEdgeForcingBound
  linarith only [hi,hnse,hc]

theorem prefix_all_pair_closure : ∀ᶠ n : ℕ in atTop,
    ∀ ω : History (Graph n) (prefixTime n),
    ω ∈ (historyLaw (PMF.pure (completeGraph n)) (fun _ => step) (prefixTime n) (prefixTime n)).support →
    PrefixRootedUpper 8001 n ω → PrefixBalancedNoise 8001 n ω →
    PrefixTriangleNoise n ω → PrefixCodegreeNoiseGood n ω →
    ∀ j ≤ prefixTime n, ∀ u v : Fin n, u ≠ v →
      |prefixNormalizedCodegree u v j (ω (historyIndex (prefixTime n) j))-1| ≤ prefixWheelRadius n/2 := by
  filter_upwards [prefix_present_edge_closure,prefix_pair_barrier_improvement,
    prefix_pair_closure_budget,earlyTemplateScale_regular 1 2] with n hedge hpair hbudget hreg
  intro ω hω hroot hbalanced htri hnoise j
  have hs := hedge ω hω hroot hbalanced htri hnoise
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj u v huv
    apply hpair ω hω htri hnoise j hj (fun i hi => hs i (by omega)) u v huv
    intro i hi
    have hh := (le_abs_self (prefixNormalizedCodegree u v i (ω (historyIndex (prefixTime n) i))-1)).trans
      (ih i hi (by omega) u v huv)
    have hc : prefixNormalizedCodegree u v i (ω (historyIndex (prefixTime n) i)) ≤ 2 := by
      linarith only [hh,hbudget.2]
    exact (div_le_iff₀ (hreg.1 i (by omega))).mp hc

end SharpTerminalLeave
end
end

end OAI
