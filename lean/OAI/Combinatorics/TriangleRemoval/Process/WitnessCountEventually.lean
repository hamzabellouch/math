import Mathlib
import OAI.Combinatorics.TriangleRemoval.Asymptotics.OneAddLogRpow
import OAI.Combinatorics.TriangleRemoval.Process.Parent
import OAI.Combinatorics.TriangleRemoval.Process.SuffixProjection
import OAI.Combinatorics.TriangleRemoval.Process.BackEdgesCardSplit

namespace OAI

section
open scoped BigOperators Topology Matrix.Norms.Operator
open MeasureTheory
open Filter MeasureTheory
open scoped BigOperators ENNReal Classical
open scoped BigOperators
open Filter
open scoped BigOperators Topology

namespace SharpTerminalLeave

theorem actual_witness_count_eventually (c C : ℝ) (hc : 0 < c) :
    ∀ᶠ n : ℕ in atTop, ∀ (G : Graph n), GoodPrefixGraph n c C G →
    ∀ r : ℕ, r ≤ 2 → ∀ N : ℕ, ∀ (A : TriangleGrowth (lookupGraph G) N (2*r)),
      2*r ≤ N → (A.seed.backEdges A.roots).card = r →
    ∀ a b : Fin N, A.birthGraph.ExtraEdge (lookupGraph G) A.label a b →
    ((graphEmbeddingSet (insert ({A.pathIndex a b a (A.left_mem_pathUnion a b),
      A.pathIndex a b b (A.right_mem_pathUnion a b)} : Finset _)
      ((A.pathPattern a b).backEdges Finset.univ)) G).card : ℝ) ≤
      (4*prefixM n)^r * (2*prefixD n)^(A.pathSuffix a b (2*r)).card / prefixD n^50 := by
  filter_upwards [prefix_short_suppression C,prefix_long_suppression C,
    prefix_suffix_scaling,prefix_scales_eventually_pos,eventually_ge_atTop (1 : ℕ)]
    with n hshort hlong hscale hpos hn
  intro G hGood r hr N A hR hseed a b he
  let s := (A.pathSuffix a b (2*r)).card
  have hcard : (A.pathUnion a b).card = 2*r+s := A.path_card_split a b hR
  have hm0 : 0 ≤ prefixM n := by
    unfold prefixM
    exact div_nonneg (mul_nonneg (sq_nonneg _) hpos.1.le) (by norm_num)
  have hD0 : 0 < prefixD n := lt_of_lt_of_le zero_lt_one hpos.2
  have hden : 0 < prefixD n^50 := pow_pos hD0 _
  have hκ0 : 0 ≤ prefixTemplateFactor n C := by unfold prefixTemplateFactor; positivity
  have hsmall : (n : ℝ)^(-c) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn) (neg_nonpos.mpr hc.le)
  by_cases hs : s < 100
  · have hcap : (A.pathUnion a b).card ≤ prefixTemplateCap := by
      rw [hcard]
      unfold prefixTemplateCap
      omega
    have h := A.actual_short_witness_count hGood a b hR hseed he hcap hpos.1.le
      (prefixDensity_le_one n) hpos.2
    change _ ≤ prefixTemplateFactor n C * ((2*prefixM n)^r * prefixD n^s * prefixDensity n) at h
    have hbase : (2*prefixM n)^r * prefixD n^s ≤ (4*prefixM n)^r * (2*prefixD n)^s :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) (by nlinarith) r)
        (pow_le_pow_left₀ hD0.le (by linarith) s) (by positivity) (by positivity)
    calc
      _ ≤ prefixTemplateFactor n C * ((2*prefixM n)^r * prefixD n^s * prefixDensity n) := h
      _ = (prefixTemplateFactor n C * prefixDensity n) * ((2*prefixM n)^r * prefixD n^s) := by ring
      _ ≤ (prefixD n^50)⁻¹ * ((4*prefixM n)^r * (2*prefixD n)^s) :=
        mul_le_mul hshort hbase (by positivity) (by positivity)
      _ = _ := by rw [div_eq_mul_inv]; ring
  · have hs100 : 100 ≤ s := Nat.le_of_not_gt hs
    let k := 2*r+(s-100)
    have hkr : 2*r ≤ k := by dsimp [k]; omega
    have hk : k < (A.pathUnion a b).card := by rw [hcard]; dsimp [k]; omega
    have hdiff : (A.pathUnion a b).card-k = 100 := by rw [hcard]; dsimp [k]; omega
    have hscale' : (n : ℝ)^((A.pathUnion a b).card-k) *
        prefixDensity n^(2*((A.pathUnion a b).card-k)+1) ≤ 1 := by
      simpa only [hdiff] using hscale
    have h := A.actual_long_witness_count hGood hsmall a b hR hseed he k hkr hk
      (by rw [hdiff]; norm_num [prefixTemplateCap]) hpos.1.le (prefixDensity_le_one n) hpos.2 hscale'
    have hks : k-2*r = s-100 := by dsimp [k]; omega
    rw [hks] at h
    calc
      _ ≤ prefixTemplateFactor n C * ((4*prefixM n)^r * (2*prefixD n)^(s-100)) := h
      _ ≤ ((2*prefixD n)^100 / prefixD n^50) * ((4*prefixM n)^r * (2*prefixD n)^(s-100)) :=
        mul_le_mul_of_nonneg_right hlong (by positivity)
      _ = _ := by
        have hp : (2*prefixD n)^100 * (2*prefixD n)^(s-100) = (2*prefixD n)^s := by
          rw [← pow_add,Nat.add_sub_of_le hs100]
        rw [div_mul_eq_mul_div]
        congr 1
        calc
          _ = (4*prefixM n)^r * ((2*prefixD n)^100 * (2*prefixD n)^(s-100)) := by ring
          _ = _ := by rw [hp]

end SharpTerminalLeave

end

end OAI
