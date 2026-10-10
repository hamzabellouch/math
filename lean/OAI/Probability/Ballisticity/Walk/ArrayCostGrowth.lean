import Mathlib
import OAI.Probability.Ballisticity.Stationary.ArrayWindowMarks
import OAI.Probability.Ballisticity.Stationary.ArrayPermutation
import OAI.Probability.Ballisticity.Walk.StationaryGrowth
import OAI.Probability.Ballisticity.Stationary.ArrayMarkTests

namespace OAI

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Classical Topology BigOperators
namespace DirectionalTransience

noncomputable def arrayRealCost {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : ℝ := (Y.1 0).2.2.toReal
lemma arrayRealCost_measurable {d : ℕ} (e : Direction d) : Measurable (arrayRealCost e) := by
  exact (show Measurable (fun Y : ActualEpisodeArray e => (Y.1 0).2.2) from by fun_prop).ennreal_toReal
lemma arrayRealCost_nonneg {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e) : 0≤arrayRealCost e Y := ENNReal.toReal_nonneg

lemma arrayWindowCost_toReal {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hc : ∀ j, (Y.1 j).2.2≠⊤) (m : ℕ) :
    (arrayWindowCost e 0 m Y).toReal=∑ j∈Finset.range m, arrayRealCost e (StationaryCompact.shift^[j] Y) := by
  rw [arrayWindowCost,ENNReal.toReal_sum (fun (j : ℕ) _ => hc (0+(j:ℤ)))]
  apply Finset.sum_congr rfl
  intro j _
  simp only [arrayRealCost,arrayMark_iterate]

lemma expNeg_toReal_of_ne_top (C : ℝ≥0∞) (hc : C≠⊤) : (expNeg C).toReal=Real.exp (-C.toReal) := by
  rw [←ENNReal.ofReal_toReal hc]
  unfold expNeg
  rw [EReal.coe_ennreal_ofReal,max_eq_left ENNReal.toReal_nonneg,←EReal.coe_neg,EReal.exp_coe,
    ENNReal.toReal_ofReal (Real.exp_nonneg _)]
  rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]

lemma array_cost_decay_of_growth {d : ℕ} (e : Direction d) (Y : ActualEpisodeArray e)
    (hc : ∀ j, (Y.1 j).2.2≠⊤) (ζ : ℝ) (hζ : 0<ζ) (ns : ℕ → ℕ) (hns : StrictMono ns)
    (hg : ∀ᶠ k in atTop, ζ*(ns k:ℝ)<∑ j∈Finset.range (ns k), arrayRealCost e (StationaryCompact.shift^[j] Y)) :
    ∀ ε : ℝ, 0<ε → ∃ m, (expNeg (arrayWindowCost e 0 m Y)).toReal<ε := by
  have ht : Tendsto (fun k => ζ*(ns k:ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop).const_mul_atTop hζ
  have he := Real.tendsto_exp_neg_atTop_nhds_zero.comp ht
  intro ε hε
  obtain ⟨k,hk,hk'⟩ := (hg.and (he.eventually (gt_mem_nhds hε))).exists
  refine ⟨ns k,?_⟩
  have hf : arrayWindowCost e 0 (ns k) Y≠⊤ := by
    unfold arrayWindowCost
    exact ENNReal.sum_ne_top.mpr fun j _ => hc (0+j)
  rw [expNeg_toReal_of_ne_top _ hf,arrayWindowCost_toReal e Y hc]
  exact (Real.exp_lt_exp.mpr (neg_lt_neg hk)).trans hk'

lemma array_growth_symmetry {d : ℕ} (e : Direction d) (μ : Measure (ActualEpisodeArray e))
    (g : ActualEpisodeArray e → ℝ) (ns : ℕ → ℕ)
    (hlim : ∀ᵐ Y ∂μ, Tendsto (fun k => orbitAverage StationaryCompact.shift
      (fun Y => min (arrayRealCost e Y) 1) (ns k) Y) atTop (𝓝 (g Y)))
    (hperm : ∀ σ, MeasurePreserving (arrayPerm e σ) μ μ) (σ : Equiv.Perm ℕ) :
    ∀ᵐ Y ∂μ, g (arrayPerm e σ Y)=g Y := by
  exact growth_limit_respects_symmetry μ ns hlim (hperm σ) (fun Y => rfl) (fun Y => rfl)

end DirectionalTransience

end

end OAI
