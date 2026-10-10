import Mathlib
import OAI.Probability.Ballisticity.Estimates.FavorablePairFraction
import OAI.Probability.Ballisticity.Estimates.WeakTailTransfer

namespace OAI

section

section

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology
namespace DirectionalTransience

lemma capExcessTest_le_one (a : ℝ) {D : ℝ} (hD : 0 ≤ D) (x : unitInterval) :
    capExcessTest a D x ≤ 1 := by
  have hh0 : 0 ≤ min (D*(x:ℝ)) 1 := le_min (mul_nonneg hD x.2.1) zero_le_one
  have hh1 := min_le_right (D*(x:ℝ)) 1
  change max ((min (D*(x:ℝ)) 1)^2-a^2) 0 ≤ 1
  apply max_le <;> nlinarith [sq_nonneg a]

lemma capExcess_integrable (a D : ℝ) (μ : ProbabilityMeasure unitInterval) :
    Integrable (capExcessTest a D) (μ : Measure unitInterval) :=
  (capExcessTest a D).continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma capExcess_integral_bounds (a : ℝ) {D : ℝ} (hD : 0 ≤ D)
    (μ : ProbabilityMeasure unitInterval) :
    0 ≤ (∫ x, capExcessTest a D x ∂(μ : Measure unitInterval)) ∧
    (∫ x, capExcessTest a D x ∂(μ : Measure unitInterval)) ≤ 1 := by
  constructor
  · exact integral_nonneg (capExcessTest_nonneg _ _)
  · calc
      _ ≤ ∫ x : unitInterval, (1:ℝ) ∂(μ : Measure unitInterval) :=
        integral_mono (capExcess_integrable _ _ _) (integrable_const _)
          (capExcessTest_le_one a hD)
      _ = 1 := by simp

lemma compact_capped_moment_transfer
    (μs νs : ℕ → ProbabilityMeasure unitInterval)
    {C D : ℝ} (hC : 0 ≤ C) (hD : 0 < D)
    (ht : ∀ ns : ℕ → ℕ, Tendsto ns atTop atTop → ∀ u > 0, u < 1 →
      limsup (fun n => (μs (ns n) : Measure unitInterval).real {x | u < (x:ℝ)}) atTop ≤
      C * limsup (fun n => (νs (ns n) : Measure unitInterval).real {y | u/D < (y:ℝ)}) atTop)
    (a : ℝ) (ha : 0 ≤ a) :
    limsup (fun n => ∫ x, capExcessTest a 1 x ∂(μs n : Measure unitInterval)) atTop ≤
      C * limsup (fun n => ∫ y, capExcessTest a (2*D) y ∂(νs n : Measure unitInterval)) atTop := by
  let F : ℕ → ℝ := fun n => ∫ x, capExcessTest a 1 x ∂(μs n : Measure unitInterval)
  let G : ℕ → ℝ := fun n => ∫ y, capExcessTest a (2*D) y ∂(νs n : Measure unitInterval)
  have hF0 (n) : 0 ≤ F n := (capExcess_integral_bounds a (by norm_num) _).1
  have hF1 (n) : F n ≤ 1 := (capExcess_integral_bounds a (by norm_num) _).2
  have hG0 (n) : 0 ≤ G n := (capExcess_integral_bounds a (by positivity) _).1
  have hG1 (n) : G n ≤ 1 := (capExcess_integral_bounds a (by positivity) _).2
  have hFb : IsBoundedUnder (· ≤ ·) atTop F := isBoundedUnder_of ⟨1,hF1⟩
  have hFc : IsCoboundedUnder (· ≤ ·) atTop F := isCoboundedUnder_le_of_le atTop hF0
  have hGb : IsBoundedUnder (· ≤ ·) atTop G := isBoundedUnder_of ⟨1,hG1⟩
  apply (limsup_le_iff hFc hFb).mpr
  intro b hb
  by_contra hbad
  have hfreq : ∃ᶠ n in atTop, b ≤ F n := by simpa only [not_eventually,not_lt] using hbad
  obtain ⟨ns,hns,hnsb⟩ := exists_seq_forall_of_frequently hfreq
  obtain ⟨p,hp,ks,hks,hpk⟩ := isCompact_univ.tendsto_subseq
    (x := fun n => (μs (ns n),νs (ns n))) (fun _ => Set.mem_univ _)
  have hμ : Tendsto (fun n => μs (ns (ks n))) atTop (𝓝 p.1) :=
    (continuous_fst.tendsto p).comp hpk
  have hν : Tendsto (fun n => νs (ns (ks n))) atTop (𝓝 p.2) :=
    (continuous_snd.tendsto p).comp hpk
  have htail := weak_tail_comparison _ _ _ _ hμ hν hC hD
    (ht (ns ∘ ks) (hns.comp hks.tendsto_atTop))
  have hcomp := capExcess_integral_comparison p.1 p.2 hC (by positivity : 0 < 2*D) htail a ha
  have hlimF : Tendsto (F ∘ (ns ∘ ks)) atTop
      (𝓝 (∫ x, capExcessTest a 1 x ∂(p.1 : Measure unitInterval))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ)
      (BoundedContinuousFunction.mkOfCompact (capExcessTest a 1))
  have hlimG : Tendsto (G ∘ (ns ∘ ks)) atTop
      (𝓝 (∫ y, capExcessTest a (2*D) y ∂(p.2 : Measure unitInterval))) :=
    (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hν)
      (BoundedContinuousFunction.mkOfCompact (capExcessTest a (2*D)))
  have hhF := ge_of_tendsto hlimF (Eventually.of_forall fun n => hnsb (ks n))
  have hhG : (∫ y, capExcessTest a (2*D) y ∂(p.2 : Measure unitInterval)) ≤ limsup G atTop := by
    rw [← hlimG.limsup_eq]
    exact (hns.comp hks.tendsto_atTop).limsup_comp_le_limsup
      (isCoboundedUnder_le_of_le atTop (fun n => hG0 (ns (ks n)))) hGb
  exact (not_le_of_gt hb) (hhF.trans (hcomp.trans (mul_le_mul_of_nonneg_left hhG hC)))

end DirectionalTransience

end

end

end OAI
