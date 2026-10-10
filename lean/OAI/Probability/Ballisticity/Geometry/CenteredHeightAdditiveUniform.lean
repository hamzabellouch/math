import Mathlib
import OAI.Probability.Ballisticity.Estimates.WeakAddTendsto

namespace OAI

section
section
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Pointwise Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical BoundedContinuousFunction
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical
namespace DirectionalTransience

theorem centered_height_additive_uniform {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : ℕ → Ω → ℝ)
    (hF : ∀ h, Measurable (F h)) (b : ℕ → ℝ) (hb0 : b 0 = 0) (r n : ℕ → ℝ)
    (hn : Tendsto n atTop atTop) (V : ℝ) (hV : 0 ≤ V)
    (hlim : ∀ T : ℝ, 0 < T → ∃ W : ProbabilityMeasure C(unitInterval,ℝ),
      TendstoInDistribution (fun i x => heightPolygon (fun h => F h x-b h) (r i) (n i) T)
        atTop id (fun _ => μ) W ∧
      ∀ I : Finset unitInterval,
        (W : Measure C(unitInterval,ℝ)).map (fun g : C(unitInterval,ℝ) => I.restrict g) = gaussianPathFiniteLaw (T*V) I)
    (p : ℝ) (hp : 0 < p)
    (hd : ∀ k j : ℕ, 0 < k → 0 < j →
      ENNReal.ofReal p • (μ.prod μ).map (fun P => F k P.1+F j P.2) ≤ μ.map (F (k+j)))
    (T : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in atTop, ∀ k j : ℕ, ((k+j:ℕ):ℝ) ≤ T*n i →
      |(b (k+j)-b k-b j)/r i| < ε := by
  let S := max T 1
  have hS : 0 < S := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨N,hN⟩ := eventually_atTop.mp (hn.eventually (eventually_gt_atTop (0:ℝ)))
  by_contra hf
  simp only [eventually_atTop,not_exists,not_forall] at hf
  have hex (l : ℕ) : ∃ i ≥ max l N, ∃ k j : ℕ,
      ((k+j:ℕ):ℝ) ≤ T*n i ∧ ε ≤ |(b (k+j)-b k-b j)/r i| := by
    obtain ⟨i,hi,hbreak⟩ := hf (max l N)
    push Not at hbreak
    obtain ⟨k,j,hkj,hbad⟩ := hbreak
    exact ⟨i,hi,k,j,hkj,hbad⟩
  choose a ha k j hkj hbad using hex
  have halim : Tendsto a atTop atTop := tendsto_atTop_mono (fun l => le_trans (le_max_left _ _) (ha l)) tendsto_id
  have hna (l : ℕ) : 0 < n (a l) := hN _ (le_trans (le_max_right _ _) (ha l))
  have hbounds (l : ℕ) : ((k l+j l:ℕ):ℝ) ≤ S*n (a l) :=
    (hkj l).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (hna l).le)
  have hkpos (l : ℕ) : 0 < k l := by
    by_contra hh
    have hz : k l = 0 := by omega
    have hb := hbad l
    simp [hz,hb0] at hb
    linarith
  have hjpos (l : ℕ) : 0 < j l := by
    by_contra hh
    have hz : j l = 0 := by omega
    have hb := hbad l
    simp [hz,hb0] at hb
    linarith
  have hx (l : ℕ) : (k l:ℝ)/n (a l) ∈ Set.Icc 0 S := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) (hna l).le,(div_le_iff₀ (hna l)).mpr ?_⟩
    exact le_trans (by exact_mod_cast Nat.le_add_right (k l) (j l)) (hbounds l)
  have hy (l : ℕ) : (j l:ℝ)/n (a l) ∈ Set.Icc 0 S := by
    refine ⟨div_nonneg (Nat.cast_nonneg _) (hna l).le,(div_le_iff₀ (hna l)).mpr ?_⟩
    exact le_trans (by exact_mod_cast Nat.le_add_left (j l) (k l)) (hbounds l)
  obtain ⟨s,_,q,hq,hqs⟩ := isCompact_Icc.tendsto_subseq hx
  obtain ⟨t,_,u,hu,hut⟩ := isCompact_Icc.tendsto_subseq (fun i => hy (q i))
  let v := fun i => a (q (u i))
  have hv : Tendsto v atTop atTop := halim.comp (hq.tendsto_atTop.comp hu.tendsto_atTop)
  obtain ⟨W,hW,hWf⟩ := hlim S hS
  have hsub : TendstoInDistribution
      (fun i x => heightPolygon (fun h => F h x-b h) (r (v i)) (n (v i)) S)
      atTop id (fun _ => μ) W :=
    ⟨fun i => hW.forall_aemeasurable (v i),hW.aemeasurable_limit,hW.tendsto.comp hv⟩
  have hadd := centered_height_additive_sequence μ F hF b (r ∘ v) (n ∘ v)
    (fun i => hna (q (u i))) S V hS hV W hsub hWf p hp hd
    (fun i => k (q (u i))) (fun i => j (q (u i)))
    (fun i => hkpos _) (fun i => hjpos _) (fun i => hbounds _)
    (hqs.comp hu.tendsto_atTop) hut
  have he := hadd.abs.eventually (gt_mem_nhds (show |(0:ℝ)| < ε by simpa using hε))
  obtain ⟨i,hi⟩ := he.exists
  exact not_lt_of_ge (hbad (q (u i))) hi

end DirectionalTransience

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology Classical

end
end

end OAI
