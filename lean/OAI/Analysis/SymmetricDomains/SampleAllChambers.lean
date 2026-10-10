import Mathlib
import OAI.Analysis.SymmetricDomains.DecayWeightDeriv

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061.SignElimination
open Polynomial Set Filter
open scoped Topology BigOperators Classical

lemma same_sign_of_mul_pos {a b : ℝ} (h : 0 < a*b) :
    SignType.sign a = SignType.sign b := by
  rcases mul_pos_iff.mp h with h | h
  · rw [sign_pos h.1,sign_pos h.2]
  · rw [sign_neg h.1,sign_neg h.2]

theorem sample_nonzero_chamber {ι : Type*} [Fintype ι]
    (Q : ι → ℝ[X]) {x : ℝ} (hx : (∏ i, Q i).eval x ≠ 0) :
    ∃ y : ℝ, (criticalSampler (∏ i, Q i)).eval y = 0 ∧
      ∀ i, SignType.sign ((Q i).eval y) = SignType.sign ((Q i).eval x) := by
  classical
  let P := ∏ i, Q i
  let E : Set ℝ := {y | ∀ i, 0 ≤ (Q i).eval x * (Q i).eval y}
  have hEc : IsClosed E := by
    simp only [E,ofPred_forall]
    exact isClosed_iInter fun i => isClosed_le continuous_const
      ((Q i).continuous.const_mul ((Q i).eval x))
  have hxE : x ∈ E := fun i => mul_self_nonneg _
  have hxp : 0 < decayWeight P x := by
    exact div_pos (sq_pos_of_ne_zero hx) (by positivity)
  have hbound : ∀ᶠ t in cocompact ℝ ⊓ 𝓟 E, decayWeight P t ≤ decayWeight P x := by
    exact Filter.Eventually.filter_mono inf_le_left
      (((decayWeight_tendsto P).eventually (gt_mem_nhds hxp)).mono fun _ h => h.le)
  obtain ⟨y,hyE,hmax⟩ := (decayWeight_continuous P).continuousOn.exists_isMaxOn' hEc hxE hbound
  have hyp : 0 < decayWeight P y := hxp.trans_le (hmax hxE)
  have hyP : P.eval y ≠ 0 := by
    intro hy
    simp [decayWeight,hy] at hyp
  have hxQ : ∀ i, (Q i).eval x ≠ 0 := by
    simpa only [eval_prod,Finset.prod_ne_zero_iff,Finset.mem_univ,true_implies] using hx
  have hyQ : ∀ i, (Q i).eval y ≠ 0 := by
    simpa only [P,eval_prod,Finset.prod_ne_zero_iff,Finset.mem_univ,true_implies] using hyP
  have hstrict : ∀ i, 0 < (Q i).eval x * (Q i).eval y := by
    intro i
    exact lt_of_le_of_ne (hyE i) (Ne.symm (mul_ne_zero (hxQ i) (hyQ i)))
  have hE_nhds : E ∈ 𝓝 y := by
    have each : ∀ i, ∀ᶠ t in 𝓝 y, 0 ≤ (Q i).eval x * (Q i).eval t := by
      intro i
      exact (((Q i).continuous.const_mul ((Q i).eval x)).continuousAt.eventually_const_lt
        (hstrict i)).mono fun _ h => h.le
    exact Filter.eventually_all.mpr each
  have hd := (hmax.isLocalMax hE_nhds).hasDerivAt_eq_zero (decayWeight_deriv P y)
  have hden : (1+y^2)^(P.natDegree+2) ≠ 0 := pow_ne_zero _ (by positivity)
  have hz : (criticalSampler P).eval y = 0 := by
    rw [div_eq_zero_iff] at hd
    exact (mul_eq_zero.mp (hd.resolve_right hden)).resolve_left (mul_ne_zero (by norm_num) hyP)
  exact ⟨y,hz,fun i => (same_sign_of_mul_pos (hstrict i)).symm⟩

theorem sample_all_chambers {ι : Type*} [Fintype ι]
    (Q : ι → ℝ[X]) (hQ : ∀ i, Q i ≠ 0) :
    let R := (∏ i, Q i) * criticalSampler (∏ i, Q i)
    R ≠ 0 ∧ ∀ x : ℝ, ∃ y : ℝ, R.eval y = 0 ∧
      ∀ i, SignType.sign ((Q i).eval y) = SignType.sign ((Q i).eval x) := by
  classical
  have hP : (∏ i, Q i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hQ i)
  refine ⟨mul_ne_zero hP (criticalSampler_ne_zero hP),fun x => ?_⟩
  by_cases hx : (∏ i, Q i).eval x = 0
  · exact ⟨x,by simp [eval_mul,hx],fun _ => rfl⟩
  · obtain ⟨y,hy,hs⟩ := sample_nonzero_chamber Q hx
    exact ⟨y,by simp [eval_mul,hy],hs⟩

end Release061.SignElimination

end

end OAI
