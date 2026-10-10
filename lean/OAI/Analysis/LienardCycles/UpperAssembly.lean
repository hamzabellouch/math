import OAI.Analysis.LienardCycles.CycleTransform

namespace OAI

open scoped Topology NNReal ContDiff Manifold
open Filter Set
open Set Filter Metric MeasureTheory
open scoped Topology NNReal ContDiff
open scoped Topology ENNReal
open Set Filter MeasureTheory
open Set Filter Asymptotics
open Set Filter Metric
open scoped Topology NNReal
open scoped Topology ContDiff NNReal
open scoped Topology ContDiff
open Set Filter
open scoped Topology

open Set Filter
open scoped Topology ContDiff
namespace QuinticLienard
open ScaledProfile AxisFlow RealAnalysis
lemma no_isolated_zero_of_zero_on {f : ℝ → ℝ} {J : Set ℝ} (hJ : IsOpen J)
    (hz : ∀ x ∈ J,f x=0) (x : ℝ) : ¬IsIsolatedZeroOn f J x := by
  rintro ⟨hx,_,ε,hε,hiso⟩
  have he : ∀ᶠ y in 𝓝[>] x,x<y ∧ y ∈ J ∧ y ∈ Ioo (x-ε) (x+ε) := by
    filter_upwards [self_mem_nhdsWithin,(show ∀ᶠ y in 𝓝 x,y∈J from hJ.mem_nhds hx).filter_mono inf_le_left,
      (show ∀ᶠ y in 𝓝 x,y∈Ioo (x-ε) (x+ε) from Ioo_mem_nhds (by linarith) (by linarith)).filter_mono inf_le_left] with y hy hyJ hyI
    exact ⟨hy,hyJ,hyI⟩
  obtain ⟨y,hxy,hyJ,hyI⟩ := he.exists
  exact (ne_of_gt hxy) (hiso y hyI hyJ (hz y hyJ))
lemma reflectX_eq_of_even {a : Fin 6 → ℝ} (h1 : a 1=0) (h3 : a 3=0) (h5 : a 5=0) : reflectX a=a := by
  ext i
  fin_cases i <;> simp [reflectX,h1,h3,h5]
lemma no_isolated_matching_even {a : Fin 6 → ℝ} (h1 : a 1=0) (h3 : a 3=0) (h5 : a 5=0) :
    {r | IsIsolatedZeroOn (matchingDelta a (reflectX a)) (matchingDomain a (reflectX a)) r}=∅ := by
  apply eq_empty_of_forall_notMem
  intro r
  apply no_isolated_zero_of_zero_on (matchingDomain_open a (reflectX a))
  intro x _
  rw [matchingDelta,reflectX_eq_of_even h1 h3 h5,sub_self]
lemma upper_nonnegative {F : Polynomial ℝ} {a : Fin 6 → ℝ}
    (hF : ∀ x,F.eval x=poly a x) (h5 : 0≤a 5) : {C : Set Plane | IsLimitCycle F C}.encard≤2 := by
  by_cases h1 : 0≤a 1
  · by_cases h3 : 0≤a 3
    · by_cases hz : a 1=0 ∧ a 3=0 ∧ a 5=0
      · have H := limitCycle_encard_le_matching hF
        rw [no_isolated_matching_even hz.1 hz.2.1 hz.2.2,encard_empty] at H
        exact H.trans (by norm_num)
      · have hne : a 1≠0 ∨ a 3≠0 ∨ a 5≠0 := by tauto
        have he : {C : Set Plane | IsLimitCycle F C}=∅ := by
          apply eq_empty_of_forall_notMem
          intro C hC
          exact no_periodic_case1 hF h1 h3 h5 hne hC.1
        rw [he,encard_empty]
        norm_num
    · exact (limitCycle_encard_le_matching hF).trans (matching_isolated_case2 h1 (lt_of_not_ge h3) h5)
  · by_cases h3 : 0≤a 3
    · exact (limitCycle_encard_le_matching hF).trans (matching_isolated_case3 (lt_of_not_ge h1) h3 h5)
    · exact (limitCycle_encard_le_matching hF).trans (matching_isolated_case4 (lt_of_not_ge h1) (lt_of_not_ge h3) h5)
lemma quintic_representation {F : Polynomial ℝ} (hF : F.degree≤5) : ∀ x,F.eval x=poly (fun i : Fin 6=>F.coeff i) x := by
  have hd : F.natDegree≤5 := Polynomial.natDegree_le_of_degree_le hF
  intro x
  rw [Polynomial.eval_eq_sum_range' (show F.natDegree<6 by omega)]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,pow_zero,mul_one,pow_one,poly]
  norm_num
lemma upper_bound (F : Polynomial ℝ) (hF : F.degree≤5) : {C : Set Plane | IsLimitCycle F C}.encard≤2 := by
  by_cases h5 : 0≤F.coeff 5
  · exact upper_nonnegative (quintic_representation hF) h5
  · rw [limitCycle_encard_neg F]
    have hd : (-F).degree≤5 := by simpa only [Polynomial.degree_neg] using hF
    apply upper_nonnegative (quintic_representation hd)
    simpa using (neg_nonneg.mpr (le_of_not_ge h5))
end QuinticLienard

end OAI
