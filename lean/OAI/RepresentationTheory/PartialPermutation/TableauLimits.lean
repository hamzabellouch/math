import Mathlib
import OAI.RepresentationTheory.PartialPermutation.TableauWeights

namespace OAI

section
namespace PartialPermutation
namespace TableauZeta
noncomputable section
open Finset Filter
open Tableau DiagramCounting

lemma deficitTerm_zero (n : ℕ) (u : ℝ) : deficitTerm n u 0=0 := by
  apply Finset.sum_eq_zero
  intro μ _
  unfold inverseWeight
  have he : deficit μ.1.1=0 := μ.2
  simp only [he,ite_true]

lemma deficitTerm_fixed_bound (n : ℕ) (u : ℝ) (hu : 0 < u) (k : ℕ) (hk : 0 < k)
    (hkn : 2*k≤n) :
    deficitTerm n u k ≤ 2*(partitionCount k:ℝ)*((n-2*k+1:ℕ):ℝ)^(-u) := by
  have hcard : (Fintype.card (ShapeDeficit n k):ℝ) ≤ 2*partitionCount k := by
    exact_mod_cast deficit_count_le n k
  calc
    deficitTerm n u k ≤ ∑ μ : ShapeDeficit n k, ((n-2*k+1:ℕ):ℝ)^(-u) := by
      apply Finset.sum_le_sum
      intro μ _
      have hdef : deficit μ.1.1=k := μ.2
      have hsize : μ.1.1.cells.card=n := μ.1.2
      have hcount := fixed_deficit_growth μ.1.1 (by simpa only [hdef] using hk) (by simpa only [hdef,hsize] using hkn)
      rw [hdef,hsize] at hcount
      unfold inverseWeight
      rw [ite_eq_right (by omega)]
      exact Real.rpow_le_rpow_of_nonpos (by positivity)
        (by exact_mod_cast hcount) (neg_nonpos.mpr hu.le)
    _ = (Fintype.card (ShapeDeficit n k):ℝ)*((n-2*k+1:ℕ):ℝ)^(-u) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcard (Real.rpow_nonneg (by positivity) _)

lemma deficitTerm_tendsto_zero (u : ℝ) (hu : 0 < u) (k : ℕ) :
    Tendsto (fun n => deficitTerm n u k) atTop (nhds 0) := by
  by_cases hk : k=0
  · subst k
    simpa only [deficitTerm_zero] using tendsto_const_nhds (x := (0:ℝ))
  · have ht : Tendsto (fun n : ℕ => n-2*k+1) atTop atTop := by
      apply tendsto_atTop.2
      intro b
      filter_upwards [eventually_ge_atTop (b+2*k)] with n hn
      omega
    have hr := (tendsto_rpow_neg_atTop hu).comp (tendsto_natCast_atTop_atTop.comp ht)
    have hr' := hr.const_mul (2*(partitionCount k:ℝ))
    simp only [mul_zero] at hr'
    apply squeeze_zero' (Eventually.of_forall (fun n => deficitTerm_nonneg n u k)) _ hr'
    filter_upwards [eventually_ge_atTop (2*k)] with n hn
    exact deficitTerm_fixed_bound n u hu k (by omega) hn

lemma tsum_deficitTerm (n : ℕ) (u : ℝ) :
    (∑' k, deficitTerm n u k) = nontrivialSum n u := by
  have hh := (hasSum_fintype (fun μ : Shape n => inverseWeight u μ.1)).tsum_fiberwise
    (fun μ : Shape n => deficit μ.1)
  change HasSum (fun k => ∑' μ : ShapeDeficit n k, inverseWeight u μ.1.1)
    (nontrivialSum n u) at hh
  simpa only [tsum_fintype,deficitTerm] using hh.tsum_eq

theorem nontrivialSum_tendsto_zero (u : ℝ) (hu : 0 < u) :
    Tendsto (fun n => nontrivialSum n u) atTop (nhds 0) := by
  have hh := tendsto_tsum_of_dominated_convergence (summable_majorant u hu)
    (deficitTerm_tendsto_zero u hu)
    (Eventually.of_forall (fun n k => deficitTerm_bound n u hu k))
  simpa only [tsum_deficitTerm,tsum_zero] using hh

lemma fullSum_bound (n : ℕ) (u : ℝ) (hu : 0 < u) :
    fullSum n u ≤ 2*partitionCount 0 + nontrivialSum n u := by
  have hi (μ : YoungDiagram) : (standardCount μ:ℝ)^(-u) ≤ 1 := by
    have hc : (1:ℝ) ≤ standardCount μ := by exact_mod_cast standardCount_pos μ
    simpa only [Real.one_rpow] using
      Real.rpow_le_rpow_of_nonpos (by norm_num) hc (neg_nonpos.mpr hu.le)
  have hc : (Fintype.card (ShapeDeficit n 0):ℝ) ≤ 2*partitionCount 0 := by
    exact_mod_cast deficit_count_le n 0
  calc
    fullSum n u ≤ ∑ μ : Shape n,
        ((if deficit μ.1=0 then (1:ℝ) else 0) + inverseWeight u μ.1) := by
      apply Finset.sum_le_sum
      intro μ _
      unfold inverseWeight
      split_ifs
      · simpa only [add_zero] using hi μ.1
      · simp only [zero_add,le_refl]
    _ = (Fintype.card (ShapeDeficit n 0):ℝ) + nontrivialSum n u := by
      rw [Finset.sum_add_distrib]
      congr 1
      change (∑ μ : Shape n, if deficit μ.1=0 then (1:ℝ) else 0) =
        (Fintype.card {μ : Shape n // deficit μ.1=0}:ℝ)
      rw [Fintype.card_subtype,Finset.sum_boole]
    _ ≤ _ := add_le_add_left hc _

theorem fullSum_bddAbove (u : ℝ) (hu : 0 < u) :
    BddAbove (Set.range (fun n => fullSum n u)) := by
  obtain ⟨a,ha⟩ := (nontrivialSum_tendsto_zero u hu).bddAbove_range
  refine ⟨2*partitionCount 0+a,?_⟩
  rintro x ⟨n,rfl⟩
  exact (fullSum_bound n u hu).trans (add_le_add_right (ha (Set.mem_range_self n)) _)

end
end TableauZeta
end PartialPermutation

end

end OAI
