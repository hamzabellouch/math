import Mathlib

namespace OAI

section
section
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology
namespace Coulomb
lemma exists_minimizer_of_midpoint_control {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {S : Set E} (hS : IsClosed S) (hne : S.Nonempty)
    (hm : ∀ f ∈ S, ∀ g ∈ S, (1/2:ℝ) • (f+g) ∈ S)
    {J : E → ℝ} (hJ : Continuous J) (hb : BddBelow (J '' S))
    (hconv : ∀ f ∈ S, ∀ g ∈ S, J ((1/2:ℝ) • (f+g)) ≤ (J f+J g)/2)
    (hR : ∀ a : ℝ, ∃ R : ℝ, 0 < R ∧ ∀ f ∈ S, J f ≤ a → ‖f‖ ≤ R)
    (hgap : ∀ R : ℝ, 0 < R → ∃ C : ℝ, 0 < C ∧
      ∀ f ∈ S, ∀ g ∈ S, ‖f‖ ≤ R → ‖g‖ ≤ R →
        ‖f-g‖^(5/3:ℝ) ≤ C * ((J f+J g)/2 - J ((1/2:ℝ) • (f+g)))^(5/6:ℝ)) :
    ∃ f ∈ S, ∀ g ∈ S, J f ≤ J g := by
  let I := sInf (J '' S)
  obtain ⟨u, hu, hulim, huS⟩ := exists_seq_tendsto_sInf (hne.image J) hb
  choose f hfS hfu using huS
  obtain ⟨R,hR0,hRb⟩ := hR (u 0)
  have hfR (n : ℕ) : ‖f n‖ ≤ R := hRb _ (hfS n) (by rw [hfu]; exact hu (Nat.zero_le n))
  obtain ⟨C,hC,hCb⟩ := hgap R hR0
  have hlow {g : E} (hg : g ∈ S) : I ≤ J g := csInf_le hb ⟨g,hg,rfl⟩
  have huI (n : ℕ) : 0 ≤ u n-I := by have := hlow (hfS n); rw [hfu] at this; linarith
  have hwlim : Tendsto (fun n => C*(u n-I)^(5/6:ℝ)) atTop (𝓝 0) := by
    have hl : Tendsto (fun n => u n-I) atTop (𝓝 (0:ℝ)) := by
      simpa only [I,sub_self] using hulim.sub_const I
    have hlr := hl.rpow_const (p := (5/6:ℝ)) (Or.inr (by norm_num))
    simpa using hlr.const_mul C
  have hcauchy : CauchySeq f := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hεp : 0 < ε^(5/3:ℝ) := Real.rpow_pos_of_pos hε _
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hwlim.eventually (gt_mem_nhds hεp))
    refine ⟨N,fun m hm' n hn' => ?_⟩
    have hmid := hlow (hm _ (hfS m) _ (hfS n))
    have hg0 : 0 ≤ (J (f m)+J (f n))/2-J ((1/2:ℝ) • (f m+f n)) := by
      exact sub_nonneg.mpr (hconv _ (hfS m) _ (hfS n))
    have hgup : (J (f m)+J (f n))/2-J ((1/2:ℝ) • (f m+f n)) ≤ u N-I := by
      have hum := hu hm'
      have hun := hu hn'
      rw [← hfu m] at hum
      rw [← hfu n] at hun
      linarith
    have H := (hCb _ (hfS m) _ (hfS n) (hfR m) (hfR n)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hg0 hgup (by norm_num : (0:ℝ)≤5/6)) hC.le)
    have Hlt := H.trans_lt (hN N le_rfl)
    have hd : ‖f m-f n‖ < ε := (Real.rpow_lt_rpow_iff (norm_nonneg _) hε.le (by norm_num : (0:ℝ)<5/3)).mp Hlt
    simpa only [dist_eq_norm] using hd
  obtain ⟨g,hg⟩ := cauchySeq_tendsto_of_complete hcauchy
  have hgS : g ∈ S := hS.mem_of_tendsto hg (Eventually.of_forall hfS)
  have hJI : J g = I := by
    apply tendsto_nhds_unique (hJ.continuousAt.tendsto.comp hg)
    simpa only [Function.comp_def,hfu] using hulim
  exact ⟨g,hgS,fun x hx => by rw [hJI]; exact hlow hx⟩
end Coulomb

open MeasureTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical Topology

end
end

end OAI
