import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.StrictnessGapPos

namespace OAI

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring
variable {V : Type*} [MetricSpace V] [DecidableEq V]

lemma execution_cluster_cost_ge_one (D C : Finset V) (hCD : C ⊆ D) (hC : C.Nonempty)
    {steps : ℕ} {v lam eta : ℝ} (E : ValidExecution D V steps v lam eta)
    (hloc : ∀ j, E.location j = j.val) (i : V) (hi : i ∈ E.regular) :
    1 ≤ ∑ p ∈ C, dist p i := by
  obtain ⟨p,hp⟩ := hC
  have h := E.far_initially ⟨p,hCD hp⟩ i hi
  rw [hloc,dist_comm] at h
  exact h.trans (Finset.single_le_sum (fun q _ => (dist_nonneg : 0 ≤ dist q i)) hp)

lemma execution_comparison_cost_ge_one (F D O : Finset V) (hO : O.Nonempty)
    (hD : D.Nonempty) (hOF : O ⊆ F) {steps : ℕ} {v lam eta : ℝ}
    (E : ValidExecution D V steps v lam eta) (hloc : ∀ j, E.location j = j.val)
    (hF : E.regular = F) : 1 ≤ cost D O := by
  obtain ⟨p,hp⟩ := hD
  have h := E.far_initially ⟨p,hp⟩ (nearest O hO p) (hF ▸ hOF (nearest_mem O hO p))
  rw [hloc,dist_comm,nearest_distance] at h
  exact h.trans (Finset.single_le_sum (fun p _ => connection_nonneg O p) hp)

theorem small_price_execution_low_sensitive (F D O S : Finset V)
    (hO : O.Nonempty) (hD : D.Nonempty) (hOF : O ⊆ F)
    (N : ℕ) (hN : 0 < N) (hcard : O.card ≤ N)
    {steps : ℕ} (v : ℝ) (E : ValidExecution D V steps v (2/(N:ℝ)^2) 0)
    (hloc : ∀ j, E.location j = j.val) (hF : E.regular = F)
    (hSQ : cost D S ≤ ∑ j, nearestDistance (E.location j) (E.state steps).opened)
    (hv : 0 < v) (hv1 : v ≤ 1/12)
    (hvc : v ≤ strictnessGap (200*countConstant (1/100))/1000)
    (hsmall : v^2 ≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (hsize : 2/(N:ℝ) ≤ strictnessGap (200*countConstant (1/100))/200) :
    cost D S ≤ (2-strictnessGap (200*countConstant (1/100))/100)*cost D O := by
  classical
  let C := countConstant (1/100)
  let c := strictnessGap (200*C)
  let lam := 2/(N:ℝ)^2
  let P := cost D O
  let Q := ∑ j, nearestDistance (E.location j) (E.state steps).opened
  let alpha := extendBudget D (E.state steps).budget
  have hC : 10 ≤ C := by
    dsimp [C,countConstant]
    have hh : 0 ≤ (600/(1/100:ℝ))*(2:ℝ)^(rounds (1/100)-1) := by positivity
    linarith only [hh]
  have hT : 0 < 200*C := by linarith
  have hc : 0 < c := strictnessGap_pos hT
  have hc1 : c ≤ 1 := strictnessGap_le_one hT
  have hv6 : v < 1/6 := by linarith
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hN
  have hNR1 : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hlam2 : lam ≤ 2 := by
    dsimp [lam]
    apply (div_le_iff₀ (sq_pos_of_pos hNR)).mpr
    nlinarith only [hNR1]
  have hP1 : 1 ≤ P := execution_comparison_cost_ge_one F D O hO hD hOF E hloc hF
  have hpayment : (1-3*v)*Q ≤ ∑ p ∈ D, alpha p := by
    have h := valid_execution_payment v lam 0 E ∅ (Finset.empty_subset _) (by simp) hv6
    simp only [Finset.card_empty,Nat.cast_zero,zero_mul,add_zero] at h
    rw [sum_extended_budget]
    exact h
  have hstrict (i : V) (hi : i ∈ O) :
      (∑ p ∈ cluster D (nearest O hO) i, alpha p) ≤
        lam+(2-c/2)*clusterCost D (nearest O hO) i := by
    by_cases hne : (cluster D (nearest O hO) i).Nonempty
    · have hp := execution_cluster_cost_ge_one D (cluster D (nearest O hO) i)
        (Finset.filter_subset _ _) hne E hloc i (hF ▸ hOF hi)
      change 1 ≤ clusterCost D (nearest O hO) i at hp
      have hprice : lam ≤ 200*C*clusterCost D (nearest O hO) i := by
        nlinarith only [hp,hC,hlam2]
      exact execution_strict_on_points D (cluster D (nearest O hO) i)
        (Finset.filter_subset _ _) hne v lam 0 (200*C) E hloc i (hF ▸ hOF hi)
        hv hv6 hlam hT (show 0 < clusterCost D (nearest O hO) i by linarith only [hp]) hprice hsmall
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [clusterCost,hz,Finset.sum_empty,mul_zero,add_zero]
      exact hlam.le
  have hrow (i : V) (hi : i ∈ O) :
      (∑ p ∈ cluster D (nearest O hO) i, alpha p) ≤ lam+2*clusterCost D (nearest O hO) i := by
    have hg := hstrict i hi
    have hpos := mul_nonneg hc.le (clusterCost_nonneg D (nearest O hO) i)
    nlinarith only [hg,hpos]
  have hg := aggregate_gain D O O hO (Finset.Subset.refl _) alpha lam c hrow hstrict
  rw [total_cluster_cost] at hg
  have hnlam : (N:ℝ)*lam = 2/(N:ℝ) := by
    dsimp [lam]
    field_simp
  have hpayprice : (O.card:ℝ)*lam ≤ (c/200)*P := by
    have hcast : (O.card:ℝ) ≤ N := by exact_mod_cast hcard
    have hh := mul_le_mul_of_nonneg_right hcast hlam.le
    rw [hnlam] at hh
    have hp := mul_le_mul_of_nonneg_left hP1 (by positivity : 0 ≤ c/200)
    exact hh.trans (hsize.trans (by simpa only [mul_one] using hp))
  have hA : (∑ p ∈ D, alpha p) ≤ (2-c/2+c/200)*P := by
    dsimp [P] at *
    linarith only [hg,hpayprice]
  exact hSQ.trans (small_price_strict Q P c v _ (by linarith only [hP1]) hc hv hv1 hvc hpayment hA)

end MetricKMedianRecovery.Surplus

end OAI
