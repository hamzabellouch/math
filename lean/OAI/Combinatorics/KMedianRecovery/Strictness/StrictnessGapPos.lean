import Mathlib
import OAI.Combinatorics.KMedianRecovery.Algorithms.ExtendBudget
import OAI.Combinatorics.KMedianRecovery.Recovery.ShortPrice

namespace OAI

namespace MetricKMedianRecovery.Surplus
open MetricKMedianRecovery.LocalSearch MetricKMedianRecovery.Anchoring

lemma strictnessGap_pos {T : ℝ} (hT : 0 < T) : 0 < strictnessGap T := by
  unfold strictnessGap
  positivity
lemma strictnessGap_le_one {T : ℝ} (hT : 0 < T) : strictnessGap T ≤ 1 := by
  have hd : 1 ≤ 200*(T+2) := by linarith
  have ht : 0 < 200*(T+2) := by positivity
  have hq : 1/(200*(T+2)) ≤ (1:ℝ) := (div_le_iff₀ ht).mpr (by nlinarith only [hd])
  have hq0 : 0 ≤ 1/(200*(T+2)) := by positivity
  unfold strictnessGap
  nlinarith

variable {V : Type*} [MetricSpace V] [DecidableEq V] [Fintype V]

omit [Fintype V] [MetricSpace V] [DecidableEq V] in
lemma sum_extended_budget (D : Finset V) (alpha : D → ℝ) :
    (∑ p ∈ D, extendBudget D alpha p) = ∑ j, alpha j := by
  rw [← Finset.sum_coe_sort D (extendBudget D alpha)]
  exact Finset.sum_congr rfl (fun j _ => extendBudget_at D alpha j)

omit [Fintype V] in
lemma execution_cost_nonneg (D : Finset V) {steps : ℕ} {v lam eta : ℝ}
    (E : ValidExecution D V steps v lam eta) :
    0 ≤ ∑ j, nearestDistance (E.location j) (E.state steps).opened := by
  apply Finset.sum_nonneg
  intro j _
  unfold nearestDistance
  split_ifs with h
  · exact Finset.le_inf' h _ (fun _ _ => dist_nonneg)
  · exact le_rfl

theorem normal_execution_low_sensitive (F D O S H : Finset V)
    (hO : O.Nonempty) (hS : S.Nonempty) (hH : H.Nonempty)
    (hOF : O ⊆ F) (hSF : S ⊆ F) (hHF : H ⊆ F) (hO2 : 2 ≤ O.card)
    (L : ℕ) (hcard : S.card = O.card+L) (hHL : H.card+L = O.card)
    (hlocal : WidthLocalMin F D S 5) (hP : 0 < cost D O)
    {steps : ℕ} (v lam eta xi : ℝ) (E : ValidExecution D V steps v lam eta)
    (hloc : ∀ j, E.location j = j.val) (hF : E.regular = F)
    (paid : Finset ℕ) (hpaid : paid ⊆ Finset.range steps)
    (hregular : ∀ n ∈ paid, CertifiedRegularStep E.location E.regular v lam eta
      (E.state n) (E.state (n+1))) (hcount : paid.card = O.card)
    (hSQ : cost D S ≤ ∑ j, nearestDistance (E.location j) (E.state steps).opened)
    (hHcost : cost D H ≤ (1+xi)*cost D O) (hxi : xi ≤ 1)
    (hlam : 0 < lam) (hv : 0 < v) (hv1 : v ≤ 1/12)
    (hvc : v ≤ strictnessGap (200*countConstant (1/100))/1000)
    (hsmall : v^2 ≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (herr : (O.card:ℝ)*D.card*eta ≤ v*cost D O) :
    cost D S ≤ (2-strictnessGap (200*countConstant (1/100))/100)*cost D O := by
  classical
  let C := countConstant (1/100)
  let c := strictnessGap (200*C)
  have hC : 0 < C := by dsimp [C,countConstant]; positivity
  have hT : 0 < 200*C := by positivity
  have hc : 0 < c := strictnessGap_pos hT
  have hc1 : c ≤ 1 := strictnessGap_le_one hT
  have hv6 : v < 1/6 := by linarith
  let alpha := extendBudget D (E.state steps).budget
  let Q := ∑ j, nearestDistance (E.location j) (E.state steps).opened
  have hpayment : (1-3*v)*Q+O.card*lam-(O.card:ℝ)*D.card*eta ≤ ∑ p ∈ D, alpha p := by
    have h := valid_execution_payment v lam eta E paid hpaid hregular hv6
    rw [hcount,Fintype.card_coe] at h
    rw [sum_extended_budget]
    calc
      _ = (1-3*v)*Q+(O.card:ℝ)*(lam-D.card*eta) := by ring
      _ ≤ _ := h
  have hdual (i : V) (hi : i ∈ F) : (∑ p ∈ D, max (alpha p-2*dist i p) 0) ≤ lam :=
    execution_dual_on_points D v lam eta E hloc hv hv6 hlam i (hF ▸ hi)
  have hstrict (i : V) (hi : i ∈ O)
      (hprice : lam ≤ (200*C)*clusterCost D (nearest O hO) i) :
      (∑ p ∈ cluster D (nearest O hO) i, alpha p) ≤
        lam+(2-c/2)*clusterCost D (nearest O hO) i := by
    have hP' : 0 < clusterCost D (nearest O hO) i := by
      by_contra hg
      have hle : clusterCost D (nearest O hO) i ≤ 0 := le_of_not_gt hg
      nlinarith only [hT,hprice,hlam,hle]
    have hne : (cluster D (nearest O hO) i).Nonempty := by
      by_contra hn
      have hz := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [clusterCost,hz,Finset.sum_empty] at hP'
      exact (lt_irrefl _ hP')
    exact execution_strict_on_points D (cluster D (nearest O hO) i) (Finset.filter_subset _ _)
      hne v lam eta (200*C) E hloc i (hF ▸ hOF hi) hv hv6 hlam hT hP' hprice hsmall
  exact low_sensitive_cost F D O S H hO hS hH hOF hSF hHF hO2 L hcard hHL hlocal hP
    alpha lam Q ((O.card:ℝ)*D.card*eta) xi v c C hlam (execution_cost_nonneg D E) hSQ
    hHcost hxi hv hv1 hvc herr hc hc1 hC rfl hpayment hdual hstrict

end MetricKMedianRecovery.Surplus

end OAI
