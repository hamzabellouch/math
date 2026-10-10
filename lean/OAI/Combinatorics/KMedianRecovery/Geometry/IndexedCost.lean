import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.Dual
import OAI.Combinatorics.KMedianRecovery.Strictness.StrictnessGapPos
import OAI.Combinatorics.KMedianRecovery.Recovery.NatConnection

namespace OAI

namespace MetricKMedianRecovery.PhaseSurplusProducer
open PhaseOriginalLedger LocalSearch Anchoring Surplus
variable {V : Type*} [MetricSpace V] [DecidableEq V]

omit [DecidableEq V] in
lemma indexed_cost (D S : Finset V) :
    (∑ j : D, nearestDistance j.val S) = cost D S :=
  Finset.sum_coe_sort D (connection S)

omit [DecidableEq V] in
lemma dual_on_points (D F : Finset V) {v lam : ℝ} {alpha : D → ℝ}
    (h : Dual (fun j : D => j.val) F v lam alpha) (i : V) (hi : i ∈ F) :
    (∑ p ∈ D, max (extendBudget D alpha p-2*dist i p) 0) ≤ lam := by
  have hh := h.2.1 i hi
  rw [← Finset.sum_coe_sort D (fun p => max (extendBudget D alpha p-2*dist i p) 0)]
  simpa only [extendBudget_at] using hh

lemma strict_on_points (D C F : Finset V) (hCD : C ⊆ D) (hC : C.Nonempty)
    {v lam b : ℝ} {alpha : D → ℝ} (h : Dual (fun j : D => j.val) F v lam alpha)
    (i : V) (hi : i ∈ F) (hb : 0 < b)
    (hP : 0 < ∑ p ∈ C, dist p i) (hprice : lam ≤ b*(∑ p ∈ C, dist p i))
    (hsmall : v^2 ≤ strictnessGap b/(6*(b+2))) :
    (∑ p ∈ C, extendBudget D alpha p) ≤ lam+(2-strictnessGap b/2)*(∑ p ∈ C, dist p i) := by
  classical
  let C' := Finset.univ.filter (fun j : D => j.val ∈ C)
  have hC' : C'.Nonempty := by
    obtain ⟨p,hp⟩ := hC
    exact ⟨⟨p,hCD hp⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
  have hd : (∑ j ∈ C', dist i j.val) = ∑ p ∈ C, dist p i := by
    simpa only [dist_comm] using sum_liftSubset D C hCD (fun p => dist p i)
  have ha : (∑ j ∈ C', alpha j) = ∑ p ∈ C, extendBudget D alpha p := by
    calc
      _ = ∑ j ∈ C', extendBudget D alpha j.val :=
        Finset.sum_congr rfl (fun j _ => (extendBudget_at D alpha j).symm)
      _ = _ := sum_liftSubset D C hCD _
  have hh := h.2.2 C' hC' i hi b hb (hd ▸ hP) (hd ▸ hprice) hsmall
  simpa only [ha,hd] using hh

omit [DecidableEq V] in
lemma cluster_ge_one (D C F : Finset V) (hCD : C ⊆ D) (hC : C.Nonempty)
    (hfar : ∀ i ∈ F, ∀ p ∈ D, 1 ≤ dist i p) (i : V) (hi : i ∈ F) :
    1 ≤ ∑ p ∈ C, dist p i := by
  obtain ⟨p,hp⟩ := hC
  have hh := hfar i hi p (hCD hp)
  rw [dist_comm] at hh
  exact hh.trans (Finset.single_le_sum (fun q _ => (dist_nonneg : 0 ≤ dist q i)) hp)

omit [DecidableEq V] in
lemma comparison_ge_one (F D O : Finset V) (hD : D.Nonempty) (hO : O.Nonempty)
    (hOF : O ⊆ F) (hfar : ∀ i ∈ F, ∀ p ∈ D, 1 ≤ dist i p) : 1 ≤ cost D O := by
  obtain ⟨p,hp⟩ := hD
  have hh := hfar (nearest O hO p) (hOF (nearest_mem O hO p)) p hp
  rw [dist_comm,nearest_distance] at hh
  exact hh.trans (Finset.single_le_sum (fun p _ => connection_nonneg O p) hp)

lemma countConstant_ge_ten : (10:ℝ) ≤ countConstant (1/100) := by
  unfold countConstant
  have hh : 0 ≤ (600/(1/100:ℝ))*(2:ℝ)^(rounds (1/100)-1) := by positivity
  linarith only [hh]

lemma pad_and_descend (δ : V → V → ℕ) (F D S : Finset V) (k M : ℕ)
    (hS : S.Nonempty) (hSF : S ⊆ F) (hSk : S.card ≤ k) (hkF : k ≤ F.card)
    (hδ : ∀ p ∈ D, ∀ i ∈ F, (δ p i : ℝ) = dist p i)
    (hM : ∀ p ∈ D, ∀ i ∈ F, δ p i ≤ M) :
    ∃ T : Finset V, T ⊆ F ∧ T.Nonempty ∧ T.card = k ∧ cost D T ≤ cost D S ∧
      WidthLocalMin F D T 5 := by
  obtain ⟨U,hSU,hUF,hUk⟩ := Finset.exists_subsuperset_card_eq hSF hSk hkF
  obtain ⟨n,hn,path,hzero,hsteps,hTF,hcard,hcost,hlocal⟩ :=
    integral_bounded_descent δ F D U 5 M hUF hδ hM
  refine ⟨path n,hTF,?_,hcard.trans hUk,hcost.trans (cost_mono D hS hSU),hlocal⟩
  apply Finset.card_pos.mp
  rw [hcard,hUk]
  exact (Finset.card_pos.mpr hS).trans_le hSk

variable [Fintype V]

lemma normal_cost (F D O S H : Finset V) (hO : O.Nonempty) (hS : S.Nonempty)
    (hH : H.Nonempty) (hOF : O ⊆ F) (hSF : S ⊆ F) (hHF : H ⊆ F)
    (hO2 : 2 ≤ O.card) (L : ℕ) (hcard : S.card = O.card+L) (hHL : H.card+L = O.card)
    (hlocal : WidthLocalMin F D S 5) (hP : 0 < cost D O)
    (alpha : D → ℝ) (lam Q eta xi v : ℝ) (hdual : Dual (fun j : D => j.val) F v lam alpha)
    (hlam : 0 < lam) (hQ : 0 ≤ Q) (hSQ : cost D S ≤ Q)
    (hHcost : cost D H ≤ (1+xi)*cost D O) (hxi : xi ≤ 1)
    (hv : 0 < v) (hv1 : v ≤ 1/12)
    (hvc : v ≤ strictnessGap (200*countConstant (1/100))/1000)
    (hsmall : v^2 ≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (herr : (O.card:ℝ)*D.card*eta ≤ v*cost D O)
    (hpayment : (1-3*v)*Q+(O.card:ℝ)*(lam-(D.card:ℝ)*eta) ≤ ∑ j, alpha j) :
    cost D S ≤ (2-strictnessGap (200*countConstant (1/100))/100)*cost D O := by
  let C := countConstant (1/100)
  let c := strictnessGap (200*C)
  have hC : 0 < C := lt_of_lt_of_le (by norm_num) countConstant_ge_ten
  have hT : 0 < 200*C := by positivity
  have hc : 0 < c := strictnessGap_pos hT
  have hc1 : c ≤ 1 := strictnessGap_le_one hT
  have hpay : (1-3*v)*Q+O.card*lam-(O.card:ℝ)*D.card*eta ≤
      ∑ p ∈ D, extendBudget D alpha p := by
    rw [sum_extended_budget]
    nlinarith only [hpayment]
  have hstrict (i : V) (hi : i ∈ O)
      (hprice : lam ≤ (200*C)*clusterCost D (nearest O hO) i) :
      (∑ p ∈ cluster D (nearest O hO) i, extendBudget D alpha p) ≤
        lam+(2-c/2)*clusterCost D (nearest O hO) i := by
    have hP' : 0 < clusterCost D (nearest O hO) i := by
      by_contra hg
      have hle := le_of_not_gt hg
      nlinarith only [hT,hprice,hlam,hle]
    have hne : (cluster D (nearest O hO) i).Nonempty := by
      by_contra hn
      have hz := Finset.not_nonempty_iff_eq_empty.mp hn
      simp only [clusterCost,hz,Finset.sum_empty] at hP'
      exact (lt_irrefl _ hP')
    exact strict_on_points D _ F (Finset.filter_subset _ _) hne hdual i (hOF hi) hT hP' hprice hsmall
  exact low_sensitive_cost F D O S H hO hS hH hOF hSF hHF hO2 L hcard hHL hlocal hP
    (extendBudget D alpha) lam Q ((O.card:ℝ)*D.card*eta) xi v c C hlam hQ hSQ
    hHcost hxi hv hv1 hvc herr hc hc1 hC rfl hpay (dual_on_points D F hdual) hstrict

omit [Fintype V] in

lemma small_cost (F D O S : Finset V) (hO : O.Nonempty) (hD : D.Nonempty) (hOF : O ⊆ F)
    (hfar : ∀ i ∈ F, ∀ p ∈ D, 1 ≤ dist i p)
    (N : ℕ) (hN : 0 < N) (hcard : O.card ≤ N)
    (alpha : D → ℝ) (Q v : ℝ) (hdual : Dual (fun j : D => j.val) F v (2/(N:ℝ)^2) alpha)
    (hSQ : cost D S ≤ Q) (hv : 0 < v) (hv1 : v ≤ 1/12)
    (hvc : v ≤ strictnessGap (200*countConstant (1/100))/1000)
    (hsmall : v^2 ≤ strictnessGap (200*countConstant (1/100))/(6*(200*countConstant (1/100)+2)))
    (hsize : 2/(N:ℝ) ≤ strictnessGap (200*countConstant (1/100))/200)
    (hpay : (1-3*v)*Q ≤ ∑ j, alpha j) :
    cost D S ≤ (2-strictnessGap (200*countConstant (1/100))/100)*cost D O := by
  let C := countConstant (1/100)
  let c := strictnessGap (200*C)
  let lam := 2/(N:ℝ)^2
  let P := cost D O
  have hC : 10 ≤ C := countConstant_ge_ten
  have hT : 0 < 200*C := by linarith
  have hc : 0 < c := strictnessGap_pos hT
  have hc1 : c ≤ 1 := strictnessGap_le_one hT
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hN
  have hNR1 : 1 ≤ (N:ℝ) := by exact_mod_cast hN
  have hlam : 0 < lam := by dsimp [lam]; positivity
  have hlam2 : lam ≤ 2 := by
    dsimp [lam]
    apply (div_le_iff₀ (sq_pos_of_pos hNR)).mpr
    nlinarith only [hNR1]
  have hP1 : 1 ≤ P := comparison_ge_one F D O hD hO hOF hfar
  have hstrict (i : V) (hi : i ∈ O) :
      (∑ p ∈ cluster D (nearest O hO) i, extendBudget D alpha p) ≤
        lam+(2-c/2)*clusterCost D (nearest O hO) i := by
    by_cases hne : (cluster D (nearest O hO) i).Nonempty
    · have hp := cluster_ge_one D (cluster D (nearest O hO) i) F (Finset.filter_subset _ _) hne hfar i (hOF hi)
      change 1 ≤ clusterCost D (nearest O hO) i at hp
      have hprice : lam ≤ 200*C*clusterCost D (nearest O hO) i := by
        nlinarith only [hp,hC,hlam2]
      exact strict_on_points D _ F (Finset.filter_subset _ _) hne hdual i (hOF hi) hT
        (show 0 < clusterCost D (nearest O hO) i by linarith only [hp]) hprice hsmall
    · have hz := Finset.not_nonempty_iff_eq_empty.mp hne
      simp only [clusterCost,hz,Finset.sum_empty,mul_zero,add_zero]
      exact hlam.le
  have hrow (i : V) (hi : i ∈ O) :
      (∑ p ∈ cluster D (nearest O hO) i, extendBudget D alpha p) ≤
        lam+2*clusterCost D (nearest O hO) i := by
    have hg := hstrict i hi
    have hpos := mul_nonneg hc.le (clusterCost_nonneg D (nearest O hO) i)
    nlinarith only [hg,hpos]
  have hg := aggregate_gain D O O hO (Finset.Subset.refl _) (extendBudget D alpha) lam c hrow hstrict
  rw [total_cluster_cost,sum_extended_budget] at hg
  have hnlam : (N:ℝ)*lam = 2/(N:ℝ) := by dsimp [lam]; field_simp
  have hpayprice : (O.card:ℝ)*lam ≤ (c/200)*P := by
    have hcast : (O.card:ℝ) ≤ N := by exact_mod_cast hcard
    have hh := mul_le_mul_of_nonneg_right hcast hlam.le
    rw [hnlam] at hh
    have hp := mul_le_mul_of_nonneg_left hP1 (by positivity : 0 ≤ c/200)
    exact hh.trans (hsize.trans (by simpa only [mul_one] using hp))
  have hA : (∑ j, alpha j) ≤ (2-c/2+c/200)*P := by
    dsimp [P] at *
    linarith only [hg,hpayprice]
  exact hSQ.trans (small_price_strict Q P c v _ (by linarith only [hP1]) hc hv hv1 hvc hpay hA)

end MetricKMedianRecovery.PhaseSurplusProducer

end OAI
