import Mathlib
import OAI.Combinatorics.KMedianRecovery.Strictness.ValidExecutionFinalDual
import OAI.Combinatorics.KMedianRecovery.Strictness.ValidExecutionClusterStrictness

namespace OAI

namespace MetricKMedianRecovery

noncomputable def extendBudget {V : Type*} (D : Finset V) (alpha : D → ℝ) (p : V) : ℝ := by
  classical
  exact if hp : p ∈ D then alpha ⟨p,hp⟩ else 0
lemma extendBudget_at {V : Type*} (D : Finset V) (alpha : D → ℝ) (p : D) :
    extendBudget D alpha p.val = alpha p := by simp only [extendBudget,dite_eq_left p.property]

lemma sum_liftSubset {V : Type*} [DecidableEq V] (D C : Finset V) (hCD : C ⊆ D) (f : V → ℝ) :
    (∑ j ∈ Finset.univ.filter (fun j : D => j.val ∈ C), f j.val) = ∑ p ∈ C, f p := by
  classical
  rw [Finset.sum_filter]
  rw [Finset.sum_coe_sort D (fun p => if p ∈ C then f p else 0)]
  rw [← Finset.sum_filter]
  congr 1
  ext p
  simp only [Finset.mem_filter]
  exact ⟨fun hp => hp.2,fun hp => ⟨hCD hp,hp⟩⟩

theorem execution_dual_on_points {V : Type*} [PseudoMetricSpace V] [DecidableEq V]
    (D : Finset V) {steps : ℕ} (v lam eta : ℝ) (E : ValidExecution D V steps v lam eta)
    (hloc : ∀ j, E.location j = j.val) (hv : 0 < v) (hv1 : v < 1/6) (hlam : 0 < lam)
    (i : V) (hi : i ∈ E.regular) :
    (∑ p ∈ D, max (extendBudget D (E.state steps).budget p-2*dist i p) 0) ≤ lam := by
  have h := valid_execution_final_dual v lam eta E hv hv1 hlam i hi
  have hh : (∑ j, max ((E.state steps).budget j-2*dist i (E.location j)) 0) =
      ∑ p ∈ D, max (extendBudget D (E.state steps).budget p-2*dist i p) 0 := by
    calc
      _ = ∑ j : D, max (extendBudget D (E.state steps).budget j.val-2*dist i j.val) 0 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hloc,extendBudget_at]
      _ = _ := Finset.sum_coe_sort D (fun p => max (extendBudget D (E.state steps).budget p-2*dist i p) 0)
  rwa [hh] at h

theorem execution_strict_on_points {V : Type*} [PseudoMetricSpace V] [DecidableEq V]
    (D C : Finset V) (hCD : C ⊆ D) (hC : C.Nonempty) {steps : ℕ}
    (v lam eta T : ℝ) (E : ValidExecution D V steps v lam eta)
    (hloc : ∀ j, E.location j = j.val) (i : V) (hi : i ∈ E.regular)
    (hv : 0 < v) (hv1 : v < 1/6) (hlam : 0 < lam) (hT : 0 < T)
    (hP : 0 < ∑ p ∈ C, dist p i) (hprice : lam ≤ T*(∑ p ∈ C, dist p i))
    (hsmall : v^2 ≤ strictnessGap T/(6*(T+2))) :
    (∑ p ∈ C, extendBudget D (E.state steps).budget p) ≤
      lam+(2-strictnessGap T/2)*(∑ p ∈ C, dist p i) := by
  classical
  let C' := Finset.univ.filter (fun j : D => j.val ∈ C)
  have hC' : C'.Nonempty := by
    obtain ⟨p,hp⟩ := hC
    exact ⟨⟨p,hCD hp⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩⟩
  have hd : (∑ j ∈ C', dist i (E.location j)) = ∑ p ∈ C, dist p i := by
    calc
      _ = ∑ j ∈ C', dist j.val i := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hloc,dist_comm]
      _ = _ := sum_liftSubset D C hCD (fun p => dist p i)
  have hb : (∑ j ∈ C', (E.state steps).budget j) =
      ∑ p ∈ C, extendBudget D (E.state steps).budget p := by
    calc
      _ = ∑ j ∈ C', extendBudget D (E.state steps).budget j.val := by
        apply Finset.sum_congr rfl
        intro j _
        exact (extendBudget_at _ _ j).symm
      _ = _ := sum_liftSubset D C hCD _
  have h := valid_execution_cluster_strictness v lam eta T E C' hC' i hi hv hv1 hlam hT
    (hd ▸ hP) (hd ▸ hprice) hsmall
  rwa [hd,hb] at h

end MetricKMedianRecovery

end OAI
