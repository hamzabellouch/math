import Mathlib
import OAI.Combinatorics.KMedianRecovery.Recovery.RemovalReplay

namespace OAI

namespace MetricKMedianRecovery

theorem valid_execution_cluster_strictness
    {D X : Type*} [Fintype D] [PseudoMetricSpace X] [DecidableEq X]
    {steps : ℕ} (v lam eta T : ℝ) (E : ValidExecution D X steps v lam eta)
    (C : Finset D) (hC : C.Nonempty) (i : X) (hi : i ∈ E.regular)
    (hv : 0 < v) (hv1 : v < 1/6) (hlam : 0 < lam) (hT : 0 < T)
    (hP : 0 < ∑ j ∈ C, dist i (E.location j))
    (hprice : lam ≤ T*(∑ j ∈ C, dist i (E.location j)))
    (hsmall : v^2 ≤ strictnessGap T/(6*(T+2))) :
    (∑ j ∈ C, (E.state steps).budget j) ≤
      lam+(2-strictnessGap T/2)*(∑ j ∈ C, dist i (E.location j)) := by
  classical
  let e : Fin (Fintype.card C) ≃ C := (Fintype.equivFin C).symm
  let incl : C ↪ D := Function.Embedding.subtype _
  let cluster := e.toEmbedding.trans incl
  have hd : (∑ j, dist i (E.location (cluster j))) = ∑ j ∈ C, dist i (E.location j) := by
    calc
      _ = ∑ j : C, dist i (E.location j.val) := Equiv.sum_comp e _
      _ = _ := Finset.sum_coe_sort C (fun j => dist i (E.location j))
  have hb : (∑ j, (E.state steps).budget (cluster j)) = ∑ j ∈ C, (E.state steps).budget j := by
    calc
      _ = ∑ j : C, (E.state steps).budget j.val := Equiv.sum_comp e _
      _ = _ := Finset.sum_coe_sort C ((E.state steps).budget)
  have hq : 0 < Fintype.card C := by simpa only [Fintype.card_coe] using Finset.card_pos.mpr hC
  have h := valid_execution_bounded_price_strictness v lam eta T E cluster i hq hi
    hv hv1 hlam hT (hd ▸ hP) (hd ▸ hprice) hsmall
  simpa only [hb,hd,strictnessGap] using h

end MetricKMedianRecovery

end OAI
