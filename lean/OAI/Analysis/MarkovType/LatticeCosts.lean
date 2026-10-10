import OAI.Analysis.MarkovType.LatticePaths
import OAI.Analysis.MarkovType.MarkovTransport

namespace OAI

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MarkovSuperreflexivity

variable {S E : Type*} [Fintype S] [Fintype E]

theorem marked_stateCost_one {V : Type*} [NormedAddCommGroup V]
    (C : FiniteMarkedChain S E) (f : S → V) (p : ℝ) :
    stateCost C.toStateChain f p 1 =
      stationaryEdgeCost C (fun e => f (C.tgt e) - f (C.src e)) p := by
  classical
  rw [stateCost_one]
  change (∑ s, ∑ t, (C.π s * markedTransition C s t) *
      Real.rpow (‖f t - f s‖) p) = _
  simp only [markedTransition, Finset.mul_sum, Finset.sum_mul]
  calc
    (∑ s, ∑ t, ∑ e,
        C.π s * (if C.src e = s ∧ C.tgt e = t then C.q e else 0) *
          Real.rpow (‖f t - f s‖) p) =
        ∑ s, ∑ e, ∑ t,
          C.π s * (if C.src e = s ∧ C.tgt e = t then C.q e else 0) *
            Real.rpow (‖f t - f s‖) p := by
      apply Finset.sum_congr rfl
      intro s _
      exact Finset.sum_comm
    _ = ∑ e, ∑ s, ∑ t,
          C.π s * (if C.src e = s ∧ C.tgt e = t then C.q e else 0) *
            Real.rpow (‖f t - f s‖) p := Finset.sum_comm
    _ = stationaryEdgeCost C (fun e => f (C.tgt e) - f (C.src e)) p := by
      unfold stationaryEdgeCost
      apply Finset.sum_congr rfl
      intro e _
      have heq (s t : S) :
          C.π s * (if C.src e = s ∧ C.tgt e = t then C.q e else 0) *
              Real.rpow (‖f t - f s‖) p =
          if s = C.src e then
            (if t = C.tgt e then
              C.π (C.src e) * C.q e * Real.rpow (‖f (C.tgt e) - f (C.src e)‖) p
              else 0) else 0 := by
        by_cases hs : s = C.src e
        · subst s
          by_cases ht : t = C.tgt e
          · subst t
            simp
          · simp [ht, Ne.symm ht]
        · simp [hs, Ne.symm hs]
      simp_rw [heq]
      simp

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem lattice_oneStepCost_le (C : FiniteMarkedChain S E)
    {g : E → V} (hg : OddLabel C g) {p : ℝ} (hp : 0 < p) (R : ℕ) :
    stateCost (latticeLift C R).toStateChain (liftPotential C g R) p 1 ≤
      stationaryEdgeCost C g p := by
  classical
  rw [marked_stateCost_one]
  have hc : (Fintype.card (LiftCube C R) : ℝ) ≠ 0 :=
    ne_of_gt (latticeCube_card_real_pos R)
  calc
    stationaryEdgeCost (latticeLift C R)
        (fun e => liftPotential C g R ((latticeLift C R).tgt e) -
          liftPotential C g R ((latticeLift C R).src e)) p ≤
        ∑ x : E × LiftCube C R,
          (C.π (C.src x.1) * C.q x.1 * Real.rpow (‖g x.1‖) p) /
            (Fintype.card (LiftCube C R) : ℝ) := by
      apply Finset.sum_le_sum
      rintro ⟨e, a⟩ _
      have hcost :
          Real.rpow (‖liftPotential C g R (liftTarget C R (e, a)) -
            liftPotential C g R (liftSource C R (e, a))‖) p ≤
            Real.rpow (‖g e‖) p := by
        rw [liftPotential_increment C hg]
        by_cases h : liftAccept C R e a
        · simp [h]
        · simpa [h, Real.zero_rpow (ne_of_gt hp)] using
            Real.rpow_nonneg (norm_nonneg (g e)) p
      change (C.π (C.src e) / (Fintype.card (LiftCube C R) : ℝ) * C.q e) *
          Real.rpow (‖liftPotential C g R (liftTarget C R (e, a)) -
            liftPotential C g R (liftSource C R (e, a))‖) p ≤ _
      calc
        _ ≤ (C.π (C.src e) / (Fintype.card (LiftCube C R) : ℝ) * C.q e) *
            Real.rpow (‖g e‖) p :=
          mul_le_mul_of_nonneg_left hcost
            (mul_nonneg (div_nonneg (C.π_nonneg _) (Nat.cast_nonneg _)) (C.q_nonneg e))
        _ = _ := by ring
    _ = stationaryEdgeCost C g p := by
      rw [Fintype.sum_prod_type]
      unfold stationaryEdgeCost
      apply Finset.sum_congr rfl
      intro e _
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp [hc]

theorem MarkovTypeWith.odd_edge_bound {p K : ℝ} (hV : MarkovTypeWith p K V)
    (C : FiniteMarkedChain S E) (g : E → V) (hg : OddLabel C g)
    (n : ℕ) (hn : 1 ≤ n) :
    markedSumCost C g p n ≤
      Real.rpow K p * (n : ℝ) * stationaryEdgeCost C g p := by
  have hkn : 0 ≤ Real.rpow K p * (n : ℝ) :=
    mul_nonneg (Real.rpow_nonneg hV.2.1.le p) (Nat.cast_nonneg n)
  have hR (R : ℕ) (hnR : n ≤ R) :
      latticeDensity (OrbitRep C) n R * markedSumCost C g p n ≤
        Real.rpow K p * (n : ℝ) * stationaryEdgeCost C g p := by
    calc
      _ ≤ stateCost (latticeLift C R).toStateChain (liftPotential C g R) p n :=
        lattice_central_cost_le C hg p hnR
      _ ≤ Real.rpow K p * (n : ℝ) *
          stateCost (latticeLift C R).toStateChain (liftPotential C g R) p 1 :=
        hV.bound _ _ n hn
      _ ≤ _ := mul_le_mul_of_nonneg_left (lattice_oneStepCost_le C hg hV.1 R) hkn
  have hlim : Tendsto
      (fun m : ℕ => latticeDensity (OrbitRep C) n (m + n + 1) * markedSumCost C g p n)
      atTop (𝓝 (markedSumCost C g p n)) := by
    simpa only [one_mul] using
      (latticeDensity_tendsto_one (J := OrbitRep C) n).mul tendsto_const_nhds
  exact le_of_tendsto hlim (Eventually.of_forall fun m => hR (m + n + 1) (by omega))

end MarkovSuperreflexivity

end

end OAI
