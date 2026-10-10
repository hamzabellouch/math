import OAI.Combinatorics.BalancedRyser.Incidence.AffineProfileParameter
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileOrderComplements
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileScheduledMarks

namespace OAI

noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators

namespace Balanced.ProfileScheduledApproximation

universe u
open ConditionalOrderVariance UncoveredSampling ProfileMarkedOrders
  ProfileOrderComplements ProfileScheduledMarks ExposureInterleaving
  AffinePlaneOrderExposure AffineProfileParameter ProfileDetectionBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem planeFraction_eq_filter (U V : Finset (Line F))
    (S : Finset U) (T : Finset V) :
    planeFraction (populationLines U S) (populationLines V T) =
      (((Finset.univ : Finset (Point F)).filter (fun p =>
        (∀ m ∈ S, ¬ OnLine p m.1) ∧ (∀ m ∈ T, ¬ OnLine p m.1))).card : ℝ) /
        (Fintype.card F : ℝ)^2 := by
  unfold planeFraction
  apply congrArg (fun A : Finset (Point F) => (A.card : ℝ) / (Fintype.card F : ℝ)^2)
  ext p
  simp only [uncoveredBy, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.forall_mem_union, populationLines, Finset.forall_mem_map]
  rfl

theorem conditional_planeMean_eq_remaining (U V : Finset (Line F))
    (I : Finset U) (J : Finset V) (i x : U) (hi : i ∉ I) :
    conditionalMean U V i x (planeStatistic U V I J) =
      planeOrderMean U V (future I i) (Finset.univ \ J) i x := by
  unfold conditionalMean planeOrderMean
  rw [Finset.expect_product, Finset.expect_div]
  apply Finset.expect_congr rfl
  intro σ hσ
  rw [Finset.expect_div]
  apply Finset.expect_congr rfl
  intro τ _
  have hx : σ i = x := (Finset.mem_filter.mp hσ).2
  rw [exposed_image_eq I i x hi σ hx, exposed_image_eq_complement J τ]
  unfold planeStatistic
  rw [planeFraction_eq_filter]
  apply congrArg (fun A : Finset (Point F) => (A.card : ℝ) / (Fintype.card F : ℝ)^2)
  ext p
  simp only [Finset.mem_filter]

omit [Field F] [Fintype F] in
theorem remaining_D_counts (D C : Finset (Line F)) (i : D) :
    (future (ID D C i) i).card + 1 = (unexposedD D C (stepD D C i)).card ∧
    (Finset.univ \ JD D C i).card = (unexposedC D C (stepD D C i)).card := by
  constructor
  · rw [future_card_add_one _ _ (current_not_ID D C i), Fintype.card_coe]
    have h := prefixD_add_unexposedD D C (stepD D C i)
    dsimp only [ID]
    omega
  · exact congrArg Finset.card (prefixC_complement D C (stepD D C i))

omit [Field F] [Fintype F] in
theorem remaining_C_counts (D C : Finset (Line F)) (i : C) :
    (Finset.univ \ JC D C i).card = (unexposedD D C (stepC D C i)).card ∧
    (future (IC D C i) i).card + 1 = (unexposedC D C (stepC D C i)).card := by
  constructor
  · exact congrArg Finset.card (prefixD_complement D C (stepC D C i))
  · rw [future_card_add_one _ _ (current_not_IC D C i), Fintype.card_coe]
    have h := prefixC_add_unexposedC D C (stepC D C i)
    dsimp only [IC]
    omega

theorem uniform_scheduled_D_means (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (i x : D),
      N ≤ Fintype.card F → N ≤ D.card → N ≤ C.card → IsProfilePair k D C →
      |conditionalMean D C i x (targetStatistic D C (ID D C i) (JD D C i) x) -
        dTest (lineProfile D C x.1) (zD D i)| < ε ∧
      |conditionalMean D C i x (planeStatistic D C (ID D C i) (JD D C i)) -
        planeTest (planeProfile D C) (zD D i)| < ε := by
  obtain ⟨N₀, hN₀, δ, hδ, happ⟩ := uniform_order_d_tests_approximation k hε
  obtain ⟨N₁, hN₁⟩ := exists_reciprocal_cutoff hδ
  refine ⟨max N₀ N₁, by omega, ?_⟩
  intro F hField hFin hDec D C i x hq hD hC hp
  have hDpos : 0 < D.card := by omega
  have hCpos : 0 < C.card := by omega
  have hm := unexposed_fraction_bounds D C hDpos hCpos (stepD D C i)
  have hc := remaining_D_counts D C i
  have hdlt := hN₁ D.card (by omega)
  have hclt := hN₁ C.card (by omega)
  rw [conditional_targetMean_eq_remaining D C _ _ i x (current_not_ID D C i),
    conditional_planeMean_eq_remaining D C _ _ i x (current_not_ID D C i)]
  apply happ F D C _ _ i x (zD D i) (by omega) (by omega) (by omega) hp
    (current_not_future _ _) (grid_pos (label D i)) (grid_le_one (label D i))
  · rw [hc.1]
    exact hm.1.trans hdlt.le
  · rw [hc.2]
    exact hm.2.trans hclt.le

theorem uniform_scheduled_C_means (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (i x : C),
      N ≤ Fintype.card F → N ≤ D.card → N ≤ C.card → IsProfilePair k D C →
      |conditionalMean C D i x (targetStatistic C D (IC D C i) (JC D C i) x) -
        cTest (lineProfile D C x.1) (zC C i)| < ε ∧
      |conditionalMean C D i x (planeStatistic C D (IC D C i) (JC D C i)) -
        planeTest (planeProfile D C) (zC C i)| < ε := by
  obtain ⟨N₀, hN₀, δ, hδ, happ⟩ := uniform_order_c_tests_approximation k hε
  obtain ⟨N₁, hN₁⟩ := exists_reciprocal_cutoff hδ
  refine ⟨max N₀ N₁, by omega, ?_⟩
  intro F hField hFin hDec D C i x hq hD hC hp
  have hDpos : 0 < D.card := by omega
  have hCpos : 0 < C.card := by omega
  have hm := unexposed_fraction_bounds D C hDpos hCpos (stepC D C i)
  have hc := remaining_C_counts D C i
  have hdlt := hN₁ D.card (by omega)
  have hclt := hN₁ C.card (by omega)
  rw [conditional_targetMean_eq_remaining C D _ _ i x (current_not_IC D C i),
    conditional_planeMean_eq_remaining C D _ _ i x (current_not_IC D C i)]
  apply happ F D C _ _ i x (zC C i) (by omega) (by omega) (by omega) hp
    (current_not_future _ _) (coverGrid_pos _ (label C i))
    (coverGrid_le_one (Real.sqrt_pos.2 (by norm_num)) (label C i))
  · rw [hc.1]
    exact hm.1.trans hdlt.le
  · rw [hc.2]
    exact hm.2.trans hclt.le

omit [Field F] [Fintype F] in

theorem future_ID_fraction_exact (D C : Finset (Line F)) (i : D) :
    (((future (ID D C i) i).card + 1 : ℕ) : ℝ) / D.card = zD D i := by
  rw [(remaining_D_counts D C i).1]
  simp only [unexposedD, Finset.card_map, stepD, remainingD_at_D,
    zD, grid, Nat.cast_add, Nat.cast_one]

theorem uniform_scheduled_empty_means (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (i x : D),
      N ≤ Fintype.card F → N ≤ D.card → IsDeletionSet k D →
      |conditionalMean D ∅ i x (targetStatistic D ∅ (ID D ∅ i) (JD D ∅ i) x) -
        dTest (lineProfile D ∅ x.1) (zD D i)| < ε ∧
      |conditionalMean D ∅ i x (planeStatistic D ∅ (ID D ∅ i) (JD D ∅ i)) -
        planeTest (planeProfile D ∅) (zD D i)| < ε := by
  obtain ⟨N, hN, δ, hδ, happ⟩ := uniform_order_empty_tests_approximation k hε
  refine ⟨N, hN, ?_⟩
  intro F hField hFin hDec D i x hq hD hp
  rw [conditional_targetMean_eq_remaining D ∅ _ _ i x (current_not_ID D ∅ i),
    conditional_planeMean_eq_remaining D ∅ _ _ i x (current_not_ID D ∅ i)]
  have hJ : (Finset.univ \ JD D (∅ : Finset (Line F)) i) = ∅ := by
    exact Finset.eq_empty_of_forall_notMem (fun j => (Finset.notMem_empty j.1 j.2).elim)
  rw [hJ]
  apply happ F D _ i x (zD D i) hq hD hp (current_not_future _ _)
    (grid_pos (label D i)) (grid_le_one (label D i))
  rw [future_ID_fraction_exact, sub_self, abs_zero]
  exact hδ.le

end Balanced.ProfileScheduledApproximation

end

end OAI
