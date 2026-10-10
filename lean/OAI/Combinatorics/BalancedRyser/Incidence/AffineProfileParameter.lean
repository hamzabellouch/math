import OAI.Combinatorics.BalancedRyser.Incidence.AffinePlaneOrderExposure
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileDetectionBridge

namespace OAI

namespace Balanced.AffineProfileParameter

universe u

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open AffinePlaneOrderExposure AffineProfileExposure ProfileDetectionBridge

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem monomial_eq_real_power {z : ℝ} (hz : 0 < z) (a b : ℕ) :
    z ^ a * (z ^ Real.sqrt 2) ^ b =
      z ^ ((a : ℝ) + Real.sqrt 2 * b) := by
  rw [Real.rpow_add hz, Real.rpow_natCast, Real.rpow_mul hz.le,
    Real.rpow_natCast]

omit [Fintype F] in

theorem target_multiplicity_pos (D : Finset (Line F)) (l : Line F)
    (hl : l ∈ D) (p : Point F) (hp : OnLine p l) :
    1 ≤ lineMultiplicity D p := by
  exact Finset.card_pos.mpr ⟨l, Finset.mem_filter.mpr ⟨hl, hp⟩⟩

theorem planeTest_eq_average (D C : Finset (Line F)) {z : ℝ} (hz : 0 < z) :
    planeTest (planeProfile D C) z =
      (∑ p : Point F, z ^ lineMultiplicity D p *
        (z ^ Real.sqrt 2) ^ lineMultiplicity C p) / (Fintype.card F : ℝ) ^ 2 := by
  have h := planeProfile_weighted_hasSum D C (fun ij =>
    z ^ ((ij.1 : ℝ) + Real.sqrt 2 * ij.2))
  calc
    _ = (∑ p : Point F,
        z ^ ((lineMultiplicity D p : ℝ) + Real.sqrt 2 * lineMultiplicity C p)) /
          (Fintype.card F : ℝ) ^ 2 := by
      exact (tsum_congr (fun ij => mul_comm _ _)).trans h.tsum_eq
    _ = _ := by
      apply congrArg (fun r : ℝ => r / (Fintype.card F : ℝ) ^ 2)
      apply Finset.sum_congr rfl
      intro p hp
      exact (monomial_eq_real_power hz _ _).symm

theorem dTest_eq_average (D C : Finset (Line F)) (l : Line F)
    (hl : l ∈ D) {z : ℝ} (hz : 0 < z) :
    dTest (lineProfile D C l) z =
      (∑ p ∈ linePoints l, z ^ (lineMultiplicity D p - 1) *
        (z ^ Real.sqrt 2) ^ lineMultiplicity C p) / (Fintype.card F : ℝ) := by
  have h := lineProfile_weighted_hasSum D C l (fun ij =>
    z ^ ((ij.1 : ℝ) - 1 + Real.sqrt 2 * ij.2))
  calc
    _ = (∑ p ∈ linePoints l,
        z ^ ((lineMultiplicity D p : ℝ) - 1 + Real.sqrt 2 * lineMultiplicity C p)) /
          (Fintype.card F : ℝ) := by
      exact (tsum_congr (fun ij => mul_comm _ _)).trans h.tsum_eq
    _ = _ := by
      apply congrArg (fun r : ℝ => r / (Fintype.card F : ℝ))
      apply Finset.sum_congr rfl
      intro p hp
      have hm := target_multiplicity_pos D l hl p (Finset.mem_filter.mp hp).2
      rw [monomial_eq_real_power hz, Nat.cast_sub hm, Nat.cast_one]

theorem cTest_eq_average (D C : Finset (Line F)) (l : Line F)
    (hl : l ∈ C) {z : ℝ} (hz : 0 < z) :
    cTest (lineProfile D C l) z =
      (∑ p ∈ linePoints l, z ^ lineMultiplicity D p *
        (z ^ Real.sqrt 2) ^ (lineMultiplicity C p - 1)) / (Fintype.card F : ℝ) := by
  have h := lineProfile_weighted_hasSum D C l (fun ij =>
    z ^ ((ij.1 : ℝ) + Real.sqrt 2 * ((ij.2 : ℝ) - 1)))
  calc
    _ = (∑ p ∈ linePoints l,
        z ^ ((lineMultiplicity D p : ℝ) + Real.sqrt 2 * ((lineMultiplicity C p : ℝ) - 1))) /
          (Fintype.card F : ℝ) := by
      exact (tsum_congr (fun ij => mul_comm _ _)).trans h.tsum_eq
    _ = _ := by
      apply congrArg (fun r : ℝ => r / (Fintype.card F : ℝ))
      apply Finset.sum_congr rfl
      intro p hp
      have hm := target_multiplicity_pos C l hl p (Finset.mem_filter.mp hp).2
      rw [monomial_eq_real_power hz, Nat.cast_sub hm, Nat.cast_one]

theorem planePowerMean_error_to_planeTest {k : ℕ} {D C : Finset (Line F)}
    (hpair : IsProfilePair k D C) (d c : ℕ)
    (hd : d ≤ D.card) (hc : c ≤ C.card) {z δ : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hδ : 0 ≤ δ)
    (hD : |(d : ℝ) / D.card - z| ≤ δ)
    (hC : |(c : ℝ) / C.card - z ^ Real.sqrt 2| ≤ δ) :
    |planePowerMean D C d c - planeTest (planeProfile D C) z| ≤
      (2 * (k : ℝ) + 4) * δ := by
  have hy : 0 ≤ z ^ Real.sqrt 2 ∧ z ^ Real.sqrt 2 ≤ 1 :=
    ⟨Real.rpow_nonneg hz.le _, Real.rpow_le_one hz.le hz1 (Real.sqrt_nonneg 2)⟩
  have h := ProfileTargetExclusion.weighted_parameter_error Finset.univ
    (fun _ : Point F => 1 / (Fintype.card F : ℝ) ^ 2)
    (fun p => lineMultiplicity D p) (fun p => lineMultiplicity C p)
    ((d : ℝ) / D.card) z ((c : ℝ) / C.card) (z ^ Real.sqrt 2)
    δ (2 * (k : ℝ) + 4) (by intros; positivity) (plane_mean_le hpair)
    (ProfileTargetExclusion.fraction_bounds d D.card hd) ⟨hz.le, hz1⟩
    (ProfileTargetExclusion.fraction_bounds c C.card hc) hy hδ hD hC
  rw [planeTest_eq_average D C hz]
  simpa only [planePowerMean, one_div_mul_eq_div, ← Finset.sum_div] using h

theorem targetPowerMean_error_to_dTest {k : ℕ} {D C : Finset (Line F)}
    (hpair : IsProfilePair k D C) (l : Line F) (hl : l ∈ D) (d c : ℕ)
    (hd : d ≤ D.card) (hc : c ≤ C.card) {z δ : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hδ : 0 ≤ δ)
    (hD : |(d : ℝ) / D.card - z| ≤ δ)
    (hC : |(c : ℝ) / C.card - z ^ Real.sqrt 2| ≤ δ) :
    |targetPowerMean D C l d c - dTest (lineProfile D C l) z| ≤
      (2 * (k : ℝ) + 4) * δ := by
  have hy : 0 ≤ z ^ Real.sqrt 2 ∧ z ^ Real.sqrt 2 ≤ 1 :=
    ⟨Real.rpow_nonneg hz.le _, Real.rpow_le_one hz.le hz1 (Real.sqrt_nonneg 2)⟩
  have h := ProfileTargetExclusion.weighted_parameter_error (linePoints l)
    (fun _ : Point F => 1 / (Fintype.card F : ℝ))
    (fun p => lineMultiplicity D p - 1) (fun p => lineMultiplicity C p)
    ((d : ℝ) / D.card) z ((c : ℝ) / C.card) (z ^ Real.sqrt 2)
    δ (2 * (k : ℝ) + 4) (by intros; positivity) (shifted_target_mean_le hpair hl)
    (ProfileTargetExclusion.fraction_bounds d D.card hd) ⟨hz.le, hz1⟩
    (ProfileTargetExclusion.fraction_bounds c C.card hc) hy hδ hD hC
  rw [dTest_eq_average D C l hl hz]
  simpa only [targetPowerMean, one_div_mul_eq_div, ← Finset.sum_div] using h

theorem targetPowerMean_error_to_cTest {k : ℕ} {D C : Finset (Line F)}
    (hpair : IsProfilePair k D C) (l : Line F) (hl : l ∈ C) (d c : ℕ)
    (hd : d ≤ D.card) (hc : c ≤ C.card) {z δ : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hδ : 0 ≤ δ)
    (hD : |(d : ℝ) / D.card - z| ≤ δ)
    (hC : |(c : ℝ) / C.card - z ^ Real.sqrt 2| ≤ δ) :
    |targetPowerMean C D l c d - cTest (lineProfile D C l) z| ≤
      (2 * (k : ℝ) + 4) * δ := by
  have hy : 0 ≤ z ^ Real.sqrt 2 ∧ z ^ Real.sqrt 2 ≤ 1 :=
    ⟨Real.rpow_nonneg hz.le _, Real.rpow_le_one hz.le hz1 (Real.sqrt_nonneg 2)⟩
  have h := ProfileTargetExclusion.weighted_parameter_error (linePoints l)
    (fun _ : Point F => 1 / (Fintype.card F : ℝ))
    (fun p => lineMultiplicity C p - 1) (fun p => lineMultiplicity D p)
    ((c : ℝ) / C.card) (z ^ Real.sqrt 2) ((d : ℝ) / D.card) z
    δ (2 * (k : ℝ) + 4) (by intros; positivity) (shifted_cover_target_mean_le hpair hl)
    (ProfileTargetExclusion.fraction_bounds c C.card hc) hy
    (ProfileTargetExclusion.fraction_bounds d D.card hd) ⟨hz.le, hz1⟩ hδ hC hD
  rw [cTest_eq_average D C l hl hz]
  simp only [one_div_mul_eq_div, ← Finset.sum_div] at h
  simpa only [targetPowerMean, mul_comm] using h

theorem planePowerMean_empty_error_to_planeTest {k : ℕ} {D : Finset (Line F)}
    (hDel : IsDeletionSet k D) (d : ℕ) (hd : d ≤ D.card) {z δ : ℝ}
    (hz : 0 < z) (hz1 : z ≤ 1) (hδ : 0 ≤ δ)
    (hD : |(d : ℝ) / D.card - z| ≤ δ) :
    |planePowerMean D ∅ d 0 - planeTest (planeProfile D ∅) z| ≤
      (2 * (k : ℝ) + 4) * δ := by
  have hpair : IsProfilePair k D (∅ : Finset (Line F)) := ⟨hDel, by simp, by simp⟩
  have hm (p : Point F) : lineMultiplicity (∅ : Finset (Line F)) p = 0 := by
    simp only [lineMultiplicity, Finset.filter_empty, Finset.card_empty]
  have hmean := plane_mean_le hpair
  simp only [hm, Nat.add_zero] at hmean
  have h := ProfileTargetExclusion.weighted_parameter_error Finset.univ
    (fun _ : Point F => 1 / (Fintype.card F : ℝ) ^ 2)
    (fun p => lineMultiplicity D p) (fun _ => 0)
    ((d : ℝ) / D.card) z 0 0 δ (2 * (k : ℝ) + 4)
    (by intros; positivity) (by simpa only [Nat.add_zero] using hmean)
    (ProfileTargetExclusion.fraction_bounds d D.card hd) ⟨hz.le, hz1⟩
    ⟨le_rfl, zero_le_one⟩ ⟨le_rfl, zero_le_one⟩ hδ hD (by simpa using hδ)
  rw [planeTest_eq_average D ∅ hz]
  simpa only [planePowerMean, hm, pow_zero, mul_one,
    one_div_mul_eq_div, ← Finset.sum_div] using h

theorem targetPowerMean_empty_error_to_dTest {k : ℕ} {D : Finset (Line F)}
    (hDel : IsDeletionSet k D) (l : Line F) (hl : l ∈ D) (d : ℕ)
    (hd : d ≤ D.card) {z δ : ℝ} (hz : 0 < z) (hz1 : z ≤ 1) (hδ : 0 ≤ δ)
    (hD : |(d : ℝ) / D.card - z| ≤ δ) :
    |targetPowerMean D ∅ l d 0 - dTest (lineProfile D ∅ l) z| ≤
      (2 * (k : ℝ) + 4) * δ := by
  have hpair : IsProfilePair k D (∅ : Finset (Line F)) := ⟨hDel, by simp, by simp⟩
  have hm (p : Point F) : lineMultiplicity (∅ : Finset (Line F)) p = 0 := by
    simp only [lineMultiplicity, Finset.filter_empty, Finset.card_empty]
  have hmean := shifted_target_mean_le hpair hl
  simp only [hm, Nat.add_zero] at hmean
  have h := ProfileTargetExclusion.weighted_parameter_error (linePoints l)
    (fun _ : Point F => 1 / (Fintype.card F : ℝ))
    (fun p => lineMultiplicity D p - 1) (fun _ => 0)
    ((d : ℝ) / D.card) z 0 0 δ (2 * (k : ℝ) + 4)
    (by intros; positivity) (by simpa only [Nat.add_zero] using hmean)
    (ProfileTargetExclusion.fraction_bounds d D.card hd) ⟨hz.le, hz1⟩
    ⟨le_rfl, zero_le_one⟩ ⟨le_rfl, zero_le_one⟩ hδ hD (by simpa using hδ)
  rw [dTest_eq_average D ∅ l hl hz]
  simpa only [targetPowerMean, hm, pow_zero, mul_one,
    one_div_mul_eq_div, ← Finset.sum_div] using h

theorem uniform_order_d_tests_approximation (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset D) (J : Finset C) (i l : D) (z : ℝ),
      N₀ ≤ Fintype.card F → N₀ ≤ D.card → N₀ ≤ C.card →
      IsProfilePair k D C → i ∉ I → 0 < z → z ≤ 1 →
      |(((I.card + 1 : ℕ) : ℝ) / D.card) - z| ≤ δ →
      |((J.card : ℝ) / C.card) - z ^ Real.sqrt 2| ≤ δ →
      |AffinePermutationExposure.targetOrderMean D C I J i l -
        dTest (lineProfile D C l.1) z| < ε ∧
      |planeOrderMean D C I J i l - planeTest (planeProfile D C) z| < ε := by
  obtain ⟨Nt, hNt, ht⟩ := uniform_profile_pair_target_approximation k (half_pos hε)
  obtain ⟨Np, hNp, hp⟩ := uniform_profile_pair_order_plane_approximation k (half_pos hε)
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt (half_pos hε) (2 * (k : ℝ) + 4)
  refine ⟨max Nt Np, by omega, δ, hδ, ?_⟩
  intro F hField hFin hDec D C I J i l z hq hD hC hpair hi hz hz1 heD heC
  have hd := AffinePermutationExposure.remaining_count_le D I i hi
  have hc : J.card ≤ C.card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using
      Finset.card_le_card (Finset.subset_univ J)
  have ht' : |AffinePermutationExposure.targetOrderMean D C I J i l -
      targetPowerMean D C l.1 (I.card + 1) J.card| < ε / 2 := by
    rw [AffinePermutationExposure.targetOrderMean_eq_targetExposureMean D C I J i l hi]
    exact ht F D C l.1 (I.card + 1) J.card (by omega) (by omega) hpair l.2 hd hc
  have hp' : |planeOrderMean D C I J i l - planePowerMean D C (I.card + 1) J.card| < ε / 2 := by
    simpa only [← planePowerMean_eq_profile_transform] using
      hp F D C I J i l (by omega) (by omega) (by omega) hpair hi
  have hte := targetPowerMean_error_to_dTest hpair l.1 l.2 (I.card + 1) J.card
    hd hc hz hz1 hδ.le heD heC
  have hpe := planePowerMean_error_to_planeTest hpair (I.card + 1) J.card
    hd hc hz hz1 hδ.le heD heC
  constructor
  · have htri := (abs_sub_le _ _ _).trans_lt (add_lt_add ht' (hte.trans_lt hsmall))
    simpa only [add_halves] using htri
  · have htri := (abs_sub_le _ _ _).trans_lt (add_lt_add hp' (hpe.trans_lt hsmall))
    simpa only [add_halves] using htri

theorem uniform_order_c_tests_approximation (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset C) (J : Finset D) (i l : C) (z : ℝ),
      N₀ ≤ Fintype.card F → N₀ ≤ D.card → N₀ ≤ C.card →
      IsProfilePair k D C → i ∉ I → 0 < z → z ≤ 1 →
      |((J.card : ℝ) / D.card) - z| ≤ δ →
      |(((I.card + 1 : ℕ) : ℝ) / C.card) - z ^ Real.sqrt 2| ≤ δ →
      |AffinePermutationExposure.targetOrderMean C D I J i l -
        cTest (lineProfile D C l.1) z| < ε ∧
      |planeOrderMean C D I J i l - planeTest (planeProfile D C) z| < ε := by
  obtain ⟨Nt, hNt, ht⟩ := uniform_profile_pair_cover_target_approximation k (half_pos hε)
  obtain ⟨Np, hNp, hp⟩ := uniform_profile_pair_order_cover_plane_approximation k (half_pos hε)
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt (half_pos hε) (2 * (k : ℝ) + 4)
  refine ⟨max Nt Np, by omega, δ, hδ, ?_⟩
  intro F hField hFin hDec D C I J i l z hq hD hC hpair hi hz hz1 heD heC
  have hc := AffinePermutationExposure.remaining_count_le C I i hi
  have hd : J.card ≤ D.card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using
      Finset.card_le_card (Finset.subset_univ J)
  have ht' : |AffinePermutationExposure.targetOrderMean C D I J i l -
      targetPowerMean C D l.1 (I.card + 1) J.card| < ε / 2 := by
    rw [AffinePermutationExposure.targetOrderMean_eq_targetExposureMean C D I J i l hi]
    exact ht F D C l.1 J.card (I.card + 1) (by omega) (by omega) hpair l.2 hd hc
  have hp' : |planeOrderMean C D I J i l - planePowerMean D C J.card (I.card + 1)| < ε / 2 := by
    simpa only [← planePowerMean_eq_profile_transform] using
      hp F D C I J i l (by omega) (by omega) (by omega) hpair hi
  have hte := targetPowerMean_error_to_cTest hpair l.1 l.2 J.card (I.card + 1)
    hd hc hz hz1 hδ.le heD heC
  have hpe := planePowerMean_error_to_planeTest hpair J.card (I.card + 1)
    hd hc hz hz1 hδ.le heD heC
  constructor
  · have htri := (abs_sub_le _ _ _).trans_lt (add_lt_add ht' (hte.trans_lt hsmall))
    simpa only [add_halves] using htri
  · have htri := (abs_sub_le _ _ _).trans_lt (add_lt_add hp' (hpe.trans_lt hsmall))
    simpa only [add_halves] using htri

theorem uniform_order_empty_tests_approximation (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (I : Finset D) (i l : D) (z : ℝ),
      N₀ ≤ Fintype.card F → N₀ ≤ D.card → IsDeletionSet k D →
      i ∉ I → 0 < z → z ≤ 1 → |(((I.card + 1 : ℕ) : ℝ) / D.card) - z| ≤ δ →
      |AffinePermutationExposure.targetOrderMean D ∅ I ∅ i l -
        dTest (lineProfile D ∅ l.1) z| < ε ∧
      |planeOrderMean D ∅ I ∅ i l - planeTest (planeProfile D ∅) z| < ε := by
  obtain ⟨Nt, hNt, ht⟩ :=
    AffinePermutationExposure.uniform_deletion_order_target_approximation k (half_pos hε)
  obtain ⟨Np, hNp, hp⟩ := uniform_deletion_order_plane_approximation k (half_pos hε)
  obtain ⟨δ, hδ, hsmall⟩ := exists_pos_mul_lt (half_pos hε) (2 * (k : ℝ) + 4)
  refine ⟨max Nt Np, by omega, δ, hδ, ?_⟩
  intro F hField hFin hDec D I i l z hq hD hDel hi hz hz1 heD
  have hd := AffinePermutationExposure.remaining_count_le D I i hi
  have ht' := ht F D I i l (by omega) hDel hi
  have hp' := hp F D I i l (by omega) (by omega) hDel hi
  have hte := targetPowerMean_empty_error_to_dTest hDel l.1 l.2 (I.card + 1)
    hd hz hz1 hδ.le heD
  have hpe := planePowerMean_empty_error_to_planeTest hDel (I.card + 1)
    hd hz hz1 hδ.le heD
  constructor
  · have htri := (abs_sub_le _ _ _).trans_lt (add_lt_add ht' (hte.trans_lt hsmall))
    simpa only [add_halves] using htri
  · have htri := (abs_sub_le _ _ _).trans_lt (add_lt_add hp' (hpe.trans_lt hsmall))
    simpa only [add_halves] using htri

end
end Balanced.AffineProfileParameter

end OAI
