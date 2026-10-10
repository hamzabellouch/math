import OAI.Combinatorics.BalancedRyser.Incidence.AffinePermutationExposure

namespace OAI

namespace Balanced.AffinePlaneOrderExposure

universe u
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
open AffinePermutationExposure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def planeOrderMean (D C : Finset (Line F))
    (I : Finset D) (J : Finset C) (i l : D) : ℝ :=
  (𝔼 σ ∈ Finset.univ.filter (fun σ : Equiv.Perm D => σ i = l),
    𝔼 τ : Equiv.Perm C,
      (((Finset.univ : Finset (Point F)).filter (fun p =>
        (∀ m ∈ (Finset.univ.erase l) \ I.map σ.toEmbedding, ¬ OnLine p m.1) ∧
        (∀ m ∈ Finset.univ \ J.map τ.toEmbedding, ¬ OnLine p m.1))).card : ℝ)) /
    (Fintype.card F : ℝ) ^ 2

def planePowerMean (D C : Finset (Line F)) (d c : ℕ) : ℝ :=
  (∑ p : Point F, ((d : ℝ) / D.card) ^ lineMultiplicity D p *
    ((c : ℝ) / C.card) ^ lineMultiplicity C p) / (Fintype.card F : ℝ) ^ 2

def erasedPlanePowerMean (D C : Finset (Line F)) (l : Line F) (d c : ℕ) : ℝ :=
  (∑ p : Point F, ((d : ℝ) / D.card) ^ lineMultiplicity (D.erase l) p *
    ((c : ℝ) / C.card) ^ lineMultiplicity C p) / (Fintype.card F : ℝ) ^ 2

omit [Fintype F] in

theorem erased_subtype_card (D : Finset (Line F)) (l : D) (p : Point F) :
    (((Finset.univ : Finset D).erase l).filter (fun m => OnLine p m.1)).card =
      lineMultiplicity (D.erase l.1) p := by
  unfold lineMultiplicity
  apply Finset.card_bij (fun m _ => m.1)
  · intro m hm
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hm
    refine Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨?_, m.2⟩, hp⟩
    intro heq
    exact (Finset.mem_erase.mp hm).1 (Subtype.ext heq)
  · intro m _ n _ hmn
    exact Subtype.ext hmn
  · intro m hm
    obtain ⟨hm, hp⟩ := Finset.mem_filter.mp hm
    refine ⟨⟨m, (Finset.mem_erase.mp hm).2⟩, ?_, rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩, hp⟩
    intro heq
    exact (Finset.mem_erase.mp hm).1 (congrArg Subtype.val heq)

theorem planeOrderMean_eq (D C : Finset (Line F)) (I : Finset D) (J : Finset C)
    (i l : D) (hi : i ∉ I) :
    planeOrderMean D C I J i l =
      (∑ p : Point F,
        ((I.card.descFactorial (lineMultiplicity (D.erase l.1) p) : ℝ) /
          ((D.card - 1).descFactorial (lineMultiplicity (D.erase l.1) p) : ℝ)) *
        ((J.card.descFactorial (lineMultiplicity C p) : ℝ) /
          (C.card.descFactorial (lineMultiplicity C p) : ℝ))) /
            (Fintype.card F : ℝ) ^ 2 := by
  unfold planeOrderMean
  convert (congrArg (fun z : ℝ => z / (Fintype.card F : ℝ) ^ 2)
    (permutation_target_uncovered_mean I J i l hi Finset.univ
      (fun p m => OnLine p m.1) (fun p m => OnLine p m.1))).trans ?_ using 1
  · apply congrArg (fun z : ℝ => z / (Fintype.card F : ℝ) ^ 2)
    apply Finset.expect_congr rfl
    intro σ hσ
    apply Finset.expect_congr rfl
    intro τ hτ
    apply congrArg (fun S : Finset (Point F) => (S.card : ℝ))
    ext p
    simp only [Finset.mem_filter]
  · apply congrArg (fun z : ℝ => z / (Fintype.card F : ℝ) ^ 2)
    apply Finset.sum_congr rfl
    intro p hp
    simp only [Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ,
      Fintype.card_coe]
    congr 4
    · convert erased_subtype_card D l p using 1
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]
    · convert erased_subtype_card D l p using 1
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]
    · convert subtype_filter_card C (fun m => OnLine p m) using 1
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]
    · convert subtype_filter_card C (fun m => OnLine p m) using 1
      apply congrArg Finset.card
      ext m
      simp only [Finset.mem_filter]

omit [DecidableEq F] in

theorem plane_weights_sum :
    ∑ _p : Point F, (1 / (Fintype.card F : ℝ) ^ 2) = 1 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, Point, Fintype.card_prod,
    Nat.cast_mul, nsmul_eq_mul, pow_two]
  field_simp

omit [Fintype F] in

theorem multiplicity_erase_le (D : Finset (Line F)) (l : Line F) (p : Point F) :
    lineMultiplicity (D.erase l) p ≤ lineMultiplicity D p := by
  unfold lineMultiplicity
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))

omit [Fintype F] in

theorem multiplicity_erase_eq_off (D : Finset (Line F)) (l : Line F)
    (p : Point F) (hp : ¬ OnLine p l) :
    lineMultiplicity (D.erase l) p = lineMultiplicity D p := by
  unfold lineMultiplicity
  rw [Finset.filter_erase, Finset.erase_eq_of_notMem]
  simp only [Finset.mem_filter, not_and]
  exact fun _ => hp

theorem erasedPlanePowerMean_error (D C : Finset (Line F)) (l : Line F) (d c : ℕ)
    (hd : d ≤ D.card) (hc : c ≤ C.card) :
    |erasedPlanePowerMean D C l d c - planePowerMean D C d c| ≤
      1 / (Fintype.card F : ℝ) := by
  have hx := ProfileTargetExclusion.fraction_bounds d D.card hd
  have hy := ProfileTargetExclusion.fraction_bounds c C.card hc
  have hb (a b : ℕ) :
      0 ≤ ((d : ℝ) / D.card) ^ a * ((c : ℝ) / C.card) ^ b ∧
      ((d : ℝ) / D.card) ^ a * ((c : ℝ) / C.card) ^ b ≤ 1 := by
    refine ⟨mul_nonneg (pow_nonneg hx.1 _) (pow_nonneg hy.1 _), ?_⟩
    calc
      _ ≤ 1 * ((c : ℝ) / C.card) ^ b :=
        mul_le_mul_of_nonneg_right (pow_le_one₀ hx.1 hx.2) (pow_nonneg hy.1 _)
      _ = ((c : ℝ) / C.card) ^ b := one_mul _
      _ ≤ 1 := pow_le_one₀ hy.1 hy.2
  apply AffineTargetError.plane_average_error l _ _
    (fun p => hb _ _) (fun p => hb _ _)
  intro p hp
  rw [multiplicity_erase_eq_off D l p hp]

theorem planePowerMean_eq_profile_transform (D C : Finset (Line F)) (d c : ℕ) :
    planePowerMean D C d c =
      ∑' ij : ℕ × ℕ, planeProfile D C ij *
        (((d : ℝ) / D.card) ^ ij.1 * ((c : ℝ) / C.card) ^ ij.2) := by
  have h := planeProfile_weighted_hasSum D C (fun ij =>
    ((d : ℝ) / D.card) ^ ij.1 * ((c : ℝ) / C.card) ^ ij.2)
  exact h.tsum_eq.symm.trans (tsum_congr (fun ij => mul_comm _ _))

theorem plane_mean_le {k : ℕ} {D C : Finset (Line F)} (hpair : IsProfilePair k D C) :
    (∑ p : Point F, (1 / (Fintype.card F : ℝ) ^ 2) *
      (((lineMultiplicity D p + lineMultiplicity C p : ℕ) : ℝ))) ≤ 2 * (k : ℝ) + 4 := by
  have hb := (planeProfile_isBounded k D C hpair.1 hpair.2.2).2.2.2
  rw [(planeProfile_weighted_hasSum D C
    (fun ij => ((ij.1 + ij.2 : ℕ) : ℝ))).tsum_eq] at hb
  simpa only [one_div_mul_eq_div, ← Finset.sum_div] using hb

theorem erased_plane_mean_le {k : ℕ} {D C : Finset (Line F)}
    (hpair : IsProfilePair k D C) (l : Line F) :
    (∑ p : Point F, (1 / (Fintype.card F : ℝ) ^ 2) *
      (((lineMultiplicity (D.erase l) p + lineMultiplicity C p : ℕ) : ℝ))) ≤
        2 * (k : ℝ) + 4 := by
  apply le_trans _ (plane_mean_le hpair)
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast Nat.add_le_add_right (multiplicity_erase_le D l p) _

theorem uniform_plane_order_approximation (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset D) (J : Finset C) (i l : D),
      N₀ ≤ D.card → N₀ ≤ C.card → i ∉ I →
      (∑ p : Point F, (1 / (Fintype.card F : ℝ) ^ 2) *
        (((lineMultiplicity (D.erase l.1) p + lineMultiplicity C p : ℕ) : ℝ))) ≤ M →
      |planeOrderMean D C I J i l - planePowerMean D C (I.card + 1) J.card| <
        ε + 1 / (Fintype.card F : ℝ) := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    ProfileTargetExclusion.uniform_target_hypergeometric_approximation M hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D C I J i l hD hC hi hmean
  have hd := remaining_count_le D I i hi
  have hc : J.card ≤ C.card := by
    simpa only [Finset.card_univ, Fintype.card_coe] using
      Finset.card_le_card (Finset.subset_univ J)
  have h := happrox Finset.univ (fun _ : Point F => 1 / (Fintype.card F : ℝ) ^ 2)
    (fun p => lineMultiplicity (D.erase l.1) p) (fun p => lineMultiplicity C p)
    (I.card + 1) D.card J.card C.card hD hC hd hc
    (by intros; positivity) plane_weights_sum hmean
  have hfirst : |planeOrderMean D C I J i l -
      erasedPlanePowerMean D C l.1 (I.card + 1) J.card| < ε := by
    rw [planeOrderMean_eq D C I J i l hi]
    simpa only [Nat.add_sub_cancel, one_div_mul_eq_div, ← Finset.sum_div,
      erasedPlanePowerMean] using h
  exact (abs_sub_le _ _ _).trans_lt
    (add_lt_add_of_lt_of_le hfirst (erasedPlanePowerMean_error D C l.1
      (I.card + 1) J.card hd hc))

theorem uniform_plane_order_approximation_empty_witness
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (I : Finset D) (i l : D),
      N₀ ≤ D.card → i ∉ I →
      (∑ p : Point F, (1 / (Fintype.card F : ℝ) ^ 2) *
        ((lineMultiplicity (D.erase l.1) p : ℕ) : ℝ)) ≤ M →
      |planeOrderMean D ∅ I ∅ i l - planePowerMean D ∅ (I.card + 1) 0| <
        ε + 1 / (Fintype.card F : ℝ) := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    ProfileTargetExclusion.uniform_target_hypergeometric_approximation_one_population M hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D I i l hD hi hmean
  have hd := remaining_count_le D I i hi
  have h := happrox Finset.univ (fun _ : Point F => 1 / (Fintype.card F : ℝ) ^ 2)
    (fun p => lineMultiplicity (D.erase l.1) p) (I.card + 1) D.card hD hd
    (by intros; positivity) plane_weights_sum hmean
  have hm (p : Point F) : lineMultiplicity (∅ : Finset (Line F)) p = 0 := by
    simp only [lineMultiplicity, Finset.filter_empty, Finset.card_empty]
  have hfirst : |planeOrderMean D ∅ I ∅ i l -
      erasedPlanePowerMean D ∅ l.1 (I.card + 1) 0| < ε := by
    rw [planeOrderMean_eq D ∅ I ∅ i l hi]
    simpa only [Nat.add_sub_cancel, one_div_mul_eq_div, ← Finset.sum_div,
      erasedPlanePowerMean, hm, Nat.descFactorial_zero, Nat.cast_one,
      div_self one_ne_zero, pow_zero, mul_one] using h
  exact (abs_sub_le _ _ _).trans_lt
    (add_lt_add_of_lt_of_le hfirst (erasedPlanePowerMean_error D ∅ l.1
      (I.card + 1) 0 hd (by simp)))

theorem planePowerMean_swap (D C : Finset (Line F)) (d c : ℕ) :
    planePowerMean C D c d = planePowerMean D C d c := by
  unfold planePowerMean
  apply congrArg (fun z : ℝ => z / (Fintype.card F : ℝ) ^ 2)
  apply Finset.sum_congr rfl
  intro p hp
  exact mul_comm _ _

theorem erased_cover_plane_mean_le {k : ℕ} {D C : Finset (Line F)}
    (hpair : IsProfilePair k D C) (l : Line F) :
    (∑ p : Point F, (1 / (Fintype.card F : ℝ) ^ 2) *
      (((lineMultiplicity (C.erase l) p + lineMultiplicity D p : ℕ) : ℝ))) ≤
        2 * (k : ℝ) + 4 := by
  apply le_trans _ (plane_mean_le hpair)
  apply Finset.sum_le_sum
  intro p hp
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact_mod_cast (show lineMultiplicity (C.erase l) p + lineMultiplicity D p ≤
    lineMultiplicity D p + lineMultiplicity C p by
      have h := multiplicity_erase_le C l p
      omega)

theorem exists_reciprocal_cutoff {ε : ℝ} (hε : 0 < ε) :
    ∃ Q₀ : ℕ, ∀ q : ℕ, Q₀ ≤ q → 1 / (q : ℝ) < ε := by
  have hlim : Filter.Tendsto (fun n : ℕ => 1 / (n : ℝ)) Filter.atTop (nhds 0) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).const_div_atTop 1
  exact Filter.eventually_atTop.mp (hlim.eventually_lt_const hε)

theorem uniform_profile_pair_order_plane_approximation (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset D) (J : Finset C) (i l : D),
      N₀ ≤ Fintype.card F → N₀ ≤ D.card → N₀ ≤ C.card →
      IsProfilePair k D C → i ∉ I →
      |planeOrderMean D C I J i l -
        ∑' ij : ℕ × ℕ, planeProfile D C ij *
          ((((I.card + 1 : ℕ) : ℝ) / D.card) ^ ij.1 *
            ((J.card : ℝ) / C.card) ^ ij.2)| < ε := by
  obtain ⟨N, hN, happrox⟩ :=
    uniform_plane_order_approximation (2 * (k : ℝ) + 4) (half_pos hε)
  obtain ⟨Q, hQ⟩ := exists_reciprocal_cutoff (half_pos hε)
  refine ⟨max N Q, by omega, ?_⟩
  intro F hField hFin hDec D C I J i l hq hD hC hpair hi
  rw [← planePowerMean_eq_profile_transform]
  have h := happrox F D C I J i l (by omega) (by omega) hi
    (erased_plane_mean_le hpair l.1)
  have hsmall := hQ (Fintype.card F) (by omega)
  linarith

theorem uniform_profile_pair_order_cover_plane_approximation (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (I : Finset C) (J : Finset D) (i l : C),
      N₀ ≤ Fintype.card F → N₀ ≤ D.card → N₀ ≤ C.card →
      IsProfilePair k D C → i ∉ I →
      |planeOrderMean C D I J i l -
        ∑' ij : ℕ × ℕ, planeProfile D C ij *
          (((J.card : ℝ) / D.card) ^ ij.1 *
            (((I.card + 1 : ℕ) : ℝ) / C.card) ^ ij.2)| < ε := by
  obtain ⟨N, hN, happrox⟩ :=
    uniform_plane_order_approximation (2 * (k : ℝ) + 4) (half_pos hε)
  obtain ⟨Q, hQ⟩ := exists_reciprocal_cutoff (half_pos hε)
  refine ⟨max N Q, by omega, ?_⟩
  intro F hField hFin hDec D C I J i l hq hD hC hpair hi
  rw [← planePowerMean_eq_profile_transform, ← planePowerMean_swap D C]
  have h := happrox F C D I J i l (by omega) (by omega) hi
    (erased_cover_plane_mean_le hpair l.1)
  have hsmall := hQ (Fintype.card F) (by omega)
  linarith

theorem uniform_deletion_order_plane_approximation (k : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (I : Finset D) (i l : D),
      N₀ ≤ Fintype.card F → N₀ ≤ D.card → IsDeletionSet k D → i ∉ I →
      |planeOrderMean D ∅ I ∅ i l - planePowerMean D ∅ (I.card + 1) 0| < ε := by
  obtain ⟨N, hN, happrox⟩ :=
    uniform_plane_order_approximation_empty_witness (2 * (k : ℝ) + 4) (half_pos hε)
  obtain ⟨Q, hQ⟩ := exists_reciprocal_cutoff (half_pos hε)
  refine ⟨max N Q, by omega, ?_⟩
  intro F hField hFin hDec D I i l hq hD hDel hi
  have hpair : IsProfilePair k D (∅ : Finset (Line F)) := ⟨hDel, by simp, by simp⟩
  have hmean := erased_plane_mean_le hpair l.1
  have h := happrox F D I i l (by omega) hi (by
    simpa only [lineMultiplicity, Finset.filter_empty, Finset.card_empty,
      Nat.add_zero] using hmean)
  have hsmall := hQ (Fintype.card F) (by omega)
  linarith

end
end Balanced.AffinePlaneOrderExposure

end OAI
