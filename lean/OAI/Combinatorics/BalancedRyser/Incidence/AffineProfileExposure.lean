import OAI.Combinatorics.BalancedRyser.Incidence.AffineProfileIncidence
import OAI.Combinatorics.BalancedRyser.Incidence.AffineTargetError
import OAI.Combinatorics.BalancedRyser.Probability.UniformSubsetExposure
import OAI.Combinatorics.BalancedRyser.Profiles.Profile
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileEmpirical
import OAI.Combinatorics.BalancedRyser.Profiles.ProfileTargetExclusion

namespace OAI

namespace Balanced.AffineProfileExposure

universe u

noncomputable section
open scoped Classical
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] in

theorem multiplicity_erase_on_target (D : Finset (Line F)) (l : Line F)
    (hl : l ∈ D) (p : Point F) (hp : OnLine p l) :
    lineMultiplicity (D.erase l) p = lineMultiplicity D p - 1 := by
  unfold lineMultiplicity
  rw [Finset.filter_erase, Finset.card_erase_of_mem (Finset.mem_filter.mpr ⟨hl, hp⟩)]

def targetExposureMean (D C : Finset (Line F)) (l : Line F) (d c : ℕ) : ℝ :=
  (∑ S ∈ ((D.erase l).powersetCard (d - 1)) ×ˢ (C.powersetCard c),
    (((linePoints l).filter (fun p =>
      (∀ m ∈ D.erase l \ S.1, ¬ OnLine p m) ∧
      (∀ m ∈ C \ S.2, ¬ OnLine p m))).card : ℝ) /
        ((((D.erase l).powersetCard (d - 1)) ×ˢ (C.powersetCard c)).card : ℝ)) /
    (Fintype.card F : ℝ)

def targetPowerMean (D C : Finset (Line F)) (l : Line F) (d c : ℕ) : ℝ :=
  (∑ p ∈ linePoints l,
    ((d : ℝ) / D.card) ^ (lineMultiplicity D p - 1) *
      ((c : ℝ) / C.card) ^ lineMultiplicity C p) / (Fintype.card F : ℝ)

theorem targetExposureMean_eq (D C : Finset (Line F)) (l : Line F) (d c : ℕ)
    (hl : l ∈ D) (hd : d ≤ D.card) (hc : c ≤ C.card) :
    targetExposureMean D C l d c =
      (∑ p ∈ linePoints l,
        (((d - 1).descFactorial (lineMultiplicity D p - 1) : ℝ) /
          ((D.card - 1).descFactorial (lineMultiplicity D p - 1) : ℝ)) *
        ((c.descFactorial (lineMultiplicity C p) : ℝ) /
          (C.card.descFactorial (lineMultiplicity C p) : ℝ))) / (Fintype.card F : ℝ) := by
  have hd' : d - 1 ≤ (D.erase l).card := by
    rw [Finset.card_erase_of_mem hl]
    exact Nat.sub_le_sub_right hd 1
  unfold targetExposureMean
  congr 1
  convert (Balanced.uniform_two_subsets_expected_uncovered_card (D.erase l) C
    (linePoints l) (fun p m => OnLine p m) (d - 1) c hd' hc).trans ?_ using 1
  · apply Finset.sum_congr rfl
    intro S _
    congr 1
    congr 2
    ext p
    simp only [Finset.mem_filter]
  · apply Finset.sum_congr rfl
    intro p hp
    have hp' : OnLine p l := (Finset.mem_filter.mp hp).2
    have hm := multiplicity_erase_on_target D l hl p hp'
    have hE := Finset.card_erase_of_mem hl
    calc
      _ = (((d - 1).descFactorial (lineMultiplicity (D.erase l) p) : ℝ) /
          ((D.erase l).card.descFactorial (lineMultiplicity (D.erase l) p) : ℝ)) *
          ((c.descFactorial (lineMultiplicity C p) : ℝ) /
            (C.card.descFactorial (lineMultiplicity C p) : ℝ)) := by
        unfold lineMultiplicity
        congr 6
      _ = _ := by rw [hm, hE]

theorem target_weights_sum (l : Line F) :
    ∑ _p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) = 1 := by
  have hq : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [AffineTargetError.target_card, hq]

theorem uniform_target_exposure_approximation (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (l : Line F) (d c : ℕ),
      N₀ ≤ D.card → N₀ ≤ C.card → l ∈ D → d ≤ D.card → c ≤ C.card →
      (∑ p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) *
        (((lineMultiplicity D p - 1 + lineMultiplicity C p : ℕ) : ℝ))) ≤ M →
      |targetExposureMean D C l d c - targetPowerMean D C l d c| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    ProfileTargetExclusion.uniform_target_hypergeometric_approximation M hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D C l d c hD hC hl hd hc hmean
  have h := happrox (linePoints l) (fun _ => 1 / (Fintype.card F : ℝ))
    (fun p => lineMultiplicity D p - 1) (fun p => lineMultiplicity C p)
    d D.card c C.card hD hC hd hc (by intros; positivity) (target_weights_sum l) hmean
  rw [targetExposureMean_eq D C l d c hl hd hc]
  unfold targetPowerMean
  simpa only [one_div_mul_eq_div, ← Finset.sum_div] using h

theorem uniform_target_exposure_approximation_empty_witness
    (M : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (l : Line F) (d : ℕ),
      N₀ ≤ D.card → l ∈ D → d ≤ D.card →
      (∑ p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) *
        ((lineMultiplicity D p - 1 : ℕ) : ℝ)) ≤ M →
      |targetExposureMean D ∅ l d 0 - targetPowerMean D ∅ l d 0| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    ProfileTargetExclusion.uniform_target_hypergeometric_approximation_one_population M hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D l d hD hl hd hmean
  have h := happrox (linePoints l) (fun _ => 1 / (Fintype.card F : ℝ))
    (fun p => lineMultiplicity D p - 1) d D.card hD hd
    (by intros; positivity) (target_weights_sum l) hmean
  rw [targetExposureMean_eq D ∅ l d 0 hl hd (by simp)]
  unfold targetPowerMean
  have hm (p : Point F) : lineMultiplicity (∅ : Finset (Line F)) p = 0 := by
    simp only [lineMultiplicity, Finset.filter_empty, Finset.card_empty]
  simp only [hm, Nat.descFactorial_zero, Nat.cast_one, div_self one_ne_zero, pow_zero, mul_one]
  simpa only [one_div_mul_eq_div, ← Finset.sum_div] using h

theorem shifted_target_mean_le {k : ℕ} {D C : Finset (Line F)} {l : Line F}
    (hpair : IsProfilePair k D C) (hl : l ∈ D) :
    (∑ p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) *
      (((lineMultiplicity D p - 1 + lineMultiplicity C p : ℕ) : ℝ))) ≤ 2 * k + 4 := by
  obtain ⟨hD, hDC, hC⟩ := hpair
  calc
    _ ≤ ∑ p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) *
        (((lineMultiplicity D p + lineMultiplicity C p : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast Nat.add_le_add_right (Nat.sub_le _ _) _
    _ = (∑ p ∈ linePoints l,
        (((lineMultiplicity D p + lineMultiplicity C p : ℕ) : ℝ))) /
        (Fintype.card F : ℝ) := by
      simp only [one_div_mul_eq_div, Finset.sum_div]
    _ ≤ 2 * k + 4 := by
      simpa only [lineMultiplicity, deletionMultiplicity] using
        FiniteProfile.line_firstMoment_le_source_bound hD hC hDC
          (Finset.mem_union_left C hl)

theorem uniform_profile_pair_target_approximation (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (l : Line F) (d c : ℕ),
      N₀ ≤ D.card → N₀ ≤ C.card → IsProfilePair k D C →
      l ∈ D → d ≤ D.card → c ≤ C.card →
      |targetExposureMean D C l d c - targetPowerMean D C l d c| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ := uniform_target_exposure_approximation (2 * k + 4) hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D C l d c hD hC hpair hl hd hc
  exact happrox F D C l d c hD hC hl hd hc (shifted_target_mean_le hpair hl)

theorem uniform_deletion_target_approximation (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D : Finset (Line F)) (l : Line F) (d : ℕ),
      N₀ ≤ D.card → IsDeletionSet k D → l ∈ D → d ≤ D.card →
      |targetExposureMean D ∅ l d 0 - targetPowerMean D ∅ l d 0| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ :=
    uniform_target_exposure_approximation_empty_witness (2 * k + 4) hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D l d hD hDel hl hd
  apply happrox F D l d hD hl hd
  have hpair : IsProfilePair k D (∅ : Finset (Line F)) := ⟨hDel, by simp, by simp⟩
  simpa only [lineMultiplicity, Finset.filter_empty, Finset.card_empty, Nat.add_zero] using
    shifted_target_mean_le hpair hl

theorem targetPowerMean_eq_profile_transform
    (D C : Finset (Line F)) (l : Line F) (d c : ℕ) :
    targetPowerMean D C l d c =
      ∑' ij : ℕ × ℕ, lineProfile D C l ij *
        (((d : ℝ) / D.card) ^ (ij.1 - 1) * ((c : ℝ) / C.card) ^ ij.2) := by
  have h := lineProfile_weighted_hasSum D C l (fun ij =>
    ((d : ℝ) / D.card) ^ (ij.1 - 1) * ((c : ℝ) / C.card) ^ ij.2)
  exact h.tsum_eq.symm.trans (tsum_congr (fun ij => mul_comm _ _))

theorem shifted_cover_target_mean_le {k : ℕ} {D C : Finset (Line F)} {l : Line F}
    (hpair : IsProfilePair k D C) (hl : l ∈ C) :
    (∑ p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) *
      (((lineMultiplicity C p - 1 + lineMultiplicity D p : ℕ) : ℝ))) ≤ 2 * k + 4 := by
  obtain ⟨hD, hDC, hC⟩ := hpair
  calc
    _ ≤ ∑ p ∈ linePoints l, (1 / (Fintype.card F : ℝ)) *
        (((lineMultiplicity D p + lineMultiplicity C p : ℕ) : ℝ)) := by
      apply Finset.sum_le_sum
      intro p _
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact_mod_cast (show lineMultiplicity C p - 1 + lineMultiplicity D p ≤
        lineMultiplicity D p + lineMultiplicity C p by omega)
    _ = (∑ p ∈ linePoints l,
        (((lineMultiplicity D p + lineMultiplicity C p : ℕ) : ℝ))) /
        (Fintype.card F : ℝ) := by
      simp only [one_div_mul_eq_div, Finset.sum_div]
    _ ≤ 2 * k + 4 := by
      simpa only [lineMultiplicity, deletionMultiplicity] using
        FiniteProfile.line_firstMoment_le_source_bound hD hC hDC
          (Finset.mem_union_right D hl)

theorem uniform_profile_pair_cover_target_approximation (k : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F]
      (D C : Finset (Line F)) (l : Line F) (d c : ℕ),
      N₀ ≤ D.card → N₀ ≤ C.card → IsProfilePair k D C →
      l ∈ C → d ≤ D.card → c ≤ C.card →
      |targetExposureMean C D l c d - targetPowerMean C D l c d| < ε := by
  obtain ⟨N₀, hN₀, happrox⟩ := uniform_target_exposure_approximation (2 * k + 4) hε
  refine ⟨N₀, hN₀, ?_⟩
  intro F hField hFin hDec D C l d c hD hC hpair hl hd hc
  exact happrox F C D l c d hC hD hl hc hd (shifted_cover_target_mean_le hpair hl)

end
end Balanced.AffineProfileExposure

end OAI
