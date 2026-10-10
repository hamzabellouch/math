import Mathlib

namespace OAI

universe u_1 u_2 u_3

noncomputable section

namespace Problem336AdditiveD139

variable (Γ : Type u_1) [Group Γ] [Countable Γ]

def groupEnumeration : ℕ → Γ :=
  Classical.choose (exists_surjective_nat Γ)

theorem groupEnumeration_surjective : Function.Surjective (groupEnumeration Γ) :=
  Classical.choose_spec (exists_surjective_nat Γ)

def groupBaseExhaustion (n : ℕ) : Finset Γ := by
  classical
  exact insert 1 ((Finset.range n).image (groupEnumeration Γ))

@[simp] theorem one_mem_groupBaseExhaustion (n : ℕ) :
    (1 : Γ) ∈ groupBaseExhaustion Γ n := by
  classical
  simp [groupBaseExhaustion]

theorem groupBaseExhaustion_monotone : Monotone (groupBaseExhaustion Γ) := by
  classical
  intro n m hnm
  exact Finset.insert_subset_insert 1 (Finset.image_subset_image (Finset.range_mono hnm))

theorem mem_groupBaseExhaustion_eventually (g : Γ) :
    ∃ N : ℕ, ∀ n, N ≤ n → g ∈ groupBaseExhaustion Γ n := by
  classical
  obtain ⟨k, hk⟩ := groupEnumeration_surjective Γ g
  refine ⟨k + 1, fun n hn => ?_⟩
  apply Finset.mem_insert_of_mem
  exact Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), hk⟩

def translatedGroupExhaustion (h : Γ) (n : ℕ) : Finset Γ := by
  classical
  exact (groupBaseExhaustion Γ n).image (fun k => h * k)

@[simp] theorem self_mem_translatedGroupExhaustion (h : Γ) (n : ℕ) :
    h ∈ translatedGroupExhaustion Γ h n := by
  classical
  exact Finset.mem_image.mpr ⟨1, one_mem_groupBaseExhaustion Γ n, mul_one h⟩

theorem translatedGroupExhaustion_monotone (h : Γ) :
    Monotone (translatedGroupExhaustion Γ h) := by
  classical
  intro n m hnm
  exact Finset.image_subset_image (groupBaseExhaustion_monotone Γ hnm)

theorem mem_translatedGroupExhaustion_eventually (h g : Γ) :
    ∃ N : ℕ, ∀ n, N ≤ n → g ∈ translatedGroupExhaustion Γ h n := by
  classical
  obtain ⟨N, hN⟩ := mem_groupBaseExhaustion_eventually Γ (h⁻¹ * g)
  refine ⟨N, fun n hn => ?_⟩
  exact Finset.mem_image.mpr ⟨h⁻¹ * g, hN n hn, by simp⟩

theorem subset_translatedGroupExhaustion_eventually (h : Γ) (A : Finset Γ) :
    ∃ N : ℕ, ∀ n, N ≤ n → A ⊆ translatedGroupExhaustion Γ h n := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      exact ⟨0, fun _ _ => Finset.empty_subset _⟩
  | @insert g A hg ih =>
      obtain ⟨N, hN⟩ := mem_translatedGroupExhaustion_eventually Γ h g
      obtain ⟨M, hM⟩ := ih
      refine ⟨max N M, fun n hn => ?_⟩
      exact Finset.insert_subset_iff.mpr
        ⟨hN n (le_trans (le_max_left _ _) hn),
         hM n (le_trans (le_max_right _ _) hn)⟩

theorem translatedGroupExhaustion_equivariant [DecidableEq Γ] (g h : Γ) (n : ℕ) :
    translatedGroupExhaustion Γ (g * h) n =
      (translatedGroupExhaustion Γ h n).image (fun k => g * k) := by
  classical
  ext k
  simp only [translatedGroupExhaustion, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨h * a, ⟨a, ha, rfl⟩, (mul_assoc g h a).symm⟩
  · rintro ⟨b, ⟨a, ha, rfl⟩, rfl⟩
    exact ⟨a, ha, mul_assoc g h a⟩

theorem iUnion_translatedGroupExhaustion (h : Γ) :
    (⋃ n : ℕ, (translatedGroupExhaustion Γ h n : Set Γ)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro g
  obtain ⟨N, hN⟩ := mem_translatedGroupExhaustion_eventually Γ h g
  exact Set.mem_iUnion.mpr ⟨N, hN N le_rfl⟩

def groupExhaustionLimsup {Y : Type u_2} (b : Γ → Finset Γ → Y → ℝ)
    (h : Γ) (y : Y) : ℝ :=
  Filter.limsup (fun n : ℕ => b h (translatedGroupExhaustion Γ h n) y) Filter.atTop

theorem groupExhaustionLimsup_equivariant {Y : Type u_3} [DecidableEq Γ]
    (τ : Γ → Y → Y) (b : Γ → Finset Γ → Y → ℝ)
    (hb : ∀ (g h : Γ) (S : Finset Γ) (y : Y),
      b (g * h) (S.image (fun k => g * k)) (τ g y) = b h S y)
    (g h : Γ) (y : Y) :
    groupExhaustionLimsup Γ b (g * h) (τ g y) =
      groupExhaustionLimsup Γ b h y := by
  apply Filter.limsup_congr
  exact Filter.Eventually.of_forall fun n => by
    rw [translatedGroupExhaustion_equivariant]
    exact hb g h _ y

end Problem336AdditiveD139

end

end OAI
