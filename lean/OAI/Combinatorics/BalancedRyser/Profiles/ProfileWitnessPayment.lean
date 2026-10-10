import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic
import OAI.Combinatorics.BalancedRyser.Deletion.ExponentialDomination
import OAI.Combinatorics.BalancedRyser.Probability.WitnessCounting
import OAI.Combinatorics.BalancedRyser.Profiles.Profile
import OAI.Combinatorics.BalancedRyser.Profiles.WitnessDetection

namespace OAI

namespace Balanced.ProfileWitnessPayment

universe u

noncomputable section
open scoped BigOperators Classical

theorem projection_mass_le {D W : Type*} [Fintype D] [DecidableEq W]
    (s : Finset W) (A : D → W → Prop) (w : D → W → ℝ)
    (α : ℝ) (hw : ∀ d c, 0 ≤ w d c)
    (hmarked : ∀ d c, c ∈ s → A d c → α ≤ w d c) :
    α * ((Finset.univ.filter (fun d => ∃ c ∈ s, A d c)).card : ℝ) ≤
      ∑ d, ∑ c ∈ s, w d c := by
  have h := WitnessDetection.detection_sum_ge_witness_card
    (fun (d : D) (c : s) => A d c.val) (fun d c => w d c.val) α
    (fun d c => hw d c.val) (fun d c hc => hmarked d c.val c.property hc)
  simpa only [Subtype.exists, Finset.mem_coe, exists_prop, Finset.sum_coe_sort] using h

theorem projection_probability_le {D W : Type*} [Fintype D] [DecidableEq W]
    (s : Finset W) (hs : 0 < s.card) (A : D → W → Prop) (w : D → W → ℝ)
    (α R : ℝ) (hα : 0 < α) (hw : ∀ d c, 0 ≤ w d c)
    (hmarked : ∀ d c, c ∈ s → A d c → α ≤ w d c)
    (hrare : ((∑ d, ∑ c ∈ s, w d c) / (Fintype.card D : ℝ)) /
      (s.card : ℝ) ≤ R) :
    ((Finset.univ.filter (fun d => ∃ c ∈ s, A d c)).card : ℝ) /
        (Fintype.card D : ℝ) ≤ (s.card : ℝ) * R / α := by
  have hsR : (0 : ℝ) < s.card := by exact_mod_cast hs
  have hsum := div_le_div_of_nonneg_right
    (projection_mass_le s A w α hw hmarked)
    (show (0 : ℝ) ≤ Fintype.card D by positivity)
  have hra := (div_le_iff₀ hsR).mp hrare
  apply (le_div_iff₀ hα).mpr
  calc
    _ = α * ((Finset.univ.filter (fun d => ∃ c ∈ s, A d c)).card : ℝ) /
        (Fintype.card D : ℝ) := by ring
    _ ≤ (∑ d, ∑ c ∈ s, w d c) / (Fintype.card D : ℝ) := hsum
    _ ≤ (s.card : ℝ) * R := by simpa [mul_comm] using hra

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

def witnesses (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m : ℕ) :
    Finset (Finset (Line F)) := (Finset.univ : Finset (Line F)).powersetCard m

@[simp] theorem mem_witnesses (m : ℕ) (C : Finset (Line F)) :
    C ∈ witnesses F m ↔ C.card = m := by
  simp [witnesses]

@[simp] theorem card_witnesses (m : ℕ) :
    (witnesses F m).card =
      (Fintype.card F * (Fintype.card F + 1)).choose m := by
  simp [witnesses, Line, Direction, Nat.mul_comm]

theorem card_witnesses_pos {m : ℕ} (hm : m ≤ Fintype.card F) :
    0 < (witnesses F m).card := by
  rw [card_witnesses]
  apply Nat.choose_pos
  exact hm.trans (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))

def pairMarkAverage (k m : ℕ)
    (w : DeletionSet F k → Finset (Line F) → ℝ) : ℝ :=
  ((∑ D, ∑ C ∈ witnesses F m, w D C) /
    (Fintype.card (DeletionSet F k) : ℝ)) / (witnesses F m).card

theorem fixed_size_payment (k m : ℕ) (hm : m ≤ Fintype.card F)
    (A : Finset (Line F) → Finset (Line F) → Prop)
    (w : DeletionSet F k → Finset (Line F) → ℝ)
    (α R : ℝ) (hα : 0 < α) (hw : ∀ D C, 0 ≤ w D C)
    (hmarked : ∀ D C, C.card = m → A D.val C → α ≤ w D C)
    (hrare : pairMarkAverage k m w ≤ R) :
    ((Finset.univ.filter (fun D : DeletionSet F k =>
      ∃ C : Finset (Line F), C.card = m ∧ A D.val C)).card : ℝ) /
        Fintype.card (DeletionSet F k) ≤
      ((Fintype.card F * (Fintype.card F + 1)).choose m : ℝ) * R / α := by
  simpa only [mem_witnesses, card_witnesses] using
    projection_probability_le (witnesses F m) (card_witnesses_pos hm)
      (fun D C => A D.val C) w α R hα hw
      (fun D C hC hA => hmarked D C ((mem_witnesses m C).mp hC) hA) hrare

theorem witness_probability_le_sum_fixed_sizes (k : ℕ) (A : ProfileClass)
    (hvalid : ProfileClassValid k A) :
    uniformProfileWitnessProbability k A F ≤
      ∑ m ∈ Finset.range (Fintype.card F + 1),
        ((Finset.univ.filter (fun D : DeletionSet F k =>
          ∃ C : Finset (Line F), C.card = m ∧ A F D.val C)).card : ℝ) /
            Fintype.card (DeletionSet F k) := by
  let E (m : ℕ) : Finset (DeletionSet F k) := Finset.univ.filter (fun D =>
    ∃ C : Finset (Line F), C.card = m ∧ A F D.val C)
  have hsub : (Finset.univ.filter (fun D : DeletionSet F k =>
      ∃ C : Finset (Line F), A F D.val C)) ⊆
      (Finset.range (Fintype.card F + 1)).biUnion E := by
    intro D hD
    obtain ⟨C, hC⟩ := (Finset.mem_filter.mp hD).2
    have hm := (hvalid F D.val C hC).2.2
    apply Finset.mem_biUnion.mpr
    refine ⟨C.card, Finset.mem_range.mpr (by omega), ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, C, rfl, hC⟩
  have hc := (Finset.card_le_card hsub).trans
    Finset.card_biUnion_le
  have hcR : ((Finset.univ.filter (fun D : DeletionSet F k =>
      ∃ C : Finset (Line F), A F D.val C)).card : ℝ) ≤
      ∑ m ∈ Finset.range (Fintype.card F + 1), ((E m).card : ℝ) := by
    exact_mod_cast hc
  unfold uniformProfileWitnessProbability
  rw [← Finset.sum_div]
  exact div_le_div_of_nonneg_right hcR (by positivity)

theorem all_sizes_payment (k : ℕ) (A : ProfileClass)
    (hvalid : ProfileClassValid k A)
    (w : ℕ → DeletionSet F k → Finset (Line F) → ℝ)
    (α : ℝ) (R : ℕ → ℝ) (hα : 0 < α)
    (hw : ∀ m D C, 0 ≤ w m D C)
    (hmarked : ∀ m D C, C.card = m → A F D.val C → α ≤ w m D C)
    (hrare : ∀ m, m ≤ Fintype.card F → pairMarkAverage k m (w m) ≤ R m) :
    uniformProfileWitnessProbability k A F ≤
      ∑ m ∈ Finset.range (Fintype.card F + 1),
        ((Fintype.card F * (Fintype.card F + 1)).choose m : ℝ) * R m / α := by
  apply (witness_probability_le_sum_fixed_sizes k A hvalid).trans
  apply Finset.sum_le_sum
  intro m hm
  exact fixed_size_payment k m (by simpa using hm) (A F) (w m) α (R m) hα
    (hw m) (hmarked m) (hrare m (by simpa using hm))

theorem cancellation_payment (k : ℕ) (A : ProfileClass)
    (hvalid : ProfileClassValid k A)
    (w : ℕ → DeletionSet F k → Finset (Line F) → ℝ)
    (α T : ℝ) (hα : 0 < α) (hT : 0 ≤ T)
    (hw : ∀ m D C, 0 ≤ w m D C)
    (hmarked : ∀ m D C, C.card = m → A F D.val C → α ≤ w m D C)
    (hrare : ∀ m, m ≤ Fintype.card F →
      pairMarkAverage k m (w m) ≤ T / (Fintype.card F : ℝ) ^ m) :
    uniformProfileWitnessProbability k A F ≤
      T * Real.exp (2 * (Fintype.card F : ℝ)) / α := by
  have h := all_sizes_payment k A hvalid w α
    (fun m => T / (Fintype.card F : ℝ) ^ m) hα hw hmarked hrare
  rw [← Finset.sum_div] at h
  apply h.trans
  apply div_le_div_of_nonneg_right _ hα.le
  exact affine_witness_union_bound (Fintype.card F) Fintype.card_pos
    (fun m => T / (Fintype.card F : ℝ) ^ m) hT (fun _ _ => le_rfl)

theorem eventually_superexponential_payment (α L ξ : ℝ)
    (hξ : 0 < ξ) :
    ∀ᶠ q : ℕ in Filter.atTop,
      Real.exp (L * q - ξ * q * Real.log q) * Real.exp (2 * q) / α ≤
        Real.exp (-(ξ / 2) * q * Real.log q) := by
  have ht := (BalancedRyser.tendsto_exp_linear_mul_exp_neg_mul_log
    (L + 2) (show 0 < ξ / 2 by positivity)).div_const α
  have hsmall : ∀ᶠ q : ℕ in Filter.atTop,
      (Real.exp ((L + 2) * q) * Real.exp (-(ξ / 2) * q * Real.log q)) / α ≤ 1 := by
    have h := ht.eventually_lt_const (show (0 : ℝ) / α < 1 by simp)
    exact h.mono (fun q hq => hq.le)
  filter_upwards [hsmall] with q hq
  calc
    _ = ((Real.exp ((L + 2) * q) *
        Real.exp (-(ξ / 2) * q * Real.log q)) / α) *
          Real.exp (-(ξ / 2) * q * Real.log q) := by
      rw [div_mul_eq_mul_div, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      congr 2
      ring
    _ ≤ 1 * Real.exp (-(ξ / 2) * q * Real.log q) :=
      mul_le_mul_of_nonneg_right hq (Real.exp_nonneg _)
    _ = _ := one_mul _

theorem counting_of_mark_bounds (k : ℕ) (A : ProfileClass.{u})
    (hvalid : ProfileClassValid k A) (α L ξ : ℝ) (hα : 0 < α) (hξ : 0 < ξ)
    (hmarks : ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F → k ≤ Fintype.card F →
        ∃ w : ℕ → DeletionSet F k → Finset (Line F) → ℝ,
          (∀ m D C, 0 ≤ w m D C) ∧
          (∀ m D C, C.card = m → A F D.val C → α ≤ w m D C) ∧
          (∀ m, m ≤ Fintype.card F → pairMarkAverage k m (w m) ≤
            Real.exp (L * Fintype.card F - ξ * Fintype.card F *
              Real.log (Fintype.card F)) / (Fintype.card F : ℝ) ^ m)) :
    ∃ b : ℝ, 0 < b ∧ ∃ N : ℕ,
      ∀ (F : Type u) [Field F] [Fintype F] [DecidableEq F],
        N ≤ Fintype.card F → k ≤ Fintype.card F →
        uniformProfileWitnessProbability k A F ≤
          Real.exp (-b * Fintype.card F * Real.log (Fintype.card F)) := by
  obtain ⟨N₀, hN₀⟩ := hmarks
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    (eventually_superexponential_payment α L ξ hξ)
  refine ⟨ξ / 2, by positivity, max N₀ N₁, ?_⟩
  intro F _ _ _ hN hk
  obtain ⟨w, hw, hmarked, hrare⟩ :=
    hN₀ F ((le_max_left N₀ N₁).trans hN) hk
  exact (cancellation_payment k A hvalid w α _ hα (Real.exp_nonneg _)
    hw hmarked hrare).trans (hN₁ _ ((le_max_right N₀ N₁).trans hN))

end
end Balanced.ProfileWitnessPayment

end OAI
