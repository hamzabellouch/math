import OAI.MeasureTheory.Falconer.Recursion.PrefixPolicyGeometry
import Mathlib.Data.Set.Function

namespace OAI

namespace PlanarFalconer

theorem branch_charges_injective {n : ℕ} (start charge : ℕ → ℕ)
    (C : Finset ℕ) (hC : C ⊆ Finset.range n)
    (hstart : MonotoneOn start (Set.Icc 0 n))
    (hcharge : ∀ j ∈ C, start j < charge j ∧ charge j ≤ start (j+1)) :
    Set.InjOn charge C := by
  intro i hi j hj he
  have hiN := Finset.mem_range.mp (hC hi)
  have hjN := Finset.mem_range.mp (hC hj)
  have hci := hcharge i hi
  have hcj := hcharge j hj
  rcases lt_trichotomy i j with hij | hij | hji
  · have hm := hstart (show i+1 ∈ Set.Icc 0 n by constructor <;> omega)
      (show j ∈ Set.Icc 0 n by constructor <;> omega) (by omega : i+1 ≤ j)
    omega
  · exact hij
  · have hm := hstart (show j+1 ∈ Set.Icc 0 n by constructor <;> omega)
      (show i ∈ Set.Icc 0 n by constructor <;> omega) (by omega : j+1 ≤ i)
    omega

theorem branch_representative_charges_bound (A : ℕ → ℝ) (N q n : ℕ)
    (start charge : ℕ → ℕ) (C : Finset ℕ) (hC : C ⊆ Finset.range n)
    (hstart : MonotoneOn start (Set.Icc 0 n))
    (hcharge : ∀ j ∈ C, start j < charge j ∧ charge j ≤ start (j+1))
    (hrep : ∀ j ∈ C, charge j ∈ policyRepresentatives A N q) :
    C.card ≤ (policyRepresentatives A N q).card ∧ C.card ≤ N/q+1 := by
  have hi := branch_charges_injective start charge C hC hstart hcharge
  have hc : C.card ≤ (policyRepresentatives A N q).card := by
    calc
      _ = (C.image charge).card := (Finset.card_image_of_injOn hi).symm
      _ ≤ _ := Finset.card_le_card (by
        intro p hp
        obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hp
        exact hrep j hj)
  exact ⟨hc,hc.trans (policy_representatives_card A N q)⟩

theorem source_representatives_real_bound (A : ℕ → ℝ) {N : ℕ}
    (hN : 0 < N) {kap : ℝ} (hkap : 0 < kap) (hkap1 : kap ≤ 1) :
    ((policyRepresentatives A N (sourcePolicyBlock N kap)).card:ℝ) ≤ 2/kap := by
  let q := sourcePolicyBlock N kap
  have hq : 0 < q := sourcePolicyBlock_pos hN hkap
  have hqR : (0:ℝ) < q := Nat.cast_pos.mpr hq
  have hc : ((policyRepresentatives A N q).card:ℝ) ≤ ((N/q:ℕ):ℝ)+1 := by
    exact_mod_cast policy_representatives_card A N q
  have hmul : ((N/q:ℕ):ℝ)*(q:ℝ) ≤ (N:ℝ) := by
    exact_mod_cast Nat.div_mul_le_self N q
  have hdiv : ((N/q:ℕ):ℝ) ≤ (N:ℝ)/(q:ℝ) := (le_div_iff₀ hqR).mpr hmul
  have hblock := source_policy_block_lower N kap
  have hrat : (N:ℝ)/(q:ℝ) ≤ 1/kap := (div_le_div_iff₀ hqR hkap).mpr (by
    change (N:ℝ)*kap ≤ 1*(sourcePolicyBlock N kap:ℝ)
    nlinarith)
  have hone : 1 ≤ 1/kap := (le_div_iff₀ hkap).mpr (by simpa using hkap1)
  change ((policyRepresentatives A N q).card:ℝ) ≤ 2/kap
  have he : 2/kap = 1/kap+1/kap := by ring
  rw [he]
  linarith

end PlanarFalconer

end OAI
