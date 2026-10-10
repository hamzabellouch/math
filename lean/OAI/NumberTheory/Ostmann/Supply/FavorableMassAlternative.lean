import OAI.NumberTheory.Ostmann.Preliminaries.MertensHarmonicBands
import OAI.NumberTheory.Ostmann.Supply.CollisionPrimeCellBudget

namespace OAI

/-! # Failure of favorable mass forces a large sparse balanced prime set -/

namespace Ostmann
open scoped Classical BigOperators

noncomputable def favorableTransformPrimes (P : Finset ℕ) (S : ℕ → Finset ℕ)
    (γ : ℕ → ℝ) (δ : ℝ) : Finset ℕ :=
  P.filter (fun p => (p : ℝ) / 3 ≤ (S p).card ∧
    ((S p).card : ℝ) ≤ 2 * p / 3 ∧ δ ≤ γ p)

noncomputable def sparseTransformPrimes (P : Finset ℕ) (S : ℕ → Finset ℕ)
    (γ : ℕ → ℝ) (δ : ℝ) : Finset ℕ :=
  P.filter (fun p => (p : ℝ) / 3 ≤ (S p).card ∧
    ((S p).card : ℝ) ≤ 2 * p / 3 ∧ γ p < δ)

theorem sparse_transform_mass_lower (P : Finset ℕ) (S T : ℕ → Finset ℕ)
    (μ ν : ℕ → ℕ → ℝ) (γ : ℕ → ℝ) (δ G D : ℝ) (hG : 0 < G)
    (hprime : ∀ p ∈ P, p.Prime) (hlog : ∀ p ∈ P, G ≤ Real.log (p : ℝ))
    (hS : ∀ p ∈ P, (S p).Nonempty) (hT : ∀ p ∈ P, (T p).Nonempty)
    (hcard : ∀ p ∈ P, (S p).card + (T p).card = p)
    (hbudget : (∑ p ∈ P, Real.log (p : ℝ) * collisionDefect p (S p) (T p) (μ p) (ν p)) ≤ D) :
    (∑ p ∈ P, (p : ℝ)⁻¹) - 4 * D / G -
        (∑ p ∈ favorableTransformPrimes P S γ δ, (p : ℝ)⁻¹) ≤
      ∑ p ∈ sparseTransformPrimes P S γ δ, (p : ℝ)⁻¹ := by
  let E := collisionExceptionalPrimes P S T μ ν
  let F := favorableTransformPrimes P S γ δ
  let R := P \ (E ∪ F)
  have hE : E ⊆ P := Finset.filter_subset _ _
  have hF : F ⊆ P := Finset.filter_subset _ _
  have hbad := collisionExceptionalPrimes_log_mass P S T μ ν D hprime hS hT
    (fun p hp => (hcard p hp).le) hbudget
  have hbadmass : (∑ p ∈ E, (p : ℝ)⁻¹) ≤ 4 * D / G := by
    apply (le_div_iff₀ hG).mpr
    calc
      _ = ∑ p ∈ E, G * (p : ℝ)⁻¹ := by rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
      _ ≤ ∑ p ∈ E, Real.log (p : ℝ) / p := by
        apply Finset.sum_le_sum
        intro p hp
        simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right (hlog p (hE hp)) (by positivity : 0 ≤ (p : ℝ)⁻¹)
      _ ≤ _ := hbad
  have hR : R ⊆ sparseTransformPrimes P S γ δ := by
    intro p hp
    obtain ⟨hpP, hpnot⟩ := Finset.mem_sdiff.mp hp
    have hpE : p ∉ E := fun he => hpnot (Finset.mem_union_left _ he)
    have hpF : p ∉ F := fun hf => hpnot (Finset.mem_union_right _ hf)
    have hb := collision_retained_prime_balanced P S T μ ν hS hT hcard p
      (Finset.mem_sdiff.mpr ⟨hpP, hpE⟩)
    apply Finset.mem_filter.mpr
    refine ⟨hpP, hb.1, hb.2, ?_⟩
    by_contra h
    exact hpF (Finset.mem_filter.mpr ⟨hpP, hb.1, hb.2, le_of_not_gt h⟩)
  have hremove : (∑ p ∈ R, (p : ℝ)⁻¹) =
      (∑ p ∈ P, (p : ℝ)⁻¹) - ∑ p ∈ E ∪ F, (p : ℝ)⁻¹ :=
    Finset.sum_sdiff_eq_sub (Finset.union_subset hE hF)
  have hunion := Finset.sum_union_inter (s₁ := E) (s₂ := F) (f := fun p => (p : ℝ)⁻¹)
  have hinter : 0 ≤ ∑ p ∈ E ∩ F, (p : ℝ)⁻¹ := Finset.sum_nonneg (fun _ _ => by positivity)
  have hremaining : (∑ p ∈ P, (p : ℝ)⁻¹) - (∑ p ∈ E, (p : ℝ)⁻¹) -
      (∑ p ∈ F, (p : ℝ)⁻¹) ≤ ∑ p ∈ R, (p : ℝ)⁻¹ := by linarith
  have hmass : (∑ p ∈ R, (p : ℝ)⁻¹) ≤ ∑ p ∈ sparseTransformPrimes P S γ δ, (p : ℝ)⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hR (fun _ _ _ => by positivity)
  change _ - 4 * D / G - (∑ p ∈ F, (p : ℝ)⁻¹) ≤ _
  linarith

end Ostmann

end OAI
