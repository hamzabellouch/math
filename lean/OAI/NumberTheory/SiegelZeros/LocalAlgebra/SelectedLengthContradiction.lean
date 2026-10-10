import Mathlib.Data.Fintype.Card
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Length
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.SetTheory.Cardinal.Finite
import OAI.NumberTheory.SiegelZeros.Estimates.RectangleNumerics
import OAI.NumberTheory.SiegelZeros.Structure.SelectedComponentTaylor

namespace OAI

namespace SiegelZeros

noncomputable section

namespace WeightedTorusJets.W25

open MvPolynomial

variable {σ K : Type*} [Fintype σ] [Field K]

def truncationIdeal (t : σ → ℕ) : Ideal (MvPolynomial σ K) :=
  Ideal.span (Set.range fun i => (X i : MvPolynomial σ K) ^ (t i + 1))

abbrev Box (t : σ → ℕ) := (i : σ) → Fin (t i + 1)

def boxExponent (t : σ → ℕ) (a : Box t) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun i => (a i).val

@[simp] theorem boxExponent_apply (t : σ → ℕ) (a : Box t) (i : σ) :
    boxExponent t a i = (a i).val := rfl

theorem boxExponent_injective (t : σ → ℕ) : Function.Injective (boxExponent t) := by
  intro a b h
  funext i
  apply Fin.ext
  exact congrArg (fun m : σ →₀ ℕ => m i) h

omit [Fintype σ] in
theorem mem_truncationIdeal_iff (t : σ → ℕ) (p : MvPolynomial σ K) :
    p ∈ truncationIdeal (K := K) t ↔ ∀ m ∈ p.support, ∃ i, t i + 1 ≤ m i := by
  classical
  have hr : (Set.range fun i => (X i : MvPolynomial σ K) ^ (t i + 1)) =
      (fun m => monomial m (1 : K)) ''
        Set.range (fun i => Finsupp.single i (t i + 1)) := by
    ext f
    simp only [Set.mem_range, Set.mem_image]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, X_pow_eq_monomial.symm⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, X_pow_eq_monomial⟩
  rw [truncationIdeal, hr, mem_ideal_span_monomial_image]
  simp only [Set.mem_range, exists_exists_eq_and, Finsupp.single_le_iff]

def boxCoefficients (t : σ → ℕ) : MvPolynomial σ K →ₗ[K] (Box t → K) where
  toFun p a := p.coeff (boxExponent t a)
  map_add' p q := by ext a; simp
  map_smul' c p := by ext a; simp

@[simp] theorem boxCoefficients_apply (t : σ → ℕ) (p : MvPolynomial σ K) (a : Box t) :
    boxCoefficients t p a = p.coeff (boxExponent t a) := rfl

theorem ker_boxCoefficients (t : σ → ℕ) :
    LinearMap.ker (boxCoefficients (K := K) t) =
      (truncationIdeal (K := K) t).restrictScalars K := by
  classical
  ext p
  change boxCoefficients t p = 0 ↔ p ∈ truncationIdeal (K := K) t
  rw [mem_truncationIdeal_iff]
  constructor
  · intro hp m hm
    by_contra hn
    have hbound : ∀ i, m i < t i + 1 := by simpa only [not_exists, not_le] using hn
    let a : Box t := fun i => ⟨m i, hbound i⟩
    have ha : boxExponent t a = m := by ext i; rfl
    have hz := congrFun hp a
    have : p.coeff m = 0 := by simpa only [boxCoefficients_apply, ha, Pi.zero_apply] using hz
    exact (MvPolynomial.mem_support_iff.mp hm) this
  · intro hp
    funext a
    change p.coeff (boxExponent t a) = 0
    by_contra hn
    obtain ⟨i, hi⟩ := hp _ (MvPolynomial.mem_support_iff.mpr hn)
    exact (Nat.not_le_of_lt (a i).isLt) hi

theorem boxCoefficients_surjective (t : σ → ℕ) :
    Function.Surjective (boxCoefficients (K := K) t) := by
  classical
  intro f
  refine ⟨∑ a : Box t, monomial (boxExponent t a) (f a), ?_⟩
  funext a
  simp [boxCoefficients_apply, coeff_monomial,
    (boxExponent_injective t).eq_iff]

def truncatedQuotientEquiv (t : σ → ℕ) :
    (MvPolynomial σ K ⧸ truncationIdeal (K := K) t) ≃ₗ[K] (Box t → K) :=
  (Submodule.quotEquivOfEq _ _ (ker_boxCoefficients (K := K) t).symm).trans
    ((boxCoefficients (K := K) t).quotKerEquivOfSurjective (boxCoefficients_surjective (K := K) t))

theorem finrank_truncatedQuotient (t : σ → ℕ) :
    Module.finrank K (MvPolynomial σ K ⧸ truncationIdeal (K := K) t) =
      ∏ i, (t i + 1) := by
  classical
  rw [(truncatedQuotientEquiv (K := K) t).finrank_eq, Module.finrank_pi]
  simp only [Box, Fintype.card_pi, Fintype.card_fin]

instance truncatedQuotient_finite (t : σ → ℕ) :
    Module.Finite K (MvPolynomial σ K ⧸ truncationIdeal (K := K) t) :=
  Module.Finite.of_injective (truncatedQuotientEquiv (K := K) t).toLinearMap
    (truncatedQuotientEquiv (K := K) t).injective

theorem coefficientField_length_truncatedQuotient (t : σ → ℕ) :
    Module.length K (MvPolynomial σ K ⧸ truncationIdeal (K := K) t) =
      (∏ i, (t i + 1) : ℕ) := by
  rw [Module.length_eq_finrank, finrank_truncatedQuotient]

end WeightedTorusJets.W25

end

section

namespace WeightedTorusJets.RectangleNumerics

theorem finite_value_of_bound (L : ℕ∞) (B : ℕ) (hL : L ≤ (B : ℕ∞)) :
    ∃ n : ℕ, L = (n : ℕ∞) ∧ n ≤ B := by
  have hfin : L ≠ ⊤ := ne_top_of_le_ne_top (ENat.natCast_ne_top B) hL
  exact ⟨L.toNat, (ENat.natCast_toNat hfin).symm, ENat.toNat_le_of_le_natCast hL⟩

section Modules

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

theorem finite_length_of_bound (B : ℕ) (upper : Module.length R M ≤ (B : ℕ∞)) :
    IsFiniteLength R M :=
  Module.length_ne_top_iff.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top B) upper)

theorem enat_length_bounds_incompatible
    (H N h : ℕ) (hH : 0 < H) (hHN : H ≤ N) (hh : 1 ≤ h) (hh4 : h ≤ 4)
    (I : Finset (Fin 3)) (hcard : I.card = min h 3) (L : ℕ∞)
    (upper : L ≤ (((4 * N) ^ h : ℕ) : ℕ∞))
    (lower : ((∏ j ∈ I, (truncation H N j + 1) : ℕ) : ℕ∞) ≤ L) : False := by
  have hnat : (∏ j ∈ I, (truncation H N j + 1) : ℕ) ≤ (4 * N) ^ h :=
    ENat.natCast_le_natCast.mp (lower.trans upper)
  have hreal : (∏ j ∈ I, ((truncation H N j : ℝ) + 1)) ≤ (4 * (N : ℝ)) ^ h := by
    exact_mod_cast hnat
  exact length_bounds_incompatible_nat H N h hH hHN hh hh4 I hcard
    ((4 * (N : ℝ)) ^ h) le_rfl hreal

theorem module_length_bounds_incompatible
    (H N h : ℕ) (hH : 0 < H) (hHN : H ≤ N) (hh : 1 ≤ h) (hh4 : h ≤ 4)
    (I : Finset (Fin 3)) (hcard : I.card = min h 3)
    (upper : Module.length R M ≤ (((4 * N) ^ h : ℕ) : ℕ∞))
    (lower : ((∏ j ∈ I, (truncation H N j + 1) : ℕ) : ℕ∞) ≤ Module.length R M) :
    False :=
  enat_length_bounds_incompatible H N h hH hHN hh hh4 I hcard
    (Module.length R M) upper lower

end Modules

section CoefficientQuotient

abbrev selectedQuotient (K : Type*) [Field K] (H N : ℕ) (I : Finset (Fin 3)) :=
  MvPolynomial I K ⧸ W25.truncationIdeal (K := K) (fun j : I => truncation H N j.val)

theorem selectedQuotient_coefficient_length (K : Type*) [Field K] (H N : ℕ) (I : Finset (Fin 3)) :
    Module.length K (selectedQuotient K H N I) =
      ((∏ j ∈ I, (truncation H N j + 1) : ℕ) : ℕ∞) := by
  have hlength := W25.coefficientField_length_truncatedQuotient (K := K)
    (fun j : I => truncation H N j.val)
  have hproduct : (∏ j : I, (truncation H N j.val + 1)) =
      ∏ j ∈ I, (truncation H N j + 1) :=
    Finset.prod_coe_sort I (fun j : Fin 3 => truncation H N j + 1)
  exact hlength.trans (congrArg (fun n : ℕ => (n : ℕ∞)) hproduct)

theorem coefficient_length_bounds_incompatible (K : Type*) [Field K]
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (H N h : ℕ) (hH : 0 < H) (hHN : H ≤ N) (hh : 1 ≤ h) (hh4 : h ≤ 4)
    (I : Finset (Fin 3)) (hcard : I.card = min h 3)
    (upper : Module.length R M ≤ (((4 * N) ^ h : ℕ) : ℕ∞))
    (lower : Module.length K (selectedQuotient K H N I) ≤ Module.length R M) :
    False := by
  rw [selectedQuotient_coefficient_length] at lower
  exact module_length_bounds_incompatible H N h hH hHN hh hh4 I hcard upper lower

end CoefficientQuotient

end WeightedTorusJets.RectangleNumerics

end

section

namespace WeightedTorusJets.RectangleNumerics

open SiegelZeros.W23

noncomputable def selectedFinset (S : Set (Fin 3)) : Finset (Fin 3) := by
  classical
  exact S.toFinset

@[simp] theorem mem_selectedFinset (S : Set (Fin 3)) (j : Fin 3) :
    j ∈ selectedFinset S ↔ j ∈ S := by
  classical
  simp [selectedFinset]

theorem selectedFinset_card (S : Set (Fin 3)) :
    (selectedFinset S).card = Nat.card S := by
  classical
  rw [selectedFinset, Set.toFinset_card, Nat.card_eq_fintype_card]

theorem selectedSet_card_le_three (S : Set (Fin 3)) : Nat.card S ≤ 3 := by
  rw [← selectedFinset_card]
  simpa only [Fintype.card_fin] using (selectedFinset S).card_le_univ

theorem selectedCutoffs_product (t : Fin 3 → ℕ) (S : Set (Fin 3)) :
    (∏ j : Fin 3, (selectedCutoffs t S j + 1)) =
      ∏ j ∈ selectedFinset S, (t j + 1) := by
  classical
  calc
    (∏ j : Fin 3, (selectedCutoffs t S j + 1)) =
        ∏ j ∈ selectedFinset S, (selectedCutoffs t S j + 1) := by
      symm
      apply Finset.prod_subset (Finset.subset_univ _)
      intro j _ hj
      have hjS : j ∉ S := fun h => hj ((mem_selectedFinset S j).mpr h)
      simp only [selectedCutoffs_of_not_mem t S j hjS, zero_add]
    _ = ∏ j ∈ selectedFinset S, (t j + 1) := by
      apply Finset.prod_congr rfl
      intro j hj
      rw [selectedCutoffs_of_mem t S j ((mem_selectedFinset S j).mp hj)]

theorem selectedCutoffs_length_bounds_incompatible
    (H N h : ℕ) (hH : 0 < H) (hHN : H ≤ N) (hh : 1 ≤ h) (hh4 : h ≤ 4)
    (S : Set (Fin 3)) (hcard : Nat.card S = min h 3) (L : ℕ∞)
    (upper : L ≤ (((4 * N) ^ h : ℕ) : ℕ∞))
    (lower : ((∏ j : Fin 3,
      (selectedCutoffs (fun j => truncation H N j) S j + 1) : ℕ) : ℕ∞) ≤ L) :
    False := by
  rw [selectedCutoffs_product] at lower
  exact enat_length_bounds_incompatible H N h hH hHN hh hh4
    (selectedFinset S) ((selectedFinset_card S).trans hcard) L upper lower

theorem generic_selectedCutoffs_length_bounds_incompatible
    (H N h : ℕ) (hH : 0 < H) (hHN : H ≤ N) (hh : 1 ≤ h) (hh3 : h ≤ 3)
    (S : Set (Fin 3)) (hcard : Nat.card S = h) (L : ℕ∞)
    (upper : L ≤ (((4 * N) ^ h : ℕ) : ℕ∞))
    (lower : ((∏ j : Fin 3,
      (selectedCutoffs (fun j => truncation H N j) S j + 1) : ℕ) : ℕ∞) ≤ L) :
    False := by
  apply selectedCutoffs_length_bounds_incompatible H N h hH hHN hh
    (hh3.trans (by decide : 3 ≤ 4)) S _ L upper lower
  simpa only [min_eq_left hh3] using hcard

theorem full_length_bounds_incompatible
    (H N : ℕ) (hH : 0 < H) (hHN : H ≤ N) (L : ℕ∞)
    (upper : L ≤ (((4 * N) ^ 4 : ℕ) : ℕ∞))
    (lower : ((∏ j : Fin 3, (truncation H N j + 1) : ℕ) : ℕ∞) ≤ L) :
    False := by
  exact enat_length_bounds_incompatible H N 4 hH hHN (by decide) (by decide)
    Finset.univ (by norm_num) L upper lower

end WeightedTorusJets.RectangleNumerics

end

end SiegelZeros

end OAI
