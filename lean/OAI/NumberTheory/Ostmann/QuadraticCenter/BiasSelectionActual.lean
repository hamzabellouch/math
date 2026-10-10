import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasSelectionDeletion
import OAI.NumberTheory.Ostmann.QuadraticCenter.BiasSelectionTransfer

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Ostmann.Characters Ostmann.Preliminaries Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def quadraticBiasedPrimes (d : Decomposition) (Q : ℕ) (δ : ℝ)
    (P : Finset (PrimeUpTo Q)) : Finset (PrimeUpTo Q) :=
  P.filter (fun p => p.val ≠ 2 ∧
    δ ≤ (maxTranslatedBias (d.residueSupport p.val) (quadraticCharacter p.val) : ℝ))

def boundedPrimeWeight {Q : ℕ} (P : Finset (PrimeUpTo Q)) : ℝ :=
  ∑ p ∈ P, Real.log p.val / p.val

def biasSelectionCost (δ : ℝ) : ℝ :=
  (3 + 128 / δ ^ 2) * collisionConstant 4

lemma bounded_prime_weight_nonneg {Q : ℕ} (p : PrimeUpTo Q) :
    0 ≤ Real.log p.val / p.val :=
  div_nonneg (Real.log_nonneg (by exact_mod_cast (primeUpTo_prime p).one_le)) (Nat.cast_nonneg _)

lemma sum_subset_univ_nonneg {α : Type*} [Fintype α] (P : Finset α)
    (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) : (∑ a ∈ P, f a) ≤ ∑ a, f a := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun a _ _ => hf a)

theorem eventually_oriented_biased_subset (d : Decomposition) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℕ in atTop, ∀ P : Finset (PrimeUpTo (collisionScale 4 X)),
      ∃ G : Finset (PrimeUpTo (collisionScale 4 X)),
        G ⊆ quadraticBiasedPrimes d (collisionScale 4 X) δ P ∧
        ∃ ε t : PrimeUpTo (collisionScale 4 X) → ℤ,
          (∀ p ∈ G, (ε p = 1 ∨ ε p = -1) ∧
            δ / 4 ≤ (∑ a ∈ positiveIntegerWindow d.A X,
              ((ε p * jacobiSym (a - t p) p.val : ℤ) : ℝ)) /
                (positiveIntegerWindow d.A X).card ∧
            (∑ a ∈ negativeIntegerWindow d.B X,
              ((ε p * jacobiSym (a - t p) p.val : ℤ) : ℝ)) /
                (negativeIntegerWindow d.B X).card ≤ -δ / 4) ∧
          boundedPrimeWeight (quadraticBiasedPrimes d (collisionScale 4 X) δ P) ≤
            boundedPrimeWeight G + biasSelectionCost δ * Real.log (Real.log (X : ℝ)) := by
  classical
  filter_upwards [eventually_quadratic_window_errors d,
    eventually_upperWindow_density_stability d, eventually_collision_bound_conditions 4]
    with X herr hden hcond
  intro P
  let Q := collisionScale 4 X
  choose center hcenter using
    (fun p : PrimeUpTo Q => exists_max_quadratic_translation (d.residueSupport p.val))
  let mS : PrimeUpTo Q → ℝ := fun p => quadraticResidueMean (d.residueSupport p.val) (center p)
  let mT : PrimeUpTo Q → ℝ := fun p => quadraticResidueMean (d.residueSupport p.val)ᶜ (center p)
  let aMean : PrimeUpTo Q → ℝ := fun p =>
    integerQuadraticMean (positiveIntegerWindow d.A X) p.val ((center p).val : ℤ)
  let dMean : PrimeUpTo Q → ℝ := fun p =>
    integerQuadraticMean (negativeIntegerWindow d.B X) p.val ((center p).val : ℤ)
  let eA : PrimeUpTo Q → ℝ := fun p => |aMean p - mS p|
  let eD : PrimeUpTo Q → ℝ := fun p => |dMean p - mT p|
  let σ : PrimeUpTo Q → ℝ := fun p => d.residueDensity p.val
  let w : PrimeUpTo Q → ℝ := fun p => Real.log p.val / p.val
  let P₀ := quadraticBiasedPrimes d Q δ P
  let G := P₀.filter (fun p => GoodBiasApproximation δ (σ p) (eA p) (eD p))
  let ε : PrimeUpTo Q → ℤ := fun p => biasOrientation (mS p)
  let t : PrimeUpTo Q → ℤ := fun p => (center p).val
  refine ⟨G, Finset.filter_subset _ _, ε, t, ?_, ?_⟩
  · intro p hp
    obtain ⟨hpb, hg⟩ := Finset.mem_filter.mp hp
    obtain ⟨_, hpodd, hpbias⟩ := Finset.mem_filter.mp hpb
    have hs : δ ≤ (ε p : ℝ) * mS p := by
      dsimp only [ε]
      rw [biasOrientation_mul, ← hcenter p]
      exact hpbias
    have hpair := oriented_empirical_pair hδ hg.1 hg.2.1
      (quadratic_complement_density_relation d hpodd (center p))
      (biasOrientation_sign (mS p)) hs hg.2.2.1 hg.2.2.2
    refine ⟨biasOrientation_sign (mS p), ?_⟩
    simpa only [oriented_integerQuadraticMean] using hpair
  · let E := collisionConstant 4 * Real.log (Real.log (X : ℝ))
    have hE : 0 ≤ E := mul_nonneg (collisionConstant_pos 4).le (by linarith [hcond.2.2.1])
    have hw : ∀ p : PrimeUpTo Q, 0 ≤ w p := bounded_prime_weight_nonneg
    have hAfull : (∑ p : PrimeUpTo Q, w p * eA p ^ 2) ≤ E := by
      simpa only [w, eA, aMean, mS, sq_abs] using (herr center).1
    have hDfull : (∑ p : PrimeUpTo Q, w p * eD p ^ 2) ≤ E := by
      simpa only [w, eD, dMean, mT, sq_abs] using (herr center).2
    have hSfull : (∑ p : PrimeUpTo Q, w p * (σ p - 1 / 2) ^ 2) ≤ E / 16 := by
      simpa only [w, σ, E, div_mul_eq_mul_div] using hden
    have hA := (sum_subset_univ_nonneg P₀ (fun p => w p * eA p ^ 2)
      (fun p => mul_nonneg (hw p) (sq_nonneg _))).trans hAfull
    have hD := (sum_subset_univ_nonneg P₀ (fun p => w p * eD p ^ 2)
      (fun p => mul_nonneg (hw p) (sq_nonneg _))).trans hDfull
    have hS := (sum_subset_univ_nonneg P₀ (fun p => w p * (σ p - 1 / 2) ^ 2)
      (fun p => mul_nonneg (hw p) (sq_nonneg _))).trans hSfull
    have hdel := goodBiasApproximation_weight P₀ w σ eA eD hδ (fun p _ => hw p)
    change boundedPrimeWeight P₀ ≤ boundedPrimeWeight G + _
    change (∑ p ∈ P₀, w p) ≤ (∑ p ∈ G, w p) + _
    calc
      _ ≤ (∑ p ∈ G, w p) + 36 * (∑ p ∈ P₀, w p * (σ p - 1 / 2) ^ 2) +
          (64 / δ ^ 2) * ((∑ p ∈ P₀, w p * eA p ^ 2) +
            (∑ p ∈ P₀, w p * eD p ^ 2)) := hdel
      _ ≤ (∑ p ∈ G, w p) + 36 * (E / 16) + (64 / δ ^ 2) * (E + E) := by gcongr
      _ = (∑ p ∈ G, w p) + (9 / 4 + 128 / δ ^ 2) * E := by ring
      _ ≤ (∑ p ∈ G, w p) + (3 + 128 / δ ^ 2) * E := by gcongr; norm_num
      _ = _ := by unfold biasSelectionCost E; ring

end Ostmann.QuadraticCenter

end

end OAI
