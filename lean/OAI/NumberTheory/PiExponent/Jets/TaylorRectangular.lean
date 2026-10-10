import OAI.NumberTheory.PiExponent.Geometry.CurveContact
import OAI.NumberTheory.PiExponent.Jets.CommutingTaylor
import OAI.NumberTheory.PiExponent.Jets.TransverseMultiplicity

namespace OAI

noncomputable section
namespace PiExponent.TaylorRectangular

open scoped BigOperators
open CommutingTaylor
open PiExponentApprox

section General
variable {R K : Type*} [CommRing R] [Algebra ℚ R] [Field K] [Algebra ℚ K]

theorem residueTaylor_mem_rectangular (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (ρ : R →+* K) (n : Fin m → ℕ) (a : R)
    (ha : ∀ α : Fin m →₀ ℕ, (∀ i, α i < n i) → ρ (mixedIter m D α a) = 0) :
    residueTaylorFin m D ρ a ∈ TransverseMultiplicity.rectangularIdeal n := by
  intro α hα
  rw [coeff_residueTaylorFin, ha α hα]
  rw [Algebra.smul_def]
  exact mul_zero _

theorem residueTaylor_quotient_eq_zero (m : ℕ) (D : Fin m → Derivation ℚ R R)
    (ρ : R →+* K) (n : Fin m → ℕ) (a : R)
    (ha : ∀ α : Fin m →₀ ℕ, (∀ i, α i < n i) → ρ (mixedIter m D α a) = 0) :
    Ideal.Quotient.mk (TransverseMultiplicity.rectangularIdeal n)
      (residueTaylorFin m D ρ a) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (residueTaylor_mem_rectangular m D ρ n a ha)

end General

def rationalFrame (m : ℕ) (i : Fin (m + 1)) :
    Derivation ℚ (FramePolynomial m) (FramePolynomial m) :=
  (polynomialFrame m i).restrictScalars ℚ

@[simp] theorem rationalFrame_apply (m : ℕ) (i : Fin (m + 1)) (a : FramePolynomial m) :
    rationalFrame m i a = polynomialFrame m i a := rfl

theorem rationalFrame_commute (m : ℕ) (i j : Fin (m + 1)) :
    Commute (rationalFrame m i).toLinearMap (rationalFrame m j).toLinearMap := by
  apply LinearMap.ext
  intro a
  exact polynomialFrame_commute m i j a

def derivativeWord {ι : Type*} : (k : ℕ) → (Fin k → ι) → (Fin k →₀ ℕ) → List ι
  | 0, _, _ => []
  | k+1, B, α => derivativeWord k (fun i => B i.succ) α.tail ++ List.replicate (α 0) (B 0)

theorem frameWord_append (m : ℕ) (u v : List (Fin (m + 1))) (a : FramePolynomial m) :
    polynomialFrameWord m (u ++ v) a = polynomialFrameWord m u (polynomialFrameWord m v a) := by
  induction u with
  | nil => rfl
  | cons i u ih => simp [polynomialFrameWord_cons, ih]

theorem frameWord_replicate (m : ℕ) (i : Fin (m + 1)) (n : ℕ) (a : FramePolynomial m) :
    polynomialFrameWord m (List.replicate n i) a = iter (rationalFrame m i) n a := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

theorem mixedIter_eq_frameWord (m k : ℕ) (B : Fin k → Fin (m + 1))
    (α : Fin k →₀ ℕ) (a : FramePolynomial m) :
    mixedIter k (fun i => rationalFrame m (B i)) α a =
      polynomialFrameWord m (derivativeWord k B α) a := by
  induction k generalizing a with
  | zero => rfl
  | succ k ih =>
    simp only [mixedIter, LinearMap.comp_apply, derivativeWord, frameWord_append,
      frameWord_replicate]
    exact ih (fun i => B i.succ) α.tail _

theorem derivativeWord_cost (m k : ℕ) (B : Fin k → Fin (m + 1))
    (α : Fin k →₀ ℕ) (cost : Fin (m + 1) → ℝ) :
    frameWordCost cost (derivativeWord k B α) = ∑ i, (α i : ℝ) * cost (B i) := by
  induction k with
  | zero => simp [derivativeWord, frameWordCost]
  | succ k ih =>
    simp only [derivativeWord, frameWordCost, List.map_append, List.sum_append,
      List.map_replicate, List.sum_replicate]
    change frameWordCost cost (derivativeWord k (fun i => B i.succ) α.tail) +
      (α 0) • cost (B 0) = _
    rw [ih, Fin.sum_univ_succ]
    simp only [Finsupp.tail_apply, nsmul_eq_mul]
    ring

theorem derivativeWord_cost_le (m k : ℕ) (B : Fin k → Fin (m + 1))
    (α : Fin k →₀ ℕ) (cost : Fin (m + 1) → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i) (hα : ∀ i, α i < n i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ) :
    frameWordCost cost (derivativeWord k B α) ≤ δ := by
  rw [derivativeWord_cost]
  apply le_trans _ hn
  apply Finset.sum_le_sum
  intro i hi
  apply mul_le_mul_of_nonneg_right _ (hcost _)
  exact_mod_cast (by have := hα i; omega : α i ≤ n i - 1)

theorem frame_residueTaylor_ideal_le {K : Type*} [Field K] [Algebra ℚ K]
    (m k : ℕ) (B : Fin k → Fin (m + 1)) (ρ : FramePolynomial m →+* K)
    (I : Ideal (FramePolynomial m)) (cost : Fin (m + 1) → ℝ) (n : Fin k → ℕ) (δ : ℝ)
    (hcost : ∀ i, 0 ≤ cost i)
    (hn : ∑ i, ((n i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ)
    (hvanish : ∀ a ∈ I, ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ δ →
      ρ (polynomialFrameWord m word a) = 0) :
    I ≤ (TransverseMultiplicity.rectangularIdeal n).comap
      (residueTaylorFin k (fun i => rationalFrame m (B i)) ρ) := by
  intro a ha
  apply residueTaylor_mem_rectangular
  intro α hα
  rw [mixedIter_eq_frameWord]
  exact hvanish a ha _ (derivativeWord_cost_le m k B α cost n δ hcost hα hn)

def costRectangle (m k : ℕ) (B : Fin k → Fin (m + 1))
    (cost : Fin (m + 1) → ℝ) (δ : ℝ) (i : Fin k) : ℕ :=
  ⌊δ / ((k : ℝ) * cost (B i))⌋₊ + 1

@[simp] theorem costRectangle_pos (m k : ℕ) (B : Fin k → Fin (m + 1))
    (cost : Fin (m + 1) → ℝ) (δ : ℝ) (i : Fin k) :
    0 < costRectangle m k B cost δ i := Nat.zero_lt_succ _

theorem costRectangle_budget (m k : ℕ) (B : Fin k → Fin (m + 1))
    (cost : Fin (m + 1) → ℝ) (δ : ℝ)
    (hk : 0 < k) (hc : ∀ i, 0 < cost (B i)) (hδ : 0 ≤ δ) :
    ∑ i, ((costRectangle m k B cost δ i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hi (i : Fin k) :
      ((costRectangle m k B cost δ i - 1 : ℕ) : ℝ) * cost (B i) ≤ δ / k := by
    simp only [costRectangle, Nat.add_sub_cancel]
    have hf := Nat.floor_le (div_nonneg hδ (mul_pos hkR (hc i)).le)
    have hmul := (le_div_iff₀ (mul_pos hkR (hc i))).mp hf
    apply (le_div_iff₀ hkR).2
    nlinarith
  calc
    _ ≤ ∑ _i : Fin k, δ / (k : ℝ) := Finset.sum_le_sum (fun i _ => hi i)
    _ = δ := by simp [Finset.sum_const, nsmul_eq_mul]; field_simp

theorem costRectangle_product_lower (m k : ℕ) (B : Fin k → Fin (m + 1))
    (cost : Fin (m + 1) → ℝ) (δ : ℝ)
    (hk : 0 < k) (hc : ∀ i, 0 < cost (B i)) (hδ : 0 ≤ δ) :
    δ ^ k / ((k : ℝ) ^ k * ∏ i, cost (B i)) ≤
      ((∏ i, costRectangle m k B cost δ i : ℕ) : ℝ) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    _ = ∏ i : Fin k, δ / ((k : ℝ) * cost (B i)) := by
      simp [Finset.prod_div_distrib, Finset.prod_mul_distrib]
    _ ≤ ∏ i : Fin k, (costRectangle m k B cost δ i : ℝ) := by
      apply Finset.prod_le_prod₀ (fun i _ => div_nonneg hδ (mul_pos hkR (hc i)).le)
      intro i hi
      simpa [costRectangle] using
        (Nat.lt_floor_add_one (δ / ((k : ℝ) * cost (B i)))).le
    _ = _ := by simp

theorem frame_residueTaylor_costRectangle_ideal_le {K : Type*} [Field K] [Algebra ℚ K]
    (m k : ℕ) (B : Fin k → Fin (m + 1)) (ρ : FramePolynomial m →+* K)
    (I : Ideal (FramePolynomial m)) (cost : Fin (m + 1) → ℝ) (δ : ℝ)
    (hk : 0 < k) (hcost : ∀ i, 0 ≤ cost i) (hc : ∀ i, 0 < cost (B i)) (hδ : 0 ≤ δ)
    (hvanish : ∀ a ∈ I, ∀ word : List (Fin (m + 1)), frameWordCost cost word ≤ δ →
      ρ (polynomialFrameWord m word a) = 0) :
    I ≤ (TransverseMultiplicity.rectangularIdeal (costRectangle m k B cost δ)).comap
      (residueTaylorFin k (fun i => rationalFrame m (B i)) ρ) :=
  frame_residueTaylor_ideal_le m k B ρ I cost _ δ hcost
    (costRectangle_budget m k B cost δ hk hc hδ) hvanish

end PiExponent.TaylorRectangular

end

end OAI
