import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellReplacementTests

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellReplacement
open PrimeProgression
open scoped BigOperators

def jointUnitTest {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} [NeZero M]
    (F : (ι → (ZMod M)ˣ) → ℂ) (a : ι → ZMod M) : ℂ := by
  classical
  exact ∑ u : ι → (ZMod M)ˣ, if ∀ i, (u i : ZMod M) = a i then F u else 0

lemma jointUnitTest_units {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} [NeZero M]
    (F : (ι → (ZMod M)ˣ) → ℂ) (u : ι → (ZMod M)ˣ) :
    jointUnitTest F (fun i => (u i : ZMod M)) = F u := by
  classical
  have he (v : ι → (ZMod M)ˣ) : (∀ i, (v i : ZMod M) = u i) ↔ v = u := by
    constructor
    · intro h
      funext i
      exact Units.ext (h i)
    · rintro rfl
      exact fun _ => rfl
  simp only [jointUnitTest, he]
  simp

lemma jointUnitTest_nonunit {ι : Type*} [Fintype ι] [DecidableEq ι] {M : ℕ} [NeZero M]
    (F : (ι → (ZMod M)ˣ) → ℂ) (a : ι → ZMod M) (i : ι) (hi : ¬ IsUnit (a i)) :
    jointUnitTest F a = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro u hu
  apply ite_eq_right
  intro h
  exact hi (h i ▸ (u i).isUnit)

theorem finite_product_prior_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    {α : ι → Type*} [∀ i, Fintype (α i)] {M : ℕ} [NeZero M]
    (ρ : ∀ i, α i → ZMod M) (w : ∀ i, α i → ℂ)
    (F : (ι → (ZMod M)ˣ) → ℂ) :
    (∑ p : ∀ i, α i, (∏ i, w i (p i)) * jointUnitTest F (fun i => ρ i (p i))) =
      ∑ u : ι → (ZMod M)ˣ,
        (∏ i, ∑ p : α i, if (u i : ZMod M) = ρ i p then w i p else 0) * F u := by
  classical
  simp_rw [jointUnitTest, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u hu
  rw [Fintype.prod_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Fintype.prod_ite_zero]
  by_cases h : ∀ i, (u i : ZMod M) = ρ i (p i)
  · simp [h]
  · simp [h]

abbrev PrimeCellTuple {ι : Type*} (N : ι → ℕ) (lo hi : ι → ℝ) :=
  ∀ i, {p : ℕ // p ∈ logPrimeSupport (N i) (lo i) (hi i)}

def jointComplexTestSum {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ι → ℕ) (M : ℕ) [NeZero M]
    (lo hi Z : ι → ℝ) (F : (ι → (ZMod M)ˣ) → ℂ) : ℂ :=
  ∑ p : PrimeCellTuple N lo hi,
    (∏ i, (((Z i * ((p i).val : ℝ))⁻¹ : ℝ) : ℂ)) *
      jointUnitTest F (fun i => ((p i).val : ZMod M))

theorem jointComplexTestSum_eq {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ι → ℕ) (M : ℕ) [NeZero M] (lo hi Z : ι → ℝ)
    (F : (ι → (ZMod M)ˣ) → ℂ) :
    jointComplexTestSum N M lo hi Z F =
      ∑ u : ι → (ZMod M)ˣ,
        (∏ i, (residueMass (N i) M (u i) (lo i) (hi i) (Z i) : ℂ)) * F u := by
  classical
  have hpart := finite_product_prior_partition
    (fun i (p : {p : ℕ // p ∈ logPrimeSupport (N i) (lo i) (hi i)}) => (p.val : ZMod M))
    (fun i (p : {p : ℕ // p ∈ logPrimeSupport (N i) (lo i) (hi i)}) =>
      (((Z i * (p.val : ℝ))⁻¹ : ℝ) : ℂ)) F
  change jointComplexTestSum N M lo hi Z F = _ at hpart
  rw [hpart]
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  apply Finset.prod_congr rfl
  intro i hi'
  rw [Finset.sum_coe_sort (logPrimeSupport (N i) (lo i) (hi i))
    (fun p : ℕ => if (u i : ZMod M) = (p : ZMod M) then
      (((Z i * (p : ℝ))⁻¹ : ℝ) : ℂ) else 0)]
  simp only [residueMass, Complex.ofReal_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases he : (p : ZMod M) = (u i : ZMod M)
  · simp [he]
  · simp [he, Ne.symm he]

end Ostmann.Arithmetic.PrimeCellReplacement

end

end OAI
