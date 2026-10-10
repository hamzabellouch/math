import OAI.NumberTheory.Ostmann.Arithmetic.PrimeCellReplacement

namespace OAI

open _root_.Erdos970 _root_.OAI.Erdos970

open Erdos970.Erdos970Dependency.SiegelWalfisz

noncomputable section
namespace Ostmann.Arithmetic.PrimeCellReplacement
open scoped BigOperators
open PrimeProgression

def unitTest {M : ℕ} [NeZero M] {A : Type*} [AddCommMonoid A]
    (F : (ZMod M)ˣ → A) (a : ZMod M) : A := by
  classical
  exact ∑ u : (ZMod M)ˣ, if (u : ZMod M) = a then F u else 0

theorem unitTest_unit {M : ℕ} [NeZero M] {A : Type*} [AddCommMonoid A]
    (F : (ZMod M)ˣ → A) (u : (ZMod M)ˣ) : unitTest F (u : ZMod M) = F u := by
  classical
  simp [unitTest, Units.val_inj]

theorem unitTest_nonunit {M : ℕ} [NeZero M] {A : Type*} [AddCommMonoid A]
    (F : (ZMod M)ˣ → A) {a : ZMod M} (ha : ¬ IsUnit a) : unitTest F a = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro u _
  apply ite_eq_right
  intro he
  exact ha (he ▸ u.isUnit)

theorem sum_weighted_unitTest {M : ℕ} [NeZero M] {A : Type*} [Semiring A]
    (S : Finset ℕ) (w : ℕ → A) (F : (ZMod M)ˣ → A) :
    (∑ p ∈ S, w p * unitTest F (p : ZMod M)) =
      ∑ u : (ZMod M)ˣ, (∑ p ∈ S.filter (fun p : ℕ => (p : ZMod M) = u), w p) * F u := by
  classical
  simp_rw [unitTest, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  rw [Finset.sum_mul, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : (u : ZMod M) = (p : ZMod M) <;> simp [hp, eq_comm]

theorem sum_weighted_unitTest_filter_coprime {M : ℕ} [NeZero M]
    {A : Type*} [Semiring A] (S : Finset ℕ) (w : ℕ → A) (F : (ZMod M)ˣ → A) :
    (∑ p ∈ S, w p * unitTest F (p : ZMod M)) =
      ∑ p ∈ S.filter (fun p => p.Coprime M), w p * unitTest F (p : ZMod M) := by
  classical
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hn
  have hcp : ¬ p.Coprime M := by simpa only [Finset.mem_filter, hp, true_and] using hn
  have hu : ¬ IsUnit (p : ZMod M) := fun h => hcp ((ZMod.isUnit_iff_coprime p M).mp h)
  rw [unitTest_nonunit F hu, mul_zero]

def complexTestSum (N M : ℕ) [NeZero M] (lo hi Z : ℝ) (F : (ZMod M)ˣ → ℂ) : ℂ :=
  ∑ p ∈ logPrimeSupport N lo hi, ((Z*(p:ℝ))⁻¹ : ℝ) * unitTest F (p : ZMod M)

def realTestSum (N M : ℕ) [NeZero M] (lo hi Z : ℝ) (F : (ZMod M)ˣ → ℝ) : ℝ :=
  ∑ p ∈ logPrimeSupport N lo hi, (Z*(p:ℝ))⁻¹ * unitTest F (p : ZMod M)

theorem complexTestSum_eq (N M : ℕ) [NeZero M] (lo hi Z : ℝ)
    (F : (ZMod M)ˣ → ℂ) :
    complexTestSum N M lo hi Z F = ∑ u : (ZMod M)ˣ, (residueMass N M u lo hi Z : ℂ) * F u := by
  simpa only [complexTestSum, residueMass, Complex.ofReal_sum] using
    sum_weighted_unitTest (logPrimeSupport N lo hi) (fun p => (((Z*(p:ℝ))⁻¹ : ℝ) : ℂ)) F

theorem realTestSum_eq (N M : ℕ) [NeZero M] (lo hi Z : ℝ)
    (F : (ZMod M)ˣ → ℝ) :
    realTestSum N M lo hi Z F = ∑ u : (ZMod M)ˣ, residueMass N M u lo hi Z * F u :=
  sum_weighted_unitTest (logPrimeSupport N lo hi) (fun p => (Z*(p:ℝ))⁻¹) F

end Ostmann.Arithmetic.PrimeCellReplacement

end

end OAI
