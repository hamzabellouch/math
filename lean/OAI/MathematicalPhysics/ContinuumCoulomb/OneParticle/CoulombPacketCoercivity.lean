import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.CoulombPacketTests

namespace OAI

/-! Global Coulomb coercivity from disjoint compact tests and approximate
local duality. All integrals range over the whole Euclidean space. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace ContinuumCoulomb.CoulombPacket

theorem test_combination_energy {m : ℕ} (χ : Fin m → Position → ℝ)
    (hχ : ∀ i, ContDiff ℝ ∞ (χ i)) (hc : ∀ i, HasCompactSupport (χ i))
    (hd : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {K : ℝ} (henergy : ∀ i, (∫ x, Coulomb.testCharge (χ i) x * χ i x) ≤ K)
    (d : Fin m → ℝ) :
    pair (combination (fun i => test (χ i) (hχ i) (hc i)) d)
      (combination (fun i => test (χ i) (hχ i) (hc i)) d) ≤ K * ∑ i, d i ^ 2 := by
  classical
  rw [pair_combinations]
  have hentry (i j : Fin m) : pair (test (χ i) (hχ i) (hc i)) (test (χ j) (hχ j) (hc j)) =
      if i = j then ∫ x, Coulomb.testCharge (χ i) x * χ i x else 0 := by
    by_cases hij : i = j
    · subst j
      simpa only [ite_true] using test_pair_test (χ i) (χ i) (hχ i) (hχ i) (hc i) (hc i)
    · rw [ite_eq_right hij]
      exact test_pair_orthogonal (χ i) (χ j) (hχ i) (hχ j) (hc i) (hc j) (hd i j hij)
  simp_rw [hentry]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  calc
    _ ≤ ∑ i, d i ^ 2 * K := Finset.sum_le_sum (fun i _ => by
      simpa only [pow_two] using mul_le_mul_of_nonneg_left (henergy i) (sq_nonneg (d i)))
    _ = _ := by rw [← Finset.sum_mul]; exact mul_comm _ _

theorem gram_coercive_of_dual_lower {m : ℕ} (f : Fin m → CoulombPacket)
    (χ : Fin m → Position → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hc : ∀ i, HasCompactSupport (χ i))
    (hd : ∀ i j, i ≠ j → Disjoint (tsupport (χ i)) (tsupport (χ j)))
    {K a : ℝ} (hK : 0 < K) (ha : 0 ≤ a)
    (henergy : ∀ i, (∫ x, Coulomb.testCharge (χ i) x * χ i x) ≤ K)
    (hdual : ∀ d : Fin m → ℝ, a * ∑ i, d i ^ 2 ≤
      ∑ i, ∑ j, d i * d j * ∫ x, f i x * χ j x)
    (d : Fin m → ℝ) :
    (a ^ 2 / K) * ∑ i, d i ^ 2 ≤ ∑ i, ∑ j, pair (f i) (f j) * d i * d j := by
  let ρ := combination f d
  let η := combination (fun i => test (χ i) (hχ i) (hc i)) d
  let S := ∑ i, d i ^ 2
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => sq_nonneg (d i))
  have hpair : a * S ≤ pair ρ η := by
    rw [pair_combinations]
    simp_rw [pair_test]
    exact hdual d
  have hpair0 : 0 ≤ pair ρ η := (mul_nonneg ha hS).trans hpair
  have hsquare : (a * S) ^ 2 ≤ pair ρ η ^ 2 :=
    (sq_le_sq₀ (mul_nonneg ha hS) hpair0).mpr hpair
  have htest := test_combination_energy χ hχ hc hd henergy d
  have hQ : 0 ≤ pair ρ ρ := pair_nonnegative ρ
  have hbound : (a * S) ^ 2 ≤ pair ρ ρ * (K * S) :=
    hsquare.trans ((pair_cauchy ρ η).trans (mul_le_mul_of_nonneg_left htest hQ))
  have hcoercive : (a ^ 2 / K) * S ≤ pair ρ ρ := by
    by_cases hz : S = 0
    · simpa only [hz, mul_zero] using hQ
    · have hSpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hz)
      have hcancel := (mul_le_mul_iff_left₀ hSpos).mp
        (show (a ^ 2 * S) * S ≤ (pair ρ ρ * K) * S by nlinarith only [hbound])
      rw [div_mul_eq_mul_div]
      exact (div_le_iff₀ hK).mpr hcancel
  change (a ^ 2 / K) * S ≤ pair (combination f d) (combination f d) at hcoercive
  rw [pair_combinations] at hcoercive
  convert hcoercive using 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

end ContinuumCoulomb.CoulombPacket

end

end OAI
