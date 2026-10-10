import OAI.NumberTheory.Ostmann.Preliminaries.PrimeSums
import OAI.NumberTheory.Ostmann.QuadraticCenter.RootCollisionUpper

namespace OAI

open Erdos970

noncomputable section
namespace Ostmann.QuadraticCenter
open Filter
open scoped BigOperators

theorem rootCollision_mertens_floor_lower (X η : ℝ) (hX : 1 < X)
    (hη : η ≤ 1/1000) :
    (1/2-5*η)*Real.log X - Real.log 2 - (Real.log 4+4) ≤
      ∑ p ∈ (⌊X^(1/2-5*η)⌋₊:ℕ).primesLE, Real.log (p:ℝ)/p := by
  have hXp : 0 < X := by linarith
  have ha : 0 ≤ 1/2-5*η := by linarith
  have hr : 1 ≤ X^(1/2-5*η) := Real.one_le_rpow hX.le ha
  have hQ : 1 ≤ ⌊X^(1/2-5*η)⌋₊ := (Nat.one_le_floor_iff _).2 hr
  have hhalf : X^(1/2-5*η)/2 ≤ ((⌊X^(1/2-5*η)⌋₊:ℕ):ℝ) :=
    (Nat.div_two_lt_floor hr).le
  have hlog := Real.log_le_log (by positivity : 0 < X^(1/2-5*η)/2) hhalf
  rw [Real.log_div (by positivity) (by norm_num), Real.log_rpow hXp] at hlog
  exact (sub_le_sub_right hlog _).trans
    (Preliminaries.mertens_prime_sum_lower _ hQ)

theorem rootCollision_numerical_gap (C : ℝ) :
    ∀ᶠ X : ℝ in atTop, ∀ η : ℝ, 0 ≤ η → η ≤ 1/1000 →
      (1+2*η)*Real.log X+C <
        2*(∑ p ∈ (⌊X^(1/2-5*η)⌋₊:ℕ).primesLE, Real.log (p:ℝ)/p) +
          2*((3/100:ℝ)*Real.log X) := by
  have hlog := Real.tendsto_log_atTop.eventually
    (eventually_gt_atTop (25*(C+2*Real.log 2+2*(Real.log 4+4))))
  filter_upwards [hlog,eventually_gt_atTop 1] with X hlarge hX
  intro η hη0 hη1
  have hL : 0 < Real.log X := Real.log_pos hX
  have hηL := mul_le_mul_of_nonneg_right hη1 hL.le
  have hm := rootCollision_mertens_floor_lower X η hX hη1
  nlinarith only [hlarge,hL,hηL,hm]

theorem rootCollision_eventually_impossible :
    ∀ᶠ X : ℝ in atTop, ∀ (η : ℝ) (U V : Finset ℕ),
      0 ≤ η → η ≤ 1/1000 → U.Nonempty → V.Nonempty →
      X^(1/2-3*η) ≤ (U.card:ℝ) → X^(1/2-3*η) ≤ (V.card:ℝ) →
      (∀ a ∈ U, ∀ b ∈ U, |(a:ℝ)-b| ≤ X^(1/2+η)) →
      (∀ a ∈ V, ∀ b ∈ V, |(a:ℝ)-b| ≤ X^(1/2+η)) →
      2*(∑ p ∈ (⌊X^(1/2-5*η)⌋₊:ℕ).primesLE, Real.log (p:ℝ)/p) +
          2*((3/100:ℝ)*Real.log X) ≤
        (∑ p ∈ (⌊X^(1/2-5*η)⌋₊:ℕ).primesLE,
          Real.log p * (rootCollisionProbability U p+rootCollisionProbability V p)) → False := by
  filter_upwards [rootCollision_numerical_gap (2*Real.log 2+2*Real.log 4),
    eventually_gt_atTop 1] with X hgap hX
  intro η U V hη0 hη1 hU hV hUc hVc hUd hVd hlo
  have hup := rootCollisionProbability_pair_weighted_le_scale X η hX hη0
    U V hU hV hUc hVc hUd hVd
  exact (not_lt_of_ge (hlo.trans hup)) (hgap η hη0 hη1)

end Ostmann.QuadraticCenter

end

end OAI
