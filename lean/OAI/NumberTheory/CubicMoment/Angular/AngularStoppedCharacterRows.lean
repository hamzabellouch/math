import OAI.NumberTheory.CubicMoment.Decomposition.StoppedDivisorExclusion
import OAI.NumberTheory.CubicMoment.Estimates.MellinHeightKernel

namespace OAI

/-! The fixed-angular stopped coefficient and its exact character row.
Angular multiplication preserves the proved pointwise and energy bounds;
cube factors and divisor exclusions remain literal finite identities. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def angularStoppedRowCoefficient (ℓ : ℤ) (X w z u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (n : Eisenstein) : ℂ :=
  stoppedRowCoefficient X w z u W selected n * theta ℓ n

def angularStoppedCharacterSum (ℓ : ℤ) (X w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (v e : Eisenstein) : ℂ :=
  ∑ n ∈ stoppedIntervalSupport ι X a b e,
    angularStoppedRowCoefficient ℓ X w z u W selected n * cubicSymbol n v

lemma angularStoppedRowCoefficient_norm (ℓ : ℤ) (X w z u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) {n : Eisenstein} (hn : primary n) :
    ‖angularStoppedRowCoefficient ℓ X w z u W selected n‖ =
      ‖stoppedRowCoefficient X w z u W selected n‖ := by
  rw [angularStoppedRowCoefficient,norm_mul,norm_theta (primary_ne_zero hn),mul_one]

lemma angularStoppedCharacterSum_cube (ℓ : ℤ) (X w z a b u : ℝ) (W : ι → ℝ → ℂ)
    (selected : Eisenstein → Eisenstein → Prop) (v j e : Eisenstein) :
    angularStoppedCharacterSum ℓ X w z a b u W selected (v*j^3) e =
      angularStoppedCharacterSum ℓ X w z a b u W selected v (e*j) := by
  unfold angularStoppedCharacterSum stoppedIntervalSupport
  rw [Finset.sum_filter,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hnp : primary n := primaryPairSupport_primary _ _
    (fun r hr => orderedPrimarySupport_primary _
      (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr)
    (fun d hd => (mem_primaryElementBall.mp hd).1) hn
  have hcop : IsCoprime n (e*j) ↔ IsCoprime n e ∧ IsCoprime n j :=
    ⟨fun h => ⟨h.of_mul_right_left,h.of_mul_right_right⟩,fun h => h.1.mul_right h.2⟩
  rw [cubicSymbol_mul_upper hnp,cubicSymbol_cube_indicator hnp j]
  by_cases he : IsCoprime n e <;> by_cases hj : IsCoprime n j <;>
    simp [hcop,he,hj]

lemma angularStoppedCharacterSum_divisibility (ℓ : ℤ) (X w z a b u : ℝ)
    (W : ι → ℝ → ℂ) (selected : Eisenstein → Eisenstein → Prop) (v e : Eisenstein)
    (U : Finset Eisenstein) (hU : ∀ p ∈ U, primaryPrime p) :
    (∑ n ∈ (stoppedIntervalSupport ι X a b e).filter
        (fun n => (∏ p ∈ U,p) ∣ n),
      angularStoppedRowCoefficient ℓ X w z u W selected n*cubicSymbol n v) =
      ∑ s ∈ U.powerset, (-1:ℂ)^s.card*
        angularStoppedCharacterSum ℓ X w z a b u W selected v (e*(∏ p ∈ s,p)) := by
  rw [prime_product_filtered_sum _ U hU]
  apply Finset.sum_congr rfl
  intro s _
  rw [stoppedIntervalSupport_filter_coprime]
  rfl

theorem angular_stopped_interval_energy (ℓ : ℤ) {ξ : ℝ}
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) :
    ∃ M : ℝ, 0 < M ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (W : ι → ℝ → ℂ), (∀ i x, ‖W i x‖ ≤ 1) →
      ∀ (selected : Eisenstein → Eisenstein → Prop) (u a b : ℝ) (e : Eisenstein),
      0 ≤ b → b ≤ X →
      (∀ n ∈ stoppedIntervalSupport ι X a b e,
        ‖angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected n‖ ≤ M) ∧
      (∑ n ∈ stoppedIntervalSupport ι X a b e,
        ‖angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected n‖^2) ≤
          18*b*M^2 := by
  obtain ⟨M,hM,he⟩ := stopped_interval_energy (ι := ι) hξ hξz
  refine ⟨M,hM,?_⟩
  filter_upwards [he] with X he
  intro W hW selected u a b e hb hbX
  have hnorm (n : Eisenstein) (hn : n ∈ stoppedIntervalSupport ι X a b e) :=
    angularStoppedRowCoefficient_norm ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected
      (stoppedIntervalSupport_spec X a b e hn).1
  constructor
  · intro n hn
    rw [hnorm n hn]
    exact (he W hW selected u a b e hb hbX).1 n hn
  · have hsum : (∑ n ∈ stoppedIntervalSupport ι X a b e,
          ‖angularStoppedRowCoefficient ℓ X (X^ξ) (X^(2/5:ℝ)) u W selected n‖^2) =
        ∑ n ∈ stoppedIntervalSupport ι X a b e,
          ‖stoppedRowCoefficient X (X^ξ) (X^(2/5:ℝ)) u W selected n‖^2 :=
      Finset.sum_congr rfl (fun n hn => by rw [hnorm n hn])
    rw [hsum]
    exact (he W hW selected u a b e hb hbX).2

end CubicFirstMoment

end

end OAI
