import OAI.Probability.InvariantIsing.Cavity.RepeatedBlockRemainderSpin
import Mathlib.Analysis.SpecificLimits.Basic

namespace OAI

/-! The bounded remainder error vanishes when the number of regular
blocks grows. -/

noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron Filter
open scoped Topology BigOperators BoundedContinuousFunction

namespace InvariantIsing

lemma bounded_block_remainder_fraction_tendsto {n rMax : ℕ} (hn : 0 < n)
    (K r : ℕ → ℕ) (hK : ∀ a, 0 < K a) (hlim : Tendsto K atTop atTop)
    (hr : ∀ a, r a ≤ rMax) :
    Tendsto (fun a => 2 * (r a : ℝ) / ((n : ℝ)*K a+r a)) atTop (𝓝 0) := by
  have hb (a : ℕ) : 2 * (r a : ℝ) / ((n : ℝ)*K a+r a) ≤ 2 * (rMax : ℝ) / K a := by
    have hk : (0:ℝ) < K a := Nat.cast_pos.mpr (hK a)
    have hd : (0:ℝ) < (n:ℝ)*K a+r a := by positivity
    have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hr' : (r a:ℝ) ≤ rMax := Nat.cast_le.mpr (hr a)
    apply (div_le_div_iff₀ hd hk).mpr
    have hden : (K a:ℝ) ≤ (n:ℝ)*K a+r a := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left hden (show (0:ℝ) ≤ 2*rMax by positivity)]
  have ht : Tendsto (fun a => 2*(rMax:ℝ)/(K a:ℝ)) atTop (𝓝 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (2*(rMax:ℝ))).comp hlim
  exact squeeze_zero (fun a => by positivity) hb ht

theorem repeated_block_remainder_spin_tendsto {n m depth rMax : ℕ} (hn : 0 < n)
    (K r : ℕ → ℕ) (hK : ∀ a, 3 ≤ K a) (hlim : Tendsto K atTop atTop)
    (hr : ∀ a, r a ≤ rMax) (C : Finset (Spin n)) (hC : C.Nonempty)
    (R : (a : ℕ) → Finset (Spin (r a))) (hR : ∀ a, (R a).Nonempty)
    (μ : (a : ℕ) → Measure (SpecialOrthogonal (n*K a+r a)))
    [∀ a, IsProbabilityMeasure (μ a)] [∀ a, (μ a).IsMulRightInvariant]
    (T : ℕ → LabeledTree depth) (eig : (a : ℕ) → Fin (n*K a+r a) → ℝ)
    (I : (a : ℕ) → Fin m → Finset (Fin (n*K a+r a)))
    (u : ℕ → ℕ → ℝ) (hu : ∀ a k, |u a k| ≤ 2)
    (b₀ : (a : ℕ) → Fin (K a)) (Φ : ℝ →ᵇ ℝ) :
    Tendsto (fun a =>
      restrictedCavityFullDisorderTest (cavityProductSlice (spinBlockConstraint n (K a) C) (R a))
        (cavityProductSlice_nonempty _ (spinBlockConstraint_nonempty C hC) (R a) (hR a))
        (μ a) (T a) (eig a) (I a) (u a) (fun _ σ => Φ (cavityReplicaOverlap σ) *
          ((n:ℝ)⁻¹ * ∑ i : Fin n,
            spinValue ((σ 0).1 (Fin.castAdd (r a) (finProdFinEquiv (i,b₀ a)))) *
            spinValue ((σ 1).1 (Fin.castAdd (r a) (finProdFinEquiv (i,b₀ a)))))) -
      restrictedCavityFullDisorderTest (cavityProductSlice (spinBlockConstraint n (K a) C) (R a))
        (cavityProductSlice_nonempty _ (spinBlockConstraint_nonempty C hC) (R a) (hR a))
        (μ a) (T a) (eig a) (I a) (u a) (fun _ σ => Φ (cavityReplicaOverlap σ) * cavityReplicaOverlap σ))
      atTop (𝓝 0) := by
  have hb := (bounded_block_remainder_fraction_tendsto hn K r (fun a => by have := hK a; omega) hlim hr).const_mul ‖Φ‖
  simp only [mul_zero] at hb
  apply squeeze_zero_norm (fun a => ?_) hb
  simpa only [Real.norm_eq_abs] using
    repeated_block_remainder_spin_error hn (hK a) C hC (R a) (hR a)
      (μ a) (T a) (eig a) (I a) (u a) (hu a) Φ (b₀ a)

end InvariantIsing

end

end OAI
