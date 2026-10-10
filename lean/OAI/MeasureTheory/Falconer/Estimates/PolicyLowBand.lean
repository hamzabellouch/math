import OAI.MeasureTheory.Falconer.Estimates.MaskedLowBand

namespace OAI

/-! # Positive low-prefix transition for the actual policy list -/

namespace Falconer
open Set MeasureTheory

noncomputable def policyMaskedDistance {d : ℕ} (w₀ : Sphere d) (Q : DyadicCube d)
    (ρ : Measure (Space d)) (m : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ)
    (σ : ℝ) (J i q a t : ℕ)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d)) (X Y : DyadicCube d) : Measure ℝ :=
  maskedCellDistance w₀ Q ρ m N σ J i a
    (PlanarFalconer.policyDescriptorList A N q a t) S X Y

 theorem policy_masked_distance_low_band {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d)) [IsFiniteMeasure ρ]
    (m : ℝ → ℝ) (A : ℕ → ℝ) (N : ℕ) (σ : ℝ) (J i q a t v : ℕ)
    (hav : a ≤ v) (hvt : v ≤ t)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ PlanarFalconer.policyDescriptorList A N q a t, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) (X Y : List (Fin d → Bool))
    (hsep : ∀ᵐ z ∂(ρ.restrict (Q.descendant X).carrier).prod (ρ.restrict (Q.descendant Y).carrier),
      1 ≤ dist z.1 z.2*(2:ℝ)^a)
    [IsFiniteMeasure (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
      (Q.descendant X) (Q.descendant Y))] :
    (1/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^v) ((2:ℝ)^v),
      ‖charFun (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
        (Q.descendant X) (Q.descendant Y)) r‖^2 ≤
      (32*PlanarFalconer.binKernelConstant.toReal) *
        (positiveCollisionCount w₀ Q ρ (fun u => m (u/N)) A N σ J (i+1) q a v X Y).toReal := by
  let : IsFiniteMeasure (maskedCellDistance w₀ Q ρ m N σ J i a
      (PlanarFalconer.policyDescriptorList A N q a t) S (Q.descendant X) (Q.descendant Y)) := by
    change IsFiniteMeasure (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
      (Q.descendant X) (Q.descendant Y))
    infer_instance
  have h := masked_distance_low_band w₀ Q ρ m N σ J i a v hav
    (PlanarFalconer.policyDescriptorList A N q a t)
    (PlanarFalconer.policyDescriptorList A N q a v)
    (PlanarFalconer.policyDescriptorList_mono A (N := N) (q := q) le_rfl hvt)
    S hcover hd (Q.descendant X) (Q.descendant Y) hsep
  simp only [policyMaskedDistance,positiveCollisionCount,policyTestPairs,ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (show 0 ≤ (2:ℝ)^(v-a)*((2:ℝ)^N)^(4*m ((a:ℝ)/N)) by positivity)]
  simpa only [measureReal_def,mul_assoc,mul_left_comm,mul_comm] using h

theorem policy_masked_distance_low_frequency {d : ℕ}
    (w₀ : Sphere d) (Q : DyadicCube d) (ρ : Measure (Space d))
    {m : ℝ → ℝ} {N : ℕ} {s lam : ℝ}
    (hreg : Regularization.RegularizedProfileData Q ρ N s lam m)
    (A : ℕ → ℝ) (σ : ℝ) (J i q a t : ℕ) (ha : a ≤ N) (hat : a ≤ t)
    (S : PlanarFalconer.PolicyDescriptor → Finset (Sphere d))
    (hcover : ∀ b ∈ PlanarFalconer.policyDescriptorList A N q a t, ∀ w : Sphere d,
      ∃ c ∈ S b, dist w c ≤ descriptorMaskRadius N σ b/2)
    (hd : 1 ≤ d) (X Y : List (Fin d → Bool)) (hX : X.length = a) (hY : Y.length = a)
    (hsep : ∀ᵐ z ∂(ρ.restrict (Q.descendant X).carrier).prod (ρ.restrict (Q.descendant Y).carrier),
      1 ≤ dist z.1 z.2*(2:ℝ)^a)
    [IsFiniteMeasure (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
      (Q.descendant X) (Q.descendant Y))] :
    (1/(2:ℝ)^a) * ∫ r in Icc (-(2:ℝ)^a) ((2:ℝ)^a),
      ‖charFun (policyMaskedDistance w₀ Q ρ m A N σ J i q a t S
        (Q.descendant X) (Q.descendant Y)) r‖^2 ≤
      (32*PlanarFalconer.binKernelConstant.toReal) *
        ((2:ℝ)^N)^(4*((d:ℝ)+1)*lam) := by
  let := hreg.probability
  have h := policy_masked_distance_low_band w₀ Q ρ m A N σ J i q a t a le_rfl hat
    S hcover hd X Y hsep
  have hb := positiveCollisionCount_regularized w₀ Q ρ hreg A σ J (i+1) q (t := a) ha X Y hX hY
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top hb
  simp only [Nat.sub_self,pow_zero,one_mul,ENNReal.toReal_ofReal (by positivity :
    0 ≤ ((2:ℝ)^N)^(4*((d:ℝ)+1)*lam))] at hr
  exact h.trans (mul_le_mul_of_nonneg_left hr (by positivity))

end Falconer

end OAI
