import Mathlib
import OAI.Analysis.RieszRectifiability.Limits.SignedKernelConvergence
import OAI.Analysis.RieszRectifiability.Limits.CappedEnergyContinuity

namespace OAI

/-!
# Weak convergence of capped pair energies

Bounded continuous tests pass to weak limits of finite measures. Finite measurable
partitions with shrinking cells then control bounded Lipschitz tests on product
measures. The capped pair energy of a bounded Lipschitz function satisfies these
test bounds, giving convergence of its double integral at each positive cap.
-/

namespace RieszRectifiability

noncomputable section

open MeasureTheory Set Function Filter Topology
open scoped NNReal BoundedContinuousFunction

theorem bounded_continuous_integral_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν)) (f : Ambient d → ℝ) (hf : Continuous f)
    (B : ℝ) (hB : ∀ x, |f x| ≤ B) :
    Tendsto (fun j => ∫ x, f x ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, f x ∂(ν : Measure (Ambient d)))) := by
  let F : Ambient d →ᵇ ℝ := BoundedContinuousFunction.mkOfBound ⟨f, hf⟩ (2 * B) (by
    intro x y
    change dist (f x) (f y) ≤ 2 * B
    rw [Real.dist_eq]
    have h := abs_sub_le (f x) 0 (f y)
    simp only [sub_zero, zero_sub, abs_neg] at h
    linarith [hB x, hB y])
  exact FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hweak F

theorem bounded_lipschitz_product_integral_tendsto {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set (Ambient d))
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ y ∂(μ j : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (hcoverν : ∀ k, ∀ᵐ y ∂(ν : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (z : ∀ k, ι k → Ambient d) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0))
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ y ∂(μ j : Measure (Ambient d)).restrict (s k i),
      dist y (z k i) ≤ r k)
    (hcellν : ∀ k i, ∀ᵐ y ∂(ν : Measure (Ambient d)).restrict (s k i), dist y (z k i) ≤ r k)
    (hmass : ∀ k i, Tendsto (fun j => (μ j : Measure (Ambient d)).real (s k i)) atTop
      (𝓝 ((ν : Measure (Ambient d)).real (s k i))))
    (M : ℝ) (hM : 0 ≤ M) (htotal : ∀ᶠ j in atTop, (μ j : Measure (Ambient d)).real univ ≤ M)
    (F : Ambient d × Ambient d → ℝ) (K : ℝ≥0) (hF : LipschitzWith K F)
    (B : ℝ) (hB : ∀ q, |F q| ≤ B) :
    Tendsto (fun j => ∫ q, F q ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ q, F q ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))) := by
  have hweight : ∀ᶠ j in atTop, (∫ _ : Ambient d, |(1 : ℝ)| ∂(μ j : Measure (Ambient d))) ≤ M := by
    simpa only [abs_one, integral_const, smul_eq_mul, mul_one] using! htotal
  have hmoment : ∀ y, Tendsto (fun j => ∫ x, (1 : ℝ) * F (x, y) ∂(μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ x, (1 : ℝ) * F (x, y) ∂(ν : Measure (Ambient d)))) := by
    intro y
    simpa only [one_mul] using! bounded_continuous_integral_tendsto μ ν hweak
      (fun x => F (x, y)) (hF.continuous.comp (continuous_id.prodMk continuous_const)) B
      (fun x => hB (x, y))
  have h := weighted_product_kernel_tendsto (fun j => (μ j : Measure (Ambient d)))
    (ν : Measure (Ambient d)) (fun j => (μ j : Measure (Ambient d))) (ν : Measure (Ambient d))
    (fun _ _ => 1) (fun _ => 1) (fun _ => integrable_const 1) (integrable_const 1)
    ι s hs hd hcover hcoverν z r hr hrzero hcell hcellν hmass M M hM hM hweight htotal
    F K hF B hB hmoment
  simpa only [one_mul] using! h

theorem cappedPairEnergy_bounded_lipschitz {d : ℕ} (m : ℕ) (ε : ℝ) (hε : 0 < ε)
    (g : Ambient d → ℝ) (L B : ℝ≥0) (hg : LipschitzWith L g) (hB : ∀ x, |g x| ≤ (B : ℝ)) :
    ∃ (K : ℝ≥0) (Q : ℝ), LipschitzWith K (cappedPairEnergy m ε g) ∧
      ∀ q, |cappedPairEnergy m ε g q| ≤ Q := by
  let δg := fun q : Ambient d × Ambient d => g q.1 - g q.2
  have hdiff : LipschitzWith (L + L) δg := by
    simpa only [mul_one] using! (hg.comp LipschitzWith.prod_fst).sub (hg.comp LipschitzWith.prod_snd)
  have hdiffbound : ∀ q, |δg q| ≤ ((2 * B : ℝ≥0) : ℝ) := by
    intro q
    have h := abs_sub_le (g q.1) 0 (g q.2)
    simp only [sub_zero, zero_sub, abs_neg] at h
    simp only [δg, NNReal.coe_mul, NNReal.coe_ofNat]
    linarith [hB q.1, hB q.2]
  have hsquare : LipschitzWith ((2 * B) * (L + L) + (L + L) * (2 * B))
      (fun q => δg q ^ 2) := by
    simpa only [pow_two] using! lipschitz_bounded_product_real hdiff hdiff hdiffbound hdiffbound
  have hsquarebound : ∀ q, |δg q ^ 2| ≤ (((2 * B : ℝ≥0) ^ 2) : ℝ) := by
    intro q
    rw [abs_of_nonneg (sq_nonneg _)]
    simpa only [sq_abs] using! pow_le_pow_left₀ (abs_nonneg _) (hdiffbound q) 2
  have hcap := cappedInverseDistancePow_lipschitz (X := Ambient d) m ε hε
  have hcapbound : ∀ q : Ambient d × Ambient d, |cappedInverseDistancePow (m + 1) ε q| ≤
      (Real.toNNReal ((ε ^ (m + 1))⁻¹) : ℝ) := fun q =>
    (cappedInverseDistancePow_bound (m + 1) ε hε q).trans (Real.le_coe_toNNReal _)
  refine ⟨_, (((2 * B : ℝ≥0) ^ 2) : ℝ) * (ε ^ (m + 1))⁻¹,
    lipschitz_bounded_product_real (Bf := (2 * B) ^ 2)
      (Bg := Real.toNNReal ((ε ^ (m + 1))⁻¹)) hsquare hcap
      (fun q => by simpa only [NNReal.coe_pow] using! hsquarebound q) hcapbound, ?_⟩
  intro q
  change |δg q ^ 2 * cappedInverseDistancePow (m + 1) ε q| ≤ _
  rw [abs_mul]
  exact mul_le_mul (hsquarebound q) (cappedInverseDistancePow_bound (m + 1) ε hε q)
    (abs_nonneg _) (by positivity)

theorem capped_energy_tendsto_of_weak {d : ℕ}
    (μ : ℕ → FiniteMeasure (Ambient d)) (ν : FiniteMeasure (Ambient d))
    (hweak : Tendsto μ atTop (𝓝 ν))
    (ι : ℕ → Type*) [∀ k, Fintype (ι k)] (s : ∀ k, ι k → Set (Ambient d))
    (hs : ∀ k i, MeasurableSet (s k i)) (hd : ∀ k, Pairwise (Disjoint on s k))
    (hcover : ∀ k j, ∀ᵐ y ∂(μ j : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (hcoverν : ∀ k, ∀ᵐ y ∂(ν : Measure (Ambient d)), y ∈ ⋃ i, s k i)
    (z : ∀ k, ι k → Ambient d) (r : ℕ → ℝ) (hr : ∀ k, 0 ≤ r k)
    (hrzero : Tendsto r atTop (𝓝 0))
    (hcell : ∀ k, ∀ᶠ j in atTop, ∀ i, ∀ᵐ y ∂(μ j : Measure (Ambient d)).restrict (s k i),
      dist y (z k i) ≤ r k)
    (hcellν : ∀ k i, ∀ᵐ y ∂(ν : Measure (Ambient d)).restrict (s k i), dist y (z k i) ≤ r k)
    (hmass : ∀ k i, Tendsto (fun j => (μ j : Measure (Ambient d)).real (s k i)) atTop
      (𝓝 ((ν : Measure (Ambient d)).real (s k i))))
    (M : ℝ) (hM : 0 ≤ M) (htotal : ∀ᶠ j in atTop, (μ j : Measure (Ambient d)).real univ ≤ M)
    (m : ℕ) (ε : ℝ) (hε : 0 < ε) (g : Ambient d → ℝ) (L B : ℝ≥0)
    (hg : LipschitzWith L g) (hB : ∀ x, |g x| ≤ (B : ℝ)) :
    Tendsto (fun j => ∫ q, cappedPairEnergy m ε g q
      ∂(μ j : Measure (Ambient d)).prod (μ j : Measure (Ambient d))) atTop
      (𝓝 (∫ q, cappedPairEnergy m ε g q ∂(ν : Measure (Ambient d)).prod (ν : Measure (Ambient d)))) := by
  obtain ⟨K, Q, hLip, hbound⟩ := cappedPairEnergy_bounded_lipschitz m ε hε g L B hg hB
  exact bounded_lipschitz_product_integral_tendsto μ ν hweak ι s hs hd hcover hcoverν z r hr hrzero
    hcell hcellν hmass M hM htotal (cappedPairEnergy m ε g) K hLip Q hbound

end

end RieszRectifiability

end OAI
