import OAI.Combinatorics.Progressions.Dynamics.VectorSiteBudget

namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal Classical

theorem scalarPair_site_expansion (D : ℝ × ℝ → ℝ) (K : ℝ≥0)
    (hD : ∀ z, D z ∈ Set.Icc (0 : ℝ) (K * K))
    (hLip : LipschitzWith (K * (K * (2 * K)) + K * (K * (2 * K))) D)
    {q R ε : ℝ} (hq : 0 ≤ q) (hK : (K : ℝ) ≤ Real.exp q)
    (hR : 0 < R) (hRq : R ≤ Real.exp q) (hε : 0 < ε) (hεq : ε⁻¹ ≤ Real.exp q) :
    let P := 3 * q + 4
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * P + 8) ∧
      ∃ (c : (Bool × Unit → Fin n) → ℂ)
        (f : (Bool × Unit → Fin n) → Bool → (Unit → ℝ) → ℂ),
        (∑ k, ‖c k‖) ≤ Real.exp (2 * (4 * P + 8) + P) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (1 + 6 * P + 12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : Bool → Unit → ℝ, (∀ s d, |x s d| ≤ R) →
          ‖(D (x false (), x true ()) : ℂ) - ∑ k, c k * ∏ s, f k s (x s)‖ ≤ ε := by
  let P := 3 * q + 4
  have hP : 0 ≤ P := by dsimp [P]; linarith
  have hqP : q ≤ P := by dsimp [P]; linarith
  have hcap : ((K * K : ℝ≥0) : ℝ) ≤ Real.exp P := by
    change (K : ℝ) * K ≤ Real.exp P
    calc
      _ ≤ Real.exp q * Real.exp q := mul_le_mul hK hK K.coe_nonneg (Real.exp_pos _).le
      _ = Real.exp (q + q) := (Real.exp_add _ _).symm
      _ ≤ Real.exp P := Real.exp_le_exp.mpr (by dsimp [P]; linarith)
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hLipCap : ((K * (K * (2 * K)) + K * (K * (2 * K)) : ℝ≥0) : ℝ) ≤ Real.exp P := by
    push_cast
    calc
      _ = 4 * (K : ℝ) ^ 3 := by ring
      _ ≤ Real.exp 4 * (Real.exp q) ^ 3 :=
        mul_le_mul hfour (pow_le_pow_left₀ K.coe_nonneg hK 3)
          (pow_nonneg K.coe_nonneg _) (Real.exp_pos _).le
      _ = Real.exp P := by rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; dsimp [P]; ring
  have he : LipschitzWith 1
      (fun x : Bool → Unit → ℝ => (x false (), x true ())) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simp only [NNReal.coe_one, one_mul, Prod.dist_eq]
    exact max_le ((dist_le_pi_dist _ _ ()).trans (dist_le_pi_dist x y false))
      ((dist_le_pi_dist _ _ ()).trans (dist_le_pi_dist x y true))
  let F : (Bool → Unit → ℝ) → ℂ := fun x => D (x false (), x true ())
  have hFLip : LipschitzWith (K * (K * (2 * K)) + K * (K * (2 * K))) F := by
    simpa only [mul_one, one_mul, Function.comp_def] using
      Complex.isometry_ofReal.lipschitzWith.comp (hLip.comp he)
  have hFA (x) : ‖F x‖ ≤ (K * K : ℝ≥0) := by
    simpa only [F, Complex.norm_real, Real.norm_of_nonneg (hD _).1, NNReal.coe_mul] using
      (hD _).2
  obtain ⟨n, hn, c, f, hc, hf, hLf, herr⟩ :=
    exists_grouped_site_approximation F (K * K) (K * (K * (2 * K)) + K * (K * (2 * K)))
      hFA hFLip hR hε hP (hRq.trans (Real.exp_le_exp.mpr hqP)) hcap hLipCap
      (hεq.trans (Real.exp_le_exp.mpr hqP))
  exact ⟨n, hn, c, f, by simpa using hc, hf, by simpa using hLf, herr⟩

end Erdos3

namespace Erdos3.SlicedProductBlock

open MeasureTheory
open scoped BigOperators NNReal Classical

theorem averagedTwoSiteDensity_site_expansion
    {ι P : Type*} [Fintype ι] [MeasurableSpace P]
    (μ : Measure P) [IsProbabilityMeasure μ] (B : P → Fin 4 → SlicedProductBlock ι)
    (hBm : ∀ j, MeasurableFamily (fun p => B p j))
    (hB : ∀ p j, (B p j).Admissible) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hcoeff : ∀ p j, c ≤ |(B p j).coefficient|)
    (hlast : ∀ p j, δ ≤ (B p j).lastWidth) (hwidth : ∀ p j i, δ ≤ (B p j).width i)
    {q R ε : ℝ} (hq : 0 ≤ q)
    (hK : (uniformCap ι (c * δ ^ (Fintype.card ι + 1)) (mul_pos hc (pow_pos hδ _)) : ℝ) ≤ Real.exp q)
    (hR : 0 < R) (hRq : R ≤ Real.exp q) (hε : 0 < ε) (hεq : ε⁻¹ ≤ Real.exp q) :
    let Q := 3 * q + 4
    ∃ n : ℕ, (n : ℝ) ≤ Real.exp (4 * Q + 8) ∧
      ∃ (a : (Bool × Unit → Fin n) → ℂ)
        (f : (Bool × Unit → Fin n) → Bool → (Unit → ℝ) → ℂ),
        (∑ k, ‖a k‖) ≤ Real.exp (2 * (4 * Q + 8) + Q) ∧
        (∀ k s x, ‖f k s x‖ ≤ 1) ∧
        (∀ k s, LipschitzWith ⟨Real.exp (1 + 6 * Q + 12), Real.exp_nonneg _⟩ (f k s)) ∧
        ∀ x : Bool → Unit → ℝ, (∀ s d, |x s d| ≤ R) →
          ‖(densityMixture μ (fun p => twoSiteDensity (B p)) (x false (), x true ()) : ℂ) -
            ∑ k, a k * ∏ s, f k s (x s)‖ ≤ ε := by
  have h := averagedTwoSiteDensity_uniform_bound μ B hBm hB hc hδ hcoeff hlast hwidth
  exact scalarPair_site_expansion _ _ h.1 h.2 hq hK hR hRq hε hεq

end Erdos3.SlicedProductBlock

end

end OAI
