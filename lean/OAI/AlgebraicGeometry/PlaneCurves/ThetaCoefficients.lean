import OAI.AlgebraicGeometry.PlaneCurves.LaurentCoefficients
import OAI.AlgebraicGeometry.PlaneCurves.ThetaSections

namespace OAI

/-!
# Analytic theta coefficient extraction on circles
-/

section

namespace Nagata.W09

open Complex Metric
open Nagata.W07 Nagata.W22

noncomputable def thetaCircleMajorant (τ σ x₀ : ℝ) (n K : ℤ) (p : ℤ) : ℝ :=
  thetaDiskMajorant (n : ℝ) (K : ℝ) (2 * Real.pi)
    (Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))) 0 p

theorem thetaCircleMajorant_summable {τ : ℝ} (hτ : 0 < τ)
    (σ x₀ : ℝ) {n : ℤ} (hn : 0 ≤ n) (K : ℤ)
    (hhalf : Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) ≤ 1 / 2) :
    Summable (thetaCircleMajorant τ σ x₀ n K) := by
  exact summable_thetaDiskMajorant (by exact_mod_cast hn)
    (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hτ.le _)) hhalf _ _ _

theorem normalizedLaurentMonomial_circle_bound {τ : ℝ} (hτ : 0 < τ) (hτone : τ ≤ 1)
    (σ x₀ : ℝ) {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n)
    (K p : ℤ) {z : ℂ} (hz : z ∈ sphere 0 (τ ^ x₀)) :
    ‖normalizedLaurentCoefficient τ σ x₀ ε n K p * z ^ (K + n * p)‖ ≤
      thetaCircleMajorant τ σ x₀ n K p := by
  obtain ⟨θ, hθ, rfl⟩ := exists_circle_angle_of_mem_sphere (Real.rpow_pos_of_pos hτ _) hz
  have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 2 * Real.pi := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_pos hθ.1] using hθ.2
  have heval : circleMap 0 (τ ^ x₀) θ = ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp only [circleMap, zero_add]
  rw [heval, normalizedLaurentCoefficient_eval hτ]
  simpa only [thetaCircleMajorant, thetaDiskMajorant, pow_zero, mul_one] using
    norm_normalizedThetaTerm_le (by exact_mod_cast hn) hτ hτone hε
      (by positivity : 0 ≤ 2 * Real.pi) hx p

/-- The exact local theta-series identity and the checked fixed-disk majorant
supply a genuine monomial HasSum on the physical circle r=tau^x0. -/
theorem normalizedLaurentMonomial_hasSum_on_circle
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ ≤ 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n) (K : ℤ)
    (hhalf : Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) ≤ 1 / 2)
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x)
    {z : ℂ} (hz : z ∈ sphere 0 (τ ^ x₀)) :
    HasSum (fun p : ℤ => normalizedLaurentCoefficient τ σ x₀ ε n K p * z ^ (K + n * p)) (f z) := by
  obtain ⟨θ, hθ, rfl⟩ := exists_circle_angle_of_mem_sphere (Real.rpow_pos_of_pos hτ _) hz
  have hx : ‖(θ : ℂ) * Complex.I‖ ≤ 2 * Real.pi := by
    simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one,
      abs_of_pos hθ.1] using hθ.2
  have heval : circleMap 0 (τ ^ x₀) θ = ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp only [circleMap, zero_add]
  rw [heval, hlocal]
  simpa only [normalizedLaurentCoefficient_eval hτ, normalizedThetaSeries] using
    hasSum_normalizedThetaTerm_on_disk (by exact_mod_cast hn) hτ hτone hε
      (by positivity : 0 ≤ 2 * Real.pi) hhalf hx

/-- Under the exact local theta identity, actual contour extraction recovers
each explicit chosen Laurent coefficient; normal convergence is proved above. -/
theorem analyticLaurentCoeff_of_local_theta_series
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ ≤ 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 < n) (K : ℤ)
    (hhalf : Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) ≤ 1 / 2)
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (p : ℤ) :
    analyticLaurentCoeff (τ ^ x₀) f (K + n * p) = normalizedLaurentCoefficient τ σ x₀ ε n K p := by
  refine analyticLaurentCoeff_monomial_series_at (Real.rpow_pos_of_pos hτ _)
    (normalizedLaurentCoefficient τ σ x₀ ε n K) (fun p : ℤ => K + n * p)
    ?_ f (thetaCircleMajorant τ σ x₀ n K)
    (thetaCircleMajorant_summable hτ σ x₀ hn.le K hhalf) ?_ ?_ p
  · intro a b hab
    exact mul_left_cancel₀ hn.ne' (add_left_cancel hab)
  · intro i z hz
    exact normalizedLaurentMonomial_circle_bound hτ hτone σ x₀ hε hn.le K i hz
  · intro z hz
    exact normalizedLaurentMonomial_hasSum_on_circle hτ hτone σ x₀ hε hn.le K hhalf f hlocal hz

/-- The analytic coefficient vanishes outside the selected residue class. -/
theorem analyticLaurentCoeff_local_theta_off_residue
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ ≤ 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n) (K : ℤ)
    (hhalf : Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) ≤ 1 / 2)
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (k : ℤ) (hk : k % n ≠ K % n) :
    analyticLaurentCoeff (τ ^ x₀) f k = 0 := by
  refine analyticLaurentCoeff_monomial_series_eq_zero (Real.rpow_pos_of_pos hτ _)
    (normalizedLaurentCoefficient τ σ x₀ ε n K) (fun p : ℤ => K + n * p)
    f (thetaCircleMajorant τ σ x₀ n K)
    (thetaCircleMajorant_summable hτ σ x₀ hn K hhalf) ?_ ?_ k ?_
  · intro i z hz
    exact normalizedLaurentMonomial_circle_bound hτ hτone σ x₀ hε hn K i hz
  · intro z hz
    exact normalizedLaurentMonomial_hasSum_on_circle hτ hτone σ x₀ hε hn K hhalf f hlocal hz
  · rintro ⟨p, hp⟩
    apply hk
    rw [← hp]
    simp

/-- Literal analytic extraction of the normalized local theta series equals
the explicitly constructed recurrence coefficient sequence at every integer. -/
theorem analyticLaurentCoeff_local_theta_eq_supportedOrbit
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ ≤ 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 < n) (K : ℤ)
    (hhalf : Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) ≤ 1 / 2)
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (k : ℤ) :
    analyticLaurentCoeff (τ ^ x₀) f k =
      supportedOrbitCoefficient (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) n K
        ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) k := by
  by_cases hdiv : n ∣ k - K
  · let p := (k - K) / n
    have hp : n * p = k - K := Int.mul_ediv_cancel_of_dvd hdiv
    have hk : k = K + n * p := by omega
    rw [hk, analyticLaurentCoeff_of_local_theta_series hτ hτone σ x₀ hε hn K hhalf f hlocal,
      supportedOrbitCoefficient_on_orbit _ _ hn.ne', normalizedLaurentCoefficient_eq_orbitValue hτ]
  · have hres : k % n ≠ K % n := by
      intro heq
      exact hdiv (Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp heq))
    rw [analyticLaurentCoeff_local_theta_off_residue hτ hτone σ x₀ hε hn.le K hhalf f hlocal k hres]
    simp only [supportedOrbitCoefficient, ite_eq_right hdiv]

end Nagata.W09

end

section

noncomputable section
namespace Nagata.W09
open Nagata.W07 Complex Metric

/-- On an imaginary logarithmic contour the frequency exponential has norm one. -/
theorem norm_normalizedThetaTerm_imaginary {n a K τ : ℝ} {ε : ℂ}
    (hτ : 0 < τ) (hε : ‖ε‖ = 1) (p : ℤ) (θ : ℝ) :
    ‖normalizedThetaTerm n a K ε τ p ((θ : ℂ) * Complex.I)‖ =
      τ ^ thetaExponent n a (p : ℝ) := by
  simp [normalizedThetaTerm, hε, Complex.norm_exp,
    Complex.mul_re, Complex.mul_im, abs_of_nonneg (Real.rpow_nonneg hτ.le _)]

/-- A bilateral geometric majorant, summable for every q in [0,1). -/
theorem summable_geometric_natAbs {q : ℝ} (hq : 0 ≤ q) (hqone : q < 1) :
    Summable (fun p : ℤ => q ^ p.natAbs) := by
  have hs := summable_geometric_of_lt_one hq hqone
  have hp : Summable (fun t : ℕ => q ^ (t : ℤ).natAbs) := by simpa using hs
  have hnat (t : ℕ) : ((t : ℤ) + 1).natAbs = t + 1 := by
    simpa only [Nat.cast_add, Nat.cast_one] using Int.natAbs_natCast (t + 1)
  have hm : Summable (fun t : ℕ => q ^ (-(t + 1 : ℤ)).natAbs) := by
    simpa only [Int.natAbs_neg, hnat] using
      (summable_nat_add_iff (f := fun t : ℕ => q ^ t) 1).2 hs
  exact hp.of_nat_of_neg_add_one hm

noncomputable def thetaImaginaryMajorant (τ n a : ℝ) (p : ℤ) : ℝ :=
  (τ ^ thetaMargin n a) ^ p.natAbs

theorem thetaImaginaryMajorant_summable {τ n a : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) (ha : 0 < a) (han : a < n) :
    Summable (thetaImaginaryMajorant τ n a) :=
  summable_geometric_natAbs (Real.rpow_nonneg hτ.le _)
    (Real.rpow_lt_one hτ.le hτone (thetaMargin_pos ha han))

theorem normalizedLaurentMonomial_circle_sharp_bound {τ : ℝ}
    (hτ : 0 < τ) (hτone : τ ≤ 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n)
    (K p : ℤ) {z : ℂ} (hz : z ∈ sphere 0 (τ ^ x₀)) :
    ‖normalizedLaurentCoefficient τ σ x₀ ε n K p * z ^ (K + n * p)‖ ≤
      thetaImaginaryMajorant τ (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) p := by
  obtain ⟨θ, _, rfl⟩ := exists_circle_angle_of_mem_sphere (Real.rpow_pos_of_pos hτ _) hz
  have heval : circleMap 0 (τ ^ x₀) θ = ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp only [circleMap, zero_add]
  rw [heval, normalizedLaurentCoefficient_eval hτ,
    norm_normalizedThetaTerm_imaginary hτ hε]
  exact theta_power_le_geometric (by exact_mod_cast hn) hτ hτone p

theorem normalizedThetaTerm_hasSum_imaginary {τ n a K : ℝ}
    (hτ : 0 < τ) (hτone : τ < 1) (hn : 0 ≤ n) (ha : 0 < a) (han : a < n)
    {ε : ℂ} (hε : ‖ε‖ = 1) (θ : ℝ) :
    HasSum (fun p : ℤ => normalizedThetaTerm n a K ε τ p ((θ : ℂ) * Complex.I))
      (∑' p : ℤ, normalizedThetaTerm n a K ε τ p ((θ : ℂ) * Complex.I)) := by
  apply Summable.hasSum
  apply Summable.of_norm
  apply (thetaImaginaryMajorant_summable hτ hτone ha han).of_nonneg_of_le
  · intro p; exact norm_nonneg _
  · intro p
    rw [norm_normalizedThetaTerm_imaginary hτ hε]
    exact theta_power_le_geometric hn hτ hτone.le p

end Nagata.W09

end
end

section

noncomputable section
namespace Nagata.W09

open Nagata.W07

/-- The manuscript's normalized theta section as a genuine holomorphic
multiplier section, with the common multiplier gamma=epsilon*tau^sigma. -/
def normalizedSourceThetaSection (n K : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) :
    Nagata.W08.automorphicSections (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ)) := by
  let g := Nagata.W08.normalizedThetaSection n K hn ((K : ℝ) - σ) hε hτ hτone
  let c : ℂ := ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ)
  refine ⟨fun z => c * g.val z, ?_, ?_, ?_⟩
  · change c * g.val 0 = 0
    rw [g.property.1, mul_zero]
  · intro z hz
    exact (differentiableAt_const c).mul (g.property.2.1 z hz)
  · intro z hz
    change c * g.val ((τ : ℂ) * z) = _
    rw [g.property.2.2 z hz]
    have hσ : (K : ℝ) - ((K : ℝ) - σ) = σ := by ring
    calc
      _ = (ε * ((τ ^ ((K : ℝ) - ((K : ℝ) - σ)) : ℝ) : ℂ)) *
          z ^ (-n) * (c * g.val z) := by ring
      _ = _ := congrArg (fun t : ℝ => (ε * (t : ℂ)) * z ^ (-n) * (c * g.val z))
        (congrArg (fun t : ℝ => τ ^ t) hσ)

@[simp] theorem normalizedSourceThetaSection_apply
    (n K : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (z : ℂ) :
    (normalizedSourceThetaSection n K hn σ x₀ hε hτ hτone).val z =
      ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) *
        (Nagata.W08.normalizedThetaSection n K hn ((K : ℝ) - σ) hε hτ hτone).val z := rfl

/-- Exact local expression of the genuine global source-normalized section. -/
theorem normalizedSourceThetaSection_centered
    (n K : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (x : ℂ) :
    (normalizedSourceThetaSection n K hn σ x₀ hε hτ hτone).val
      (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x :=
  Nagata.W08.normalizedThetaSection_centered n K hn ((K : ℝ) - σ) x₀ hε hτ hτone x

end Nagata.W09

end
end

section

namespace Nagata.W09
open Complex Metric Nagata.W07

/-- The exact local theta-series identity and the checked fixed-disk majorant
supply a genuine monomial HasSum on the physical circle r=tau^x0. -/
theorem normalizedLaurentMonomial_hasSum_on_circle_all_tau
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n) (K : ℤ)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ))
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x)
    {z : ℂ} (hz : z ∈ sphere 0 (τ ^ x₀)) :
    HasSum (fun p : ℤ => normalizedLaurentCoefficient τ σ x₀ ε n K p * z ^ (K + n * p)) (f z) := by
  obtain ⟨θ, hθ, rfl⟩ := exists_circle_angle_of_mem_sphere (Real.rpow_pos_of_pos hτ _) hz
  have heval : circleMap 0 (τ ^ x₀) θ = ((τ ^ x₀ : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    simp only [circleMap, zero_add]
  rw [heval, hlocal]
  simpa only [normalizedLaurentCoefficient_eval hτ] using
    normalizedThetaTerm_hasSum_imaginary hτ hτone (by exact_mod_cast hn) ha han hε θ

/-- Under the exact local theta identity, actual contour extraction recovers
each explicit chosen Laurent coefficient; normal convergence is proved above. -/
theorem analyticLaurentCoeff_of_local_theta_series_all_tau
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 < n) (K : ℤ)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ))
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (p : ℤ) :
    analyticLaurentCoeff (τ ^ x₀) f (K + n * p) = normalizedLaurentCoefficient τ σ x₀ ε n K p := by
  refine analyticLaurentCoeff_monomial_series_at (Real.rpow_pos_of_pos hτ _)
    (normalizedLaurentCoefficient τ σ x₀ ε n K) (fun p : ℤ => K + n * p)
    ?_ f (thetaImaginaryMajorant τ (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)))
    (thetaImaginaryMajorant_summable hτ hτone ha han) ?_ ?_ p
  · intro a b hab
    exact mul_left_cancel₀ hn.ne' (add_left_cancel hab)
  · intro i z hz
    exact normalizedLaurentMonomial_circle_sharp_bound hτ hτone.le σ x₀ hε hn.le K i hz
  · intro z hz
    exact normalizedLaurentMonomial_hasSum_on_circle_all_tau hτ hτone σ x₀ hε hn.le K ha han f hlocal hz

/-- The analytic coefficient vanishes outside the selected residue class. -/
theorem analyticLaurentCoeff_local_theta_off_residue_all_tau
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 ≤ n) (K : ℤ)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ))
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (k : ℤ) (hk : k % n ≠ K % n) :
    analyticLaurentCoeff (τ ^ x₀) f k = 0 := by
  refine analyticLaurentCoeff_monomial_series_eq_zero (Real.rpow_pos_of_pos hτ _)
    (normalizedLaurentCoefficient τ σ x₀ ε n K) (fun p : ℤ => K + n * p)
    f (thetaImaginaryMajorant τ (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)))
    (thetaImaginaryMajorant_summable hτ hτone ha han) ?_ ?_ k ?_
  · intro i z hz
    exact normalizedLaurentMonomial_circle_sharp_bound hτ hτone.le σ x₀ hε hn K i hz
  · intro z hz
    exact normalizedLaurentMonomial_hasSum_on_circle_all_tau hτ hτone σ x₀ hε hn K ha han f hlocal hz
  · rintro ⟨p, hp⟩
    apply hk
    rw [← hp]
    simp

/-- Literal analytic extraction of the normalized local theta series equals
the explicitly constructed recurrence coefficient sequence at every integer. -/
theorem analyticLaurentCoeff_local_theta_eq_supportedOrbit_all_tau
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ‖ε‖ = 1) {n : ℤ} (hn : 0 < n) (K : ℤ)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ))
    (f : ℂ → ℂ)
    (hlocal : ∀ x : ℂ, f (((τ ^ x₀ : ℝ) : ℂ) * Complex.exp x) =
      ∑' p : ℤ, normalizedThetaTerm (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ))
        (K : ℝ) ε τ p x) (k : ℤ) :
    analyticLaurentCoeff (τ ^ x₀) f k =
      supportedOrbitCoefficient (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) n K
        ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) k := by
  by_cases hdiv : n ∣ k - K
  · let p := (k - K) / n
    have hp : n * p = k - K := Int.mul_ediv_cancel_of_dvd hdiv
    have hk : k = K + n * p := by omega
    rw [hk, analyticLaurentCoeff_of_local_theta_series_all_tau hτ hτone σ x₀ hε hn K ha han f hlocal,
      supportedOrbitCoefficient_on_orbit _ _ hn.ne', normalizedLaurentCoefficient_eq_orbitValue hτ]
  · have hres : k % n ≠ K % n := by
      intro heq
      exact hdiv (Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp heq))
    rw [analyticLaurentCoeff_local_theta_off_residue_all_tau hτ hτone σ x₀ hε hn.le K ha han f hlocal k hres]
    simp only [supportedOrbitCoefficient, ite_eq_right hdiv]

end Nagata.W09

end

section

noncomputable section
namespace Nagata.W09
open Nagata.W07

/-- The actual analytic extraction map of the genuine global theta section is
exactly the explicit supported Laurent orbit, for the concrete normal-convergence
parameter range used by the degeneration. -/
theorem laurentCoefficientMap_normalizedSourceThetaSection
    (n K : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (hhalf : Real.exp ((n : ℝ) * (2 * Real.pi)) *
      τ ^ thetaMargin (n : ℝ) ((K : ℝ) - σ + x₀ * (n : ℝ)) ≤ 1 / 2) (k : ℤ) :
    laurentCoefficientMap (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ))
      (normalizedSourceThetaSection n K hn σ x₀ hε hτ hτone) k =
      supportedOrbitCoefficient (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) n K
        ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) k := by
  let f := normalizedSourceThetaSection n K hn σ x₀ hε hτ hτone
  change analyticLaurentCoeff 1 f.val k = _
  rw [← analyticLaurentCoeff_radius_independent (Real.rpow_pos_of_pos hτ x₀)
    zero_lt_one f.property.2.1 k]
  exact analyticLaurentCoeff_local_theta_eq_supportedOrbit hτ hτone.le σ x₀ hunit hn K hhalf
    f.val (normalizedSourceThetaSection_centered n K hn σ x₀ hε hτ hτone) k

/-- The actual analytic extraction map of the genuine global theta section is
exactly the explicit supported Laurent orbit, for the concrete normal-convergence
parameter range used by the degeneration. -/
theorem laurentCoefficientMap_normalizedSourceThetaSection_all_tau
    (n K : ℤ) (hn : 0 < n) (σ x₀ : ℝ)
    {ε : ℂ} (hε : ε ≠ 0) (hunit : ‖ε‖ = 1)
    {τ : ℝ} (hτ : 0 < τ) (hτone : τ < 1)
    (ha : 0 < (K : ℝ) - σ + x₀ * (n : ℝ))
    (han : (K : ℝ) - σ + x₀ * (n : ℝ) < (n : ℝ)) (k : ℤ) :
    laurentCoefficientMap (τ : ℂ) n (ε * ((τ ^ σ : ℝ) : ℂ))
      (normalizedSourceThetaSection n K hn σ x₀ hε hτ hτone) k =
      supportedOrbitCoefficient (τ : ℂ) (ε * ((τ ^ σ : ℝ) : ℂ)) n K
        ((τ ^ (-x₀ * (K : ℝ)) : ℝ) : ℂ) k := by
  let f := normalizedSourceThetaSection n K hn σ x₀ hε hτ hτone
  change analyticLaurentCoeff 1 f.val k = _
  rw [← analyticLaurentCoeff_radius_independent (Real.rpow_pos_of_pos hτ x₀)
    zero_lt_one f.property.2.1 k]
  exact analyticLaurentCoeff_local_theta_eq_supportedOrbit_all_tau hτ hτone σ x₀ hunit hn K ha han
    f.val (normalizedSourceThetaSection_centered n K hn σ x₀ hε hτ hτone) k

end Nagata.W09

end
end

end OAI
