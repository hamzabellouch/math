import OAI.NumberTheory.CubicMoment.Transform.MetaplecticPrimaryInverse

namespace OAI

/-! The completed formal coefficients are exactly the actual primary
Gauss cube-divisor coefficients, including the positive angular index
and the height multiplier. -/
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

lemma theta_cube_index (ℓ : ℤ) {c : Eisenstein} (hc : c ≠ 0) :
    theta (3*ℓ) c = theta ℓ (c^3) := by
  rw [show 3*ℓ = (ℓ+ℓ)+ℓ by ring,theta_add (ℓ+ℓ) ℓ hc,theta_add ℓ ℓ hc]
  simp only [pow_succ,pow_zero,one_mul,theta_mul]

lemma mellinPhase_cube_norm (t : ℝ) (x : ℝ) :
    mellinPhase (3*t) x = mellinPhase t (x^3) := by
  unfold mellinPhase
  rw [Real.log_pow]
  congr 1
  push_cast
  ring

lemma metaplecticCompletionWeight_phase (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c : Eisenstein} (hc : primary c) :
    metaplecticCompletionWeight r ℓ t c =
      if IsCoprime c r then
        (Real.sqrt (norm c):ℂ)*theta ℓ (c^3)*mellinPhase t (norm c^3)
      else 0 := by
  unfold metaplecticCompletionWeight
  rw [theta_cube_index ℓ (primary_ne_zero hc),
    ←mellinPhase_eq_cpow (norm_pos_of_ne_zero (primary_ne_zero hc)) (3*t),
    mellinPhase_cube_norm]

lemma metaplectic_completion_factor (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {c u : Eisenstein} (hc : primary c) (hu : primary u) :
    metaplecticCompletionWeight r ℓ t c*
      (gauss (r*u)*theta ℓ (r*u)*mellinPhase t (norm u)) =
        metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (c,u)*
          mellinPhase t (norm (metaplecticCubeProduct (c,u))) := by
  rw [metaplecticCompletionWeight_phase r ℓ t hc]
  by_cases hcr : IsCoprime c r
  · simp only [hcr,ite_true,metaplecticPrimalCoefficient,metaplecticCubeProduct,
      mul_one,theta_mul,norm_mul_eq,eisenstein_norm_pow]
    rw [mellinPhase_mul_pos t (norm_pos_of_ne_zero (primary_ne_zero hu))
      (pow_pos (norm_pos_of_ne_zero (primary_ne_zero hc)) 3)]
    ring
  · simp [hcr,metaplecticPrimalCoefficient]

/-- Completing the actual Gauss ideal series gives exactly the literal
primary cube fiber used by the Voronoi formula. -/
theorem metaplectic_completed_primary_coefficient
    (r : Eisenstein) (ℓ : ℤ) (t : ℝ)
    {b : Eisenstein} (hb : primary b) {F : ℝ} (hbF : norm b ≤ F) :
    MvPowerSeries.coeff (idealExponentOf b)
      (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*
        metaplecticGaussIdealSeries r ℓ t) =
      ∑ n ∈ primaryCubeFiber F b,
        metaplecticPrimalCoefficient r ℓ (fun _ => 1) 1 (n 0,n 1)*
          mellinPhase t (norm (metaplecticCubeProduct (n 0,n 1))) := by
  have he := weightedCubeSeries_product_primary
    (MvPowerSeries.map Complex.ofRealHom idealZeta)
    (metaplecticGaussIdealSeries r ℓ t)
    (metaplecticPrimeCompletionWeights r ℓ t) hb hbF
  change MvPowerSeries.coeff (idealExponentOf b)
    (cubeCompletionSeries (metaplecticPrimeCompletionWeights r ℓ t)*
      metaplecticGaussIdealSeries r ℓ t) = _ at he
  rw [he]
  apply Finset.sum_congr rfl
  intro n hn
  have hnp (i : Fin 2) := (mem_primaryElementBall.mp
    (Fintype.mem_piFinset.mp (Finset.mem_filter.mp hn).1 i)).1
  have hz : MvPowerSeries.coeff (idealExponentOf (n 0))
      (MvPowerSeries.map Complex.ofRealHom idealZeta) = 1 := by
    rw [MvPowerSeries.coeff_map]
    change Complex.ofRealHom (1:ℝ) = 1
    exact map_one _
  rw [hz,mul_one]
  simp only [metaplecticPrimeCompletionWeights]
  rw [normalized_prime_product_character (hnp 0) le_rfl
    (metaplecticCompletionWeight r ℓ t) (metaplecticCompletionWeight_one r ℓ t)
    (fun _ _ ha hb => metaplecticCompletionWeight_mul r ℓ t ha hb),
    idealPrimaryGenerator_at_element (hnp 0),
    metaplecticGaussIdealSeries_at_primary r ℓ t (hnp 1)]
  exact metaplectic_completion_factor r ℓ t (hnp 0) (hnp 1)

end CubicFirstMoment

end

end OAI
