import OAI.Analysis.IrrationalRotation.Analysis.ParameterOrbitIdentity

namespace OAI

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace Invariant233.CircleParameterLaws
open CircleParameterData WeightedShift

variable {θ : ℝ} {p : CircleParameterData} (hp : CircleParameterLaws θ p)
include hp

theorem parameter_orbitProduct_eq_floorCocycle {s : Set Circle}
    (hinv : ∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s)
    (hc : ∀ x ∈ s, ∀ k n : ℤ, p.floorCocycle θ (k + n) x =
      p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x)
    {y : Circle} (hy : y ∈ s) (n : ℕ) (v : ℤ) :
    orbitProduct (hp.parameterOrbitWeight y) n v =
      (p.floorCocycle θ (n : ℤ) (Rotation.action θ v y) : ℂ) := by
  rw [orbitProduct_apply]
  have hprod := p.weight_product_eq_floorCocycle θ (Rotation.action θ v y)
    (hc _ ((hinv v y).mpr hy)) n
  convert hprod using 1
  apply Finset.prod_congr rfl
  intro j hj
  change (p.measurableWeight θ (Rotation.action θ (v + j) y) : ℂ) =
    (p.measurableWeight θ (Rotation.action θ (j : ℤ) (Rotation.action θ v y)) : ℂ)
  rw [Rotation.action_add, add_comm v]

theorem parameter_orbitProduct_mul_ratio {s : Set Circle}
    (hinv : ∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s)
    (hc : ∀ x ∈ s, ∀ k n : ℤ, p.floorCocycle θ (k + n) x =
      p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x)
    (x : Circle) {y : Circle} (hy : y ∈ s) (n : ℕ) (v : ℤ) :
    orbitProduct (hp.parameterOrbitWeight y) n v *
        ((p.floorCocycle θ v y / p.floorCocycle θ v x : ℝ) : ℂ) =
      (p.floorCocycle θ (v + n) y : ℂ) / (p.floorCocycle θ v x : ℂ) := by
  rw [hp.parameter_orbitProduct_eq_floorCocycle hinv hc hy n v,
    hc y hy v n, Complex.ofReal_mul, Complex.ofReal_div]
  simp only [Rotation.action, CircleWeights.rotate]
  ring

theorem parameter_convolution_absolute_and_zero {s : Set Circle}
    (hinv : ∀ (k : ℤ) x, CircleWeights.rotate θ k x ∈ s ↔ x ∈ s)
    (hc : ∀ x ∈ s, ∀ k n : ℤ, p.floorCocycle θ (k + n) x =
      p.floorCocycle θ n (CircleWeights.rotate θ k x) * p.floorCocycle θ k x)
    (x : Circle) {y : Circle} (hy : y ∈ s)
    (P Q : Hilbert →L[ℂ] Hilbert) (hQ : IsStarProjection Q)
    (hT : (1 - Q) * operator (hp.parameterOrbitWeight y) * Q = 0)
    (hpair : (1 - Q) * ratioDiagonal (p.floorCocycle θ) (x, y) * P = 0)
    (hbound : ∀ v : ℤ, p.floorCocycle θ v y / p.floorCocycle θ v x ≤ 1)
    (n : ℕ) (ξ η : Hilbert) :
    let A : ℤ → ℂ := fun v => P ξ v / (p.floorCocycle θ v x : ℂ)
    let B : ℤ → ℂ := fun v => (p.floorCocycle θ (-v) y : ℂ) * star ((1 - Q) η (-v))
    Summable (fun v : ℤ => ‖A v * B (-(n : ℤ) - v)‖) ∧
      (∑' v : ℤ, A v * B (-(n : ℤ) - v)) = 0 := by
  let r : Weight := ⟨fun v => ((p.floorCocycle θ v y / p.floorCocycle θ v x : ℝ) : ℂ),
    memℓp_infty <| by
      refine ⟨1, ?_⟩
      rintro a ⟨v, rfl⟩
      change ‖((p.floorCocycle θ v y / p.floorCocycle θ v x : ℝ) : ℂ)‖ ≤ 1
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (div_pos (p.floorCocycle_pos θ v y) (p.floorCocycle_pos θ v x))]
      exact hbound v⟩
  have hd : ratioDiagonal (p.floorCocycle θ) (x, y) = diagonal r :=
    SequenceHilbert.boundedDiagonal_eq_weighted r
  rw [hd] at hpair
  exact OrbitInvariance.cocycle_coefficients_absolute_and_zero
    (hp.parameterOrbitWeight y) r (fun v => p.floorCocycle θ v x)
    (fun v => p.floorCocycle θ v y) hQ hT hpair n ξ η
    (hp.parameter_orbitProduct_mul_ratio hinv hc x hy n)

theorem ae_parameter_convolution_absolute_and_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → Circle) (hy : AEMeasurable y μ)
    (hyac : Measure.map y μ ≪ circleMeasure)
    {P : Rotation.Hilbert →L[ℂ] Rotation.Hilbert}
    (F : Circle → Rotation.Fiber →L[ℂ] Rotation.Fiber)
    (hF : ∀ z, IsStarProjection (F z))
    (hrep : ∀ ξ : Rotation.Hilbert, P ξ =ᵐ[circleMeasure] fun z => F z (ξ z))
    (hT : (1 - P) * p.measurableOperator θ hp * P = 0)
    (hpair : ∀ᵐ ω ∂μ,
      (1 - F (y ω)) * ratioDiagonal (p.floorCocycle θ) (x ω, y ω) * F (x ω) = 0)
    (hbound : ∀ᵐ ω ∂μ, ∀ v : ℤ,
      p.floorCocycle θ v (y ω) / p.floorCocycle θ v (x ω) ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ (n : ℕ) (ξ η : Hilbert),
      let A : ℤ → ℂ := fun v => F (x ω) ξ v / (p.floorCocycle θ v (x ω) : ℂ)
      let B : ℤ → ℂ := fun v => (p.floorCocycle θ (-v) (y ω) : ℂ) *
        star ((1 - F (y ω)) η (-v))
      Summable (fun v : ℤ => ‖A v * B (-(n : ℤ) - v)‖) ∧
        (∑' v : ℤ, A v * B (-(n : ℤ) - v)) = 0 := by
  have hlocal := DirectIntegral.ae_invariant_of_representations
    (default : HilbertBasis ℤ ℂ Rotation.Fiber) P (p.measurableOperator θ hp) F
    (fun z => operator (hp.parameterOrbitWeight z)) hrep hp.measurableOperator_ae hT
  obtain ⟨s, _, hfull, hs, _, hc⟩ := hp.exists_parameter_cocycle_set
  have hylocal := ae_of_ae_map hy (hyac.ae_le hlocal)
  have hyfull := ae_of_ae_map hy (hyac.ae_le hfull)
  filter_upwards [hylocal, hyfull, hpair, hbound] with ω hloc hys hpa hbo
  intro n ξ η
  exact hp.parameter_convolution_absolute_and_zero hs hc (x ω) hys
    (F (x ω)) (F (y ω)) (hF (y ω)) hloc hpa hbo n ξ η

theorem parameter_convolution_ratio_bounds (x y : Circle)
    (hx : ∀ k : ℤ, Function.HasFiniteSupport (fun i : p.Coord =>
      Int.floor (p.coordinate i.2 x + (k : ℝ) * p.alpha θ i.2)))
    (hy : ∀ k : ℤ, Function.HasFiniteSupport (fun i : p.Coord =>
      Int.floor (p.coordinate i.2 y + (k : ℝ) * p.alpha θ i.2)))
    (hbound : ∀ v : ℤ, p.floorCocycle θ v y / p.floorCocycle θ v x ≤ 1)
    (n : ℕ) (v : ℤ) :
    0 < p.floorCocycle θ ((n : ℤ) + v) y / p.floorCocycle θ v x ∧
      p.floorCocycle θ ((n : ℤ) + v) y / p.floorCocycle θ v x ≤
        min (p.floorCocycle θ v y / p.floorCocycle θ v x)
          (p.floorCocycle θ ((n : ℤ) + v) y / p.floorCocycle θ ((n : ℤ) + v) x) ∧
      min (p.floorCocycle θ v y / p.floorCocycle θ v x)
          (p.floorCocycle θ ((n : ℤ) + v) y / p.floorCocycle θ ((n : ℤ) + v) x) ≤ 1 := by
  have hle : v ≤ (n : ℤ) + v := by omega
  have hmx := hp.parameter_cocycle_antitone x hx hle
  have hmy := hp.parameter_cocycle_antitone y hy hle
  refine ⟨div_pos (p.floorCocycle_pos θ _ y) (p.floorCocycle_pos θ v x),
    le_min ?_ ?_, (min_le_left _ _).trans (hbound v)⟩
  · exact (div_le_div_iff_of_pos_right (p.floorCocycle_pos θ v x)).mpr hmy
  · exact div_le_div_of_nonneg_left (p.floorCocycle_pos θ _ y).le
      (p.floorCocycle_pos θ _ x) hmx

theorem ae_parameter_convolution_ratio_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (x y : Ω → Circle) (hx : AEMeasurable x μ) (hy : AEMeasurable y μ)
    (hxac : Measure.map x μ ≪ circleMeasure) (hyac : Measure.map y μ ≪ circleMeasure)
    (hbound : ∀ᵐ ω ∂μ, ∀ v : ℤ,
      p.floorCocycle θ v (y ω) / p.floorCocycle θ v (x ω) ≤ 1) :
    ∀ᵐ ω ∂μ, ∀ (n : ℕ) (v : ℤ),
      0 < p.floorCocycle θ ((n : ℤ) + v) (y ω) / p.floorCocycle θ v (x ω) ∧
      p.floorCocycle θ ((n : ℤ) + v) (y ω) / p.floorCocycle θ v (x ω) ≤
        min (p.floorCocycle θ v (y ω) / p.floorCocycle θ v (x ω))
          (p.floorCocycle θ ((n : ℤ) + v) (y ω) /
            p.floorCocycle θ ((n : ℤ) + v) (x ω)) ∧
      min (p.floorCocycle θ v (y ω) / p.floorCocycle θ v (x ω))
          (p.floorCocycle θ ((n : ℤ) + v) (y ω) /
            p.floorCocycle θ ((n : ℤ) + v) (x ω)) ≤ 1 := by
  obtain ⟨s, _, hfull, _, hfinite, _⟩ := hp.exists_parameter_cocycle_set
  have hxfull := ae_of_ae_map hx (hxac.ae_le hfull)
  have hyfull := ae_of_ae_map hy (hyac.ae_le hfull)
  filter_upwards [hxfull, hyfull, hbound] with ω hxs hys hb
  intro n v
  exact hp.parameter_convolution_ratio_bounds (x ω) (y ω)
    (hfinite _ hxs) (hfinite _ hys) hb n v

end Invariant233.CircleParameterLaws

end

end OAI
