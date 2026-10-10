import OAI.Analysis.CircleDomains.Topology.CollarScalarControl
import OAI.Analysis.CircleDomains.Topology.CollarMeanLowerBound

namespace OAI

/-! Choose the smoothing accuracy before the inward circuit. Uniform
variation of the fixed smooth weight and the actual starting-point law
give a strictly positive boundary integral on every sufficiently small
inward circuit. -/

open Set Function Filter MeasureTheory
open scoped Topology

noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

 theorem OrderedCollarLift.exists_strict_mean_lower_bound
    {H : ℂ ≃ₜ ℂ} {C : RegularJordanInwardCollar H} {F : C(Sphere, ℂ)}
    (D : OrderedCollarLift C F)
    (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (η : ProbabilityMeasure K)
    [NullSingletonClass (compactArcStartingAngleLaw K η : Measure UnitAddCircle)]
    (O : Set ℂ) (hO : IsOpen O) (hCO : frontier (jordanInterior H) ⊆ O)
    (Φ : ℂ → ℝ) (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ O)
    {d : ℝ} (hd : 0 < d)
    (hgate : ∀ᵐ θ : UnitAddCircle ∂(compactArcStartingAngleLaw K η : Measure UnitAddCircle),
      d ≤ Φ (D.circuit 0 (D.angle.symm (unitCircleCut θ)))) :
    ∃ ε > 0, ε ≤ 1 ∧ ∃ σ > 0, σ < D.width ∧ ∀ ρ ∈ Ioc (0 : ℝ) σ,
      ∀ (W : Set ℂ), IsOpen W → ∀ (w : ℂ → UnitAddCircle), SmoothCircleOn w W →
      (∀ t, D.circuit ρ t ∈ W) →
      (∀ t, ∀ᵐ α : K ∂(η : Measure K), F (D.circuit ρ t : Sphere) ∉ range α.val) →
      ∀ (R : ℂ → ℝ), Continuous (R ∘ D.circuit ρ) →
      (∀ t, w (D.circuit ρ t) = diskMeanCircle hsch K hKS η (F (D.circuit ρ t : Sphere)) +
        (R (D.circuit ρ t) : UnitAddCircle)) →
      (∀ t ∈ Icc (0 : ℝ) 1, |R (D.circuit ρ t)| ≤ ε) →
      d / 2 < |circleFormIntegral Φ w (C.curve ρ)| := by
  obtain ⟨ζ, B, hζ, hζw, hB, hderiv⟩ := C.scalar_derivative_bound hO hCO Φ hΦ
  let ε := min 1 (d / (16 * (B + 1)))
  have hden : 0 < 16 * (B + 1) := by positivity
  have hε : 0 < ε := lt_min zero_lt_one (div_pos hd hden)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hprod : ε * (16 * (B + 1)) ≤ d :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have herror : 2 * ε * B < d / 8 := by nlinarith
  obtain ⟨α, hα, _hαw, hnear⟩ := C.scalar_uniform_approach hO hCO Φ hΦ.continuousOn (d / 8) (by positivity)
  obtain ⟨μ, hμ, hμw, hinside⟩ := C.eventually_in_boundary_neighborhood hO hCO
  obtain ⟨τ, hτ, hτw, hmean⟩ := D.mean_boundary_lower_bound hsch hsep K hK hKS η hε
  let σ := min ζ (min α (min μ τ))
  have hσ : 0 < σ := lt_min hζ (lt_min hα (lt_min hμ hτ))
  have hσζ : σ ≤ ζ := min_le_left _ _
  have hσα : σ ≤ α := (min_le_right _ _).trans (min_le_left _ _)
  have hσμ : σ ≤ μ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hστ : σ ≤ τ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, hε, hε1, σ, hσ, hστ.trans_lt hτw, ?_⟩
  intro ρ hρ W hW w hw hγW hmiss R hR hv hRb
  have hρζ : ρ ∈ Icc (0 : ℝ) ζ := ⟨hρ.1.le, hρ.2.trans hσζ⟩
  have hρα : ρ ∈ Icc (0 : ℝ) α := ⟨hρ.1.le, hρ.2.trans hσα⟩
  have hρμ : ρ ∈ Icc (0 : ℝ) μ := ⟨hρ.1.le, hρ.2.trans hσμ⟩
  have hρC : ρ ∈ Icc (0 : ℝ) C.width := ⟨hρ.1.le, hρμ.2.trans hμw⟩
  have hγO (t : ℝ) : D.circuit ρ t ∈ O := by
    let s := orientedParameter D.start D.reverse t
    have hh := hinside ρ hρμ (Int.fract s) ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    have he : C.curve ρ (Int.fract s) = C.curve ρ s := by
      simpa only [Int.fract, mul_one] using
        (C.parametrization ρ hρC).periodic.sub_int_mul_eq (x := s) ⌊s⌋
    rwa [he] at hh
  have hpositive : ∀ᵐ θ : UnitAddCircle ∂(compactArcStartingAngleLaw K η : Measure UnitAddCircle),
      d - d / 8 ≤ Φ (D.circuit ρ (D.angle.symm (unitCircleCut θ))) := by
    filter_upwards [hgate] with θ hθ
    have hn := hnear ρ hρα (orientedParameter D.start D.reverse (D.angle.symm (unitCircleCut θ)))
    change |Φ (D.circuit ρ (D.angle.symm (unitCircleCut θ))) -
      Φ (D.circuit 0 (D.angle.symm (unitCircleCut θ)))| < d / 8 at hn
    linarith [(abs_lt.mp hn).1]
  have hb := hmean ρ ⟨hρ.1, hρ.2.trans hστ⟩ (O ∩ W) (hO.inter hW) w
    (fun x hx => hw x hx.2) (fun t => ⟨hγO t, hγW t⟩) hmiss
    R hR hv hRb Φ (hΦ.mono inter_subset_left) (d - d / 8) hpositive
  have hV : (∫ t in (0 : ℝ)..1, |deriv (Φ ∘ D.circuit ρ) t|) ≤ B := by
    have hbound (t : ℝ) : |deriv (Φ ∘ D.circuit ρ) t| ≤ B :=
      hderiv ρ hρζ D.start D.reverse t
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := (1 : ℝ))
      (f := fun t : ℝ => |deriv (Φ ∘ D.circuit ρ) t|) (C := B)
      (fun t _ => by simpa only [Real.norm_eq_abs, abs_abs] using hbound t)
    have hh' : |(∫ t in (0 : ℝ)..1, |deriv (Φ ∘ D.circuit ρ) t|)| ≤ B := by
      simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one] using hh
    exact (le_abs_self _).trans hh'
  have hVε := mul_le_mul_of_nonneg_left hV (show 0 ≤ 2 * ε by positivity)
  nlinarith

end CircleDomainRigidity

end

end OAI
