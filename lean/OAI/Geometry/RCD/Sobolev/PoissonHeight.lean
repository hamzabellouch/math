import OAI.Geometry.RCD.Sobolev.BoundaryMaximum
import OAI.Geometry.RCD.Sobolev.TorsionBound
import OAI.Geometry.RCD.Sobolev.PoissonComparison

namespace OAI

/-!
# Height control for the Poisson replacement

A bounded torsion solution and the weak boundary maximum principle provide
the bound needed by the positive-source gradient estimate.
-/

open Set MeasureTheory Filter
open scoped InnerProductSpace ENNReal NNReal

noncomputable section

namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) (hQ : QuadraticCheegerEnergy μ)

/-- Coercivity constructs torsion and the Sobolev iteration bounds it with
a constant uniform over all the displayed domains. -/
theorem exists_uniform_bounded_torsion {d C V : ℝ} (hd : 1 < d)
    (hC : 0 ≤ C) (hV : 0 ≤ V) :
    ∃ K : ℝ, 0 < K ∧ ∀ (Ω : Set X), MeasurableSet Ω → μ Ω ≠ ∞ → μ.real Ω ≤ V →
      ∀ P : ℝ, 0 ≤ P →
      (∀ v : SobolevSpace.dirichlet μ hQ Ω,
        ‖SobolevSpace.toLp μ hQ v.val‖ ^ 2 ≤ P * energyForm μ hQ v.val v.val) →
      (∀ φ : SobolevSpace.dirichlet μ hQ Ω,
        (∫ x in Ω, |SobolevSpace.toLp μ hQ φ.val x| ^ (2 * d) ∂μ) ^ (1 / d) ≤
          C * energyForm μ hQ φ.val φ.val) →
      ∃ τ : SobolevSpace.dirichlet μ hQ Ω,
        (∀ φ : SobolevSpace.dirichlet μ hQ Ω,
          energyForm μ hQ τ.val φ.val = ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ) ∧
        (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ τ.val x ∧
          SobolevSpace.toLp μ hQ τ.val x ≤ K) := by
  obtain ⟨K, hK, hb⟩ := exists_uniform_torsion_bound μ hQ hd hC hV
  refine ⟨K, hK, ?_⟩
  intro Ω hΩ hfin hvol P hP hpoin hsob
  let F := dirichletSource μ hQ Ω (indicatorConstLp 2 hΩ hfin 1)
  have hF (φ : SobolevSpace.dirichlet μ hQ Ω) :
      F φ = ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ := by
    simpa only [F, one_mul] using dirichletSource_indicator μ hQ Ω hΩ hfin 1 φ
  have hpos (φ : SobolevSpace.dirichlet μ hQ Ω)
      (hφ : ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x) : 0 ≤ F φ := by
    rw [hF]
    exact integral_nonneg_of_ae (ae_restrict_of_ae hφ)
  obtain ⟨τ, hτ, hτ0⟩ := exists_nonnegative_dirichlet_solution μ hQ Ω hP hpoin F hpos
  have hsolve (φ : SobolevSpace.dirichlet μ hQ Ω) := (hτ φ).trans (hF φ)
  have hτK := hb Ω hfin hvol τ hsolve hsob
  have hupper : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ τ.val x ≤ K := by
    apply ae_of_ae_restrict_of_ae_restrict_compl Ω hτK
    filter_upwards [SobolevSpace.dirichlet_zero_off μ hQ Ω hΩ τ] with x hx
    rw [hx]
    exact hK.le
  exact ⟨τ, hsolve, hτ0.and hupper⟩

omit [BorelSpace X] [ProperSpace X] in
/-- Torsion comparison bounds the nonnegative difference of the boundary
datum and its constant-Laplacian replacement. -/
theorem poisson_replacement_height_le (Ω : Set X) (hΩ : MeasurableSet Ω)
    (hfin : μ Ω ≠ ∞) {P : ℝ} (hP : 0 ≤ P)
    (hpoin : ∀ v : SobolevSpace.dirichlet μ hQ Ω,
      ‖SobolevSpace.toLp μ hQ v.val‖ ^ 2 ≤ P * energyForm μ hQ v.val v.val)
    (q f : SobolevSpace μ hQ) (Q : X → ℝ) {L : ℝ≥0}
    (hQlip : LipschitzWith L Q) (hQ0 : ∀ x, 0 ≤ Q x)
    (hq : SobolevSpace.toLp μ hQ q =ᵐ[μ] Q)
    {a B K : ℝ} (ha : 0 ≤ a) (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hQB : ∀ᵐ x ∂μ.restrict Ω, Q x ≤ B)
    (τ : SobolevSpace.dirichlet μ hQ Ω)
    (hτ : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      energyForm μ hQ τ.val φ.val = ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ)
    (hτK : ∀ᵐ x ∂μ, SobolevSpace.toLp μ hQ τ.val x ≤ K)
    (hfq : f - q ∈ SobolevSpace.dirichlet μ hQ Ω)
    (hsolve : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      energyForm μ hQ f φ.val = -a * ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ)
    (hcomparison : ∀ φ : SobolevSpace.dirichlet μ hQ Ω,
      (∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ φ.val x) →
      -energyForm μ hQ q φ.val ≤ a * ∫ x in Ω, SobolevSpace.toLp μ hQ φ.val x ∂μ) :
    ∀ᵐ x ∂μ, 0 ≤ SobolevSpace.toLp μ hQ (q - f) x ∧
      SobolevSpace.toLp μ hQ (q - f) x ≤ B + a * K := by
  have hlower := constant_laplacian_replacement_le μ hQ Ω hΩ hfin hP hpoin
    a q f hfq hsolve hcomparison
  have hboundary : (f + a • τ.val) - q ∈ SobolevSpace.dirichlet μ hQ Ω := by
    have hm := (SobolevSpace.dirichlet μ hQ Ω).add_mem hfq
      ((SobolevSpace.dirichlet μ hQ Ω).smul_mem a τ.property)
    have he : (f + a • τ.val) - q = (f - q) + a • τ.val := by module
    rw [he]
    exact hm
  have hharm (φ : SobolevSpace.dirichlet μ hQ Ω) :
      energyForm μ hQ (f + a • τ.val) φ.val = 0 := by
    rw [energyForm_add_left, energyForm_smul_left, hsolve, hτ]
    ring
  have hnonneg := harmonic_nonneg_of_boundary μ hQ Ω hP hpoin (f + a • τ.val) q Q
    hQlip hQ0 hq hboundary hharm
  have hnonneg' : ∀ᵐ x ∂μ,
      0 ≤ SobolevSpace.toLp μ hQ f x + a * SobolevSpace.toLp μ hQ τ.val x := by
    filter_upwards [hnonneg, Lp.coeFn_add (SobolevSpace.toLp μ hQ f)
      (a • SobolevSpace.toLp μ hQ τ.val), Lp.coeFn_smul a (SobolevSpace.toLp μ hQ τ.val)]
      with x hx hadd hsmul
    rw [map_add, map_smul, hadd, Pi.add_apply, hsmul] at hx
    exact hx
  have hHmem : q - f ∈ SobolevSpace.dirichlet μ hQ Ω := by
    simpa only [neg_sub] using (SobolevSpace.dirichlet μ hQ Ω).neg_mem hfq
  apply ae_of_ae_restrict_of_ae_restrict_compl Ω
  · filter_upwards [ae_restrict_of_ae hlower, ae_restrict_of_ae hnonneg',
      ae_restrict_of_ae hτK, ae_restrict_of_ae hq, hQB,
      ae_restrict_of_ae (Lp.coeFn_sub (SobolevSpace.toLp μ hQ q)
        (SobolevSpace.toLp μ hQ f))] with x hlo hn ht hqx hBq hsub
    rw [map_sub, hsub, Pi.sub_apply]
    have hta := mul_le_mul_of_nonneg_left ht ha
    constructor <;> linarith
  · filter_upwards [SobolevSpace.dirichlet_zero_off μ hQ Ω hΩ ⟨q - f, hHmem⟩] with x hx
    rw [hx]
    exact ⟨le_rfl, add_nonneg hB (mul_nonneg ha hK)⟩

end RegularPointCoordinates

end

end OAI
