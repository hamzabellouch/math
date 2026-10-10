import OAI.Geometry.EinsteinFour.ScalarPoissonKernelAdjoint

namespace OAI

/-! The density step for distributional uniqueness. An invertible L2
extension of the transposed operator after Bessel regularization gives a
dense Schwartz range, and hence a trivial L2 distributional kernel. -/

namespace PositiveEinsteinFour.Geometry

open MeasureTheory TemperedDistribution FourierTransform
open scoped SchwartzMap ENNReal

noncomputable section

local notation "V" => EuclideanSpace ℝ (Fin 4)
local notation "L2" => Lp ℂ 2 (volume : Measure V)

/-- The negative-two Bessel multiplier preserves the actual test space. -/
def scalarSchwartzBesselInverse (φ : 𝓢(V, ℂ)) : 𝓢(V, ℂ) :=
  SchwartzMap.fourierMultiplierCLM ℂ
    (fun x : V => Complex.ofReal ((1 + ‖x‖ ^ 2) ^ (-1 : ℝ))) φ

theorem scalarSchwartzBesselInverse_distribution (φ : 𝓢(V, ℂ)) :
    (scalarSchwartzBesselInverse φ : 𝓢'(V, ℂ)) =
      besselPotential V ℂ (-2) (φ : 𝓢'(V, ℂ)) := by
  rw [besselPotential]
  norm_num only [show (-2 : ℝ) / 2 = -1 by norm_num]
  exact (fourierMultiplierCLM_toTemperedDistributionCLM_eq (by fun_prop) φ).symm

theorem scalarL2_distribution_injective :
    Function.Injective (fun f : L2 => (f : 𝓢'(V, ℂ))) :=
  LinearMap.ker_eq_bot.mp (Lp.ker_toTemperedDistributionCLM_eq_bot (F := ℂ)
    (μ := (volume : Measure V)) (p := 2))

theorem scalarSchwartzBesselInverse_toLp (φ : 𝓢(V, ℂ)) :
    (scalarSchwartzBesselInverse φ).toLp 2 = scalarBesselInverseL2 (φ.toLp 2) := by
  apply scalarL2_distribution_injective
  change ((scalarSchwartzBesselInverse φ).toLp 2 : 𝓢'(V, ℂ)) =
    (scalarBesselInverseL2 (φ.toLp 2) : 𝓢'(V, ℂ))
  rw [Lp.toTemperedDistribution_toLp_eq, scalarSchwartzBesselInverse_distribution,
    scalarBesselInverseL2_distribution, Lp.toTemperedDistribution_toLp_eq]

/-- The bilinear, rather than Hermitian, L2 pairing used by distributions. -/
def scalarL2TestPairing (u : L2) : L2 →L[ℂ] ℂ :=
  (ContinuousLinearMap.lsmul ℂ ℂ).flip.lpPairing volume 2 2 u

theorem scalarL2TestPairing_schwartz (u : L2) (φ : 𝓢(V, ℂ)) :
    scalarL2TestPairing u (φ.toLp 2) = (u : 𝓢'(V, ℂ)) φ := by
  rw [scalarL2TestPairing, ContinuousLinearMap.lpPairing_eq_integral,
    Lp.toTemperedDistribution_apply]
  apply integral_congr_ae
  filter_upwards [φ.coeFn_toLp 2 (volume : Measure V)] with x hx
  simp only [ContinuousLinearMap.lsmul_flip_apply, ContinuousLinearMap.toSpanSingleton_apply,
    hx]

/-- Surjectivity on L2 after a Schwartz-preserving regularization implies
density of the unregularized test-function range. -/
theorem scalarSchwartz_denseRange_of_bessel_equiv
    (T : 𝓢(V, ℂ) → 𝓢(V, ℂ)) (e : L2 ≃L[ℂ] L2)
    (hT : ∀ φ : 𝓢(V, ℂ), (T (scalarSchwartzBesselInverse φ)).toLp 2 = e (φ.toLp 2)) :
    DenseRange (fun φ : 𝓢(V, ℂ) => (T φ).toLp 2) := by
  have hd : DenseRange (fun φ : 𝓢(V, ℂ) => e (φ.toLp 2)) :=
    e.surjective.denseRange.comp (SchwartzMap.denseRange_toLpCLM ENNReal.ofNat_ne_top)
      e.continuous
  apply hd.mono
  rintro y ⟨φ, rfl⟩
  exact ⟨scalarSchwartzBesselInverse φ, hT φ⟩

/-- Nondegeneracy of the distributional L2 pairing. -/
theorem scalarL2_eq_zero_of_pairing (u : L2)
    (hzero : ∀ v : L2, scalarL2TestPairing u v = 0) : u = 0 := by
  apply scalarL2_distribution_injective
  change (u : 𝓢'(V, ℂ)) = Lp.toTemperedDistributionCLM ℂ volume 2 0
  rw [map_zero]
  ext φ
  have hφ : scalarL2TestPairing u (φ.toLp 2 (volume : Measure V)) = 0 :=
    hzero (φ.toLp 2 (volume : Measure V))
  have hpair : scalarL2TestPairing u (φ.toLp 2 (volume : Measure V)) =
      (u : 𝓢'(V, ℂ)) φ := scalarL2TestPairing_schwartz u φ
  rw [hpair] at hφ
  exact hφ

/-- A distribution represented by L2 is zero if it annihilates a dense
L2 family of Schwartz test functions. -/
theorem scalarL2_eq_zero_of_dense_tests (u : L2) (T : 𝓢(V, ℂ) → 𝓢(V, ℂ))
    (hT : DenseRange (fun φ : 𝓢(V, ℂ) => (T φ).toLp 2))
    (hu : ∀ φ : 𝓢(V, ℂ), (u : 𝓢'(V, ℂ)) (T φ) = 0) : u = 0 := by
  apply scalarL2_eq_zero_of_pairing
  intro v
  refine hT.induction_on (p := fun w => scalarL2TestPairing u w = 0) v
    (isClosed_eq (scalarL2TestPairing u).continuous continuous_const) ?_
  intro φ
  rw [scalarL2TestPairing_schwartz]
  exact hu φ

/-- A transposed L2 isomorphism gives distributional uniqueness without
regularity of the kernel element. -/
theorem scalarPerturbedOperator_kernel_of_transpose_equiv
    (a : Fin 4 → Fin 4 → 𝓢(V, ℂ)) (b : Fin 4 → 𝓢(V, ℂ))
    (e : L2 ≃L[ℂ] L2)
    (he : ∀ φ : 𝓢(V, ℂ),
      (scalarSchwartzTranspose a b (scalarSchwartzBesselInverse φ)).toLp 2 = e (φ.toLp 2))
    (u : L2) (hu : scalarPerturbedOperator a b (u : 𝓢'(V, ℂ)) = 0) : u = 0 := by
  apply scalarL2_eq_zero_of_dense_tests u (scalarSchwartzTranspose a b)
    (scalarSchwartz_denseRange_of_bessel_equiv _ e he)
  intro φ
  rw [← scalarPerturbedOperator_transpose, hu]
  rfl

end
end PositiveEinsteinFour.Geometry

end OAI
