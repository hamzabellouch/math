import OAI.Analysis.KadisonSimilarity.Representation.WeakOperatorIntegral

namespace OAI

/-! Haar symmetrization, defined through weak scalar integrals. This applies
to the compact matrix-unitary actions used in the free-product argument. -/

noncomputable section
namespace KadisonSimilarity

open MeasureTheory ContinuousLinearMap

variable {Γ H K : Type*} [Group Γ] [MeasurableSpace Γ] [MeasurableMul Γ]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (μ : Measure Γ) [IsProbabilityMeasure μ] [μ.IsMulLeftInvariant]

/-- The orbit of a bounded operator under a representation. -/
def unitaryConjugate (U : Γ →* (H →L[ℂ] H)) (T : H →L[ℂ] H) (g : Γ) :
    H →L[ℂ] H := U g * T * U g⁻¹

omit [MeasurableSpace Γ] [MeasurableMul Γ] [CompleteSpace H] in
theorem norm_unitaryConjugate_le (U : Γ →* (H →L[ℂ] H))
    (hU : ∀ g, ‖U g‖ ≤ 1) (T : H →L[ℂ] H) (g : Γ) :
    ‖unitaryConjugate U T g‖ ≤ ‖T‖ := by
  calc
    _ ≤ ‖U g‖ * ‖T‖ * ‖U g⁻¹‖ :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _))
    _ ≤ 1 * ‖T‖ * 1 := by gcongr; exact hU _; exact hU _
    _ = ‖T‖ := by ring

/-- The Haar average is an actual bounded operator, with its weak integral
constructed through Hilbert-space duality. -/
def haarTwirl (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) : H →L[ℂ] H :=
  weakOperatorIntegral μ (unitaryConjugate U T) hI ‖T‖ (norm_unitaryConjugate_le U hU T)

omit [MeasurableMul Γ] [μ.IsMulLeftInvariant] in
/-- Haar averaging is contractive in operator norm. -/
theorem norm_haarTwirl_le (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) :
    ‖haarTwirl μ U hU T hI‖ ≤ ‖T‖ :=
  norm_weakOperatorIntegral_le μ _ _ _ (norm_nonneg _) _

/-- Left invariance of Haar measure gives invariance of the operator average. -/
theorem haarTwirl_conjugate (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) (g : Γ) :
    U g * haarTwirl μ U hU T hI * U g⁻¹ = haarTwirl μ U hU T hI := by
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  rw [haarTwirl, weakOperatorIntegral_sandwich_inner, weakOperatorIntegral_inner]
  calc
    _ = ∫ h, inner ℂ (unitaryConjugate U T (g * h) x) y ∂μ := by
      apply integral_congr_ae
      filter_upwards with h
      congr 2
      simp only [unitaryConjugate, mul_inv_rev, map_mul, mul_assoc]
    _ = _ := integral_mul_left_eq_self (μ := μ) (fun h => inner ℂ (unitaryConjugate U T h x) y) g

/-- Thus the Haar average commutes with the whole compact group. -/
theorem haarTwirl_commute (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T)) (g : Γ) :
    commutator (haarTwirl μ U hU T hI) (U g) = 0 := by
  have hc := congrArg (fun B : H →L[ℂ] H => B * U g) (haarTwirl_conjugate μ U hU T hI g)
  have hi : U g⁻¹ * U g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  simp only [mul_assoc, hi, mul_one] at hc
  exact sub_eq_zero.mpr hc.symm

omit [MeasurableMul Γ] [μ.IsMulLeftInvariant] in
/-- Every common commutator estimate for the orbit survives Haar averaging. -/
theorem norm_commutator_haarTwirl_le (U : Γ →* (H →L[ℂ] H))
    (hU : ∀ g, ‖U g‖ ≤ 1) (T : H →L[ℂ] H)
    (hI : WeaklyIntegrable μ (unitaryConjugate U T)) (B : H →L[ℂ] H)
    {c : ℝ} (hc : 0 ≤ c) (hcomm : ∀ g, ‖commutator (unitaryConjugate U T g) B‖ ≤ c) :
    ‖commutator (haarTwirl μ U hU T hI) B‖ ≤ c :=
  norm_commutator_weakOperatorIntegral_le μ _ _ _ _ B hc hcomm

omit [MeasurableMul Γ] [μ.IsMulLeftInvariant] in
/-- On a subspace fixed pointwise by the group, compression is exactly
preserved by averaging. -/
theorem haarTwirl_compression (U : Γ →* (H →L[ℂ] H)) (hU : ∀ g, ‖U g‖ ≤ 1)
    (hstar : ∀ g, (U g).adjoint = U g⁻¹)
    (T : H →L[ℂ] H) (hI : WeaklyIntegrable μ (unitaryConjugate U T))
    (J : K →L[ℂ] H) (hfix : ∀ g, (U g).comp J = J) :
    J.adjoint.comp ((haarTwirl μ U hU T hI).comp J) = J.adjoint.comp (T.comp J) := by
  have happly (g : Γ) (x : K) : U g (J x) = J x :=
    congrArg (fun B : K →L[ℂ] H => B x) (hfix g)
  apply ContinuousLinearMap.ext
  intro x
  apply ext_inner_right ℂ
  intro y
  change inner ℂ (J.adjoint (haarTwirl μ U hU T hI (J x))) y =
    inner ℂ (J.adjoint (T (J x))) y
  rw [adjoint_inner_left, adjoint_inner_left, haarTwirl, weakOperatorIntegral_inner]
  apply integral_eq_const
  filter_upwards with g
  change inner ℂ (U g (T (U g⁻¹ (J x)))) (J y) = _
  rw [happly, ← adjoint_inner_right, hstar, happly]

end KadisonSimilarity

end

end OAI
