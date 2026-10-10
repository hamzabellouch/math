import OAI.Geometry.SurfaceImmersion.Correction.CombinedSeedMean

namespace OAI

/-! Exact mean identity, support and global smoothness for the combined mean. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.SmallModes
open JetPolynomial

lemma seedMeanError_zero_outside {n : ℕ} (τ : ℝ) (K : Compacts Base)
    (T : SupportedField (F := Ambient n) K →ₗ[ℝ] SupportedField (F := Ambient n) K)
    (V W : SupportedField (F := Ambient n) K) (v w p : Base) (hp : p ∉ (K : Set Base)) :
    seedMeanError τ T V W v w p = 0 := by
  have hV : p ∉ tsupport V := fun hx => hp (V.tsupport_subset hx)
  have hTV : p ∉ tsupport (T V) := fun hx => hp ((T V).tsupport_subset hx)
  have hd : gradientAmplitude τ (T V) v p = 0 := by
    simp only [gradientAmplitude, coordDeriv, fderiv_of_notMem_tsupport ℝ hTV,
      zero_apply, image_eq_zero_of_notMem_tsupport hTV, smul_zero, add_zero]
  have hl : leadingDerivative τ V v p = 0 := by
    simp only [leadingDerivative, image_eq_zero_of_notMem_tsupport hV, smul_zero]
  simp only [seedMeanError, hd, hl, QuadraticMean.zeroPair, zero_dotProduct, Complex.zero_re,
    zero_div, sub_self]

end ClosedSurfaceR4.SmallModes

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes
variable {n : ℕ} {F : RField 4} {V : Set SmallModes.Base}

lemma combinedSeedMean_tsupport (P : Fin n → Expression) (δ τ ε : ℝ) (G : Base → Space)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V)
    (R : SupportedField (F := SmallModes.Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K))
    (q : ℕ) (b : SupportedField (F := ℝ) (modeSupport K)) (v w : SmallModes.Base) :
    tsupport (combinedSeedMean P δ τ ε G hF h K hKV R q b v w) ⊆ K := by
  apply closure_minimal _ K.isCompact.isClosed
  intro x hx
  by_contra hn
  have he : planeCoordinateIsometry x ∉ (modeSupport K : Set SmallModes.Base) := by
    rintro ⟨y, hy, hey⟩
    exact hn (planeCoordinateIsometry.injective hey ▸ hy)
  have hm : normalizedPerturbedMean δ τ hF h (modeSupport K) hKV R q b v w
      (planeCoordinateIsometry x) = 0 := by
    dsimp only [normalizedPerturbedMean]
    rw [SmallModes.seedMeanError_zero_outside τ (modeSupport K) _ _ _ v w _ he, mul_zero]
  let Z := coordinateCorrectedSeed δ τ hF h K hKV R q b
  have hZ : x ∉ tsupport Z := fun hz => hn (Z.tsupport_subset hz)
  have hp : normalizedPolynomialMean P δ ε G firstPhase Z τ 0 x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hz => hZ
      (normalizedPolynomialMean_tsupport P δ ε G firstPhase_smooth Z.contDiff τ 0 hz))
  exact hx (by change _ + _ = 0; rw [hm, hp, zero_add])

lemma combinedSeedMean_smooth {P : Fin n → Expression} {U : Set Base} {O : Set LowJet}
    (hU : IsOpen U) (hO : IsOpen O) (hP : ∀ l, (P l).SmoothCoeffs O)
    (δ τ ε : ℝ) {G : Base → Space} (hG : ContDiff ℝ ∞ G)
    (hGQ : Set.MapsTo (lowJet G) U O)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V)
    (R : SupportedField (F := SmallModes.Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K))
    (q : ℕ) (b : SupportedField (F := ℝ) (modeSupport K)) (v w : SmallModes.Base) :
    ContDiff ℝ ∞ (combinedSeedMean P δ τ ε G hF h K hKV R q b v w) :=
  ((normalizedPerturbedMean_smooth δ τ hF h K hKV R q b v w).comp planeCoordinateIsometry.contDiff).add
    (normalizedPolynomialMean_smooth hU hO hP hG firstPhase_smooth hGQ K hKU
      (coordinateCorrectedSeed δ τ hF h K hKV R q b) δ ε τ 0)

lemma combined_seed_mean_identity (P : Fin n → Expression) (δ τ ε : ℝ)
    (hδ : δ ≠ 0) (hτ : τ ≠ 0) (G : Base → Space)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V)
    (R : SupportedField (F := SmallModes.Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K))
    (q : ℕ) (b : SupportedField (F := ℝ) (modeSupport K)) (v w : SmallModes.Base)
    (x : Base) (hx : planeCoordinateIsometry x ∈ V) :
    let Z := correctedNormalSeed δ τ hF h (modeSupport K) hKV R q b
    let H := coordinateCorrectedSeed δ τ hF h K hKV R q b
    QuadraticMean.zeroPair (SmallModes.gradientAmplitude τ Z v (planeCoordinateIsometry x))
        (SmallModes.gradientAmplitude τ Z w (planeCoordinateIsometry x)) +
      quadraticMeanCoefficient P ε G firstPhase H τ 0 x =
        δ ^ 2 * (b (planeCoordinateIsometry x) ^ 2 * v.1 * w.1 +
          combinedSeedMean P δ τ ε G hF h K hKV R q b v w x) := by
  dsimp only
  rw [show correctedNormalSeed δ τ hF h (modeSupport K) hKV R q b =
      SmallModes.perturbedFreeLM τ (contDiff_complexify hF) (h.complexDomain hF) (modeSupport K) hKV R q
        (supportedFreeSeed δ τ hF h (modeSupport K) hKV b) from rfl,
    perturbed_seed_mean_identity δ τ hδ hτ hF h (modeSupport K) hKV R q b v w _ hx]
  dsimp only [combinedSeedMean, normalizedPolynomialMean]
  field_simp [hδ]
  ring

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
