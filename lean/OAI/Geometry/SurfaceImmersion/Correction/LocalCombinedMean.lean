import OAI.Geometry.SurfaceImmersion.Geometry.SupportedTrialAmplitude
import OAI.Geometry.SurfaceImmersion.Atlas.CombinedTensorBounds

namespace OAI

/-! The actual combined mean operator in a phase chart. Its amplitudes are
constructed from the trial tensor and the fixed positive coefficient forms. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes
open PhaseMean (firstDirection secondDirection)
variable {n : ℕ} {F : RField 4} {V : Set SmallModes.Base}

lemma combinedMeanTensor_smooth {P : Fin 3 → Fin n → Expression}
    {U : Set Base} {O : Set LowJet} (hU : IsOpen U) (hO : IsOpen O)
    (hP : ∀ i l, (P i l).SmoothCoeffs O) (δ τ ε : ℝ)
    {G : Base → Space} (hG : ContDiff ℝ ∞ G) (hGQ : Set.MapsTo (lowJet G) U O)
    (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKU : (K : Set Base) ⊆ U)
    (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V)
    (R : SupportedField (F := SmallModes.Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K))
    (q : ℕ) (b : SupportedField (F := ℝ) (modeSupport K)) :
    ContDiff ℝ ∞ (combinedMeanTensor P δ τ ε G hF h K hKV R q b) :=
  contDiff_pi.mpr fun i => combinedSeedMean_smooth hU hO (hP i) δ τ ε hG hGQ
    hF h K hKU hKV R q b (firstDirection i) (secondDirection i)

lemma combinedMeanTensor_tsupport (P : Fin 3 → Fin n → Expression) (δ τ ε : ℝ)
    (G : Base → Space) (hF : ContDiff ℝ ∞ F) (h : RealModeDomain F V)
    (K : Compacts Base) (hKV : (modeSupport K : Set SmallModes.Base) ⊆ V)
    (R : SupportedField (F := SmallModes.Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K))
    (q : ℕ) (b : SupportedField (F := ℝ) (modeSupport K)) :
    tsupport (combinedMeanTensor P δ τ ε G hF h K hKV R q b) ⊆ K := by
  apply closure_minimal _ K.isCompact.isClosed
  intro x hx
  by_contra hn
  apply hx
  funext i
  change combinedSeedMean (P i) δ τ ε G hF h K hKV R q b (firstDirection i) (secondDirection i) x = 0
  exact image_eq_zero_of_notMem_tsupport (fun hz => hn
    (combinedSeedMean_tsupport (P i) δ τ ε G hF h K hKV R q b (firstDirection i) (secondDirection i) hz))

end ClosedSurfaceR4.JetPolynomial.Perturbation

namespace ClosedSurfaceR4.PhaseMean
open SmallModes RealModes WeightedEstimates
open JetPolynomial (SupportedField)
open JetPolynomial.Perturbation (modeSupport combinedMeanTensor)
variable {n : ℕ} {U V : Set Base} {s r ρ R₀ : ℝ} {reference : Base → Tensor}
  {F : RField 4} {K : Compacts JetPolynomial.Base}
  {ψ : SupportedField (F := ℝ) (modeSupport K)}
  {Q : Base → Tensor →L[ℝ] ℝ} {χ e : Base → Base}

def localCombinedMean (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (hρ : 0 < ρ) (hKV : (modeSupport K : Set Base) ⊆ V)
    (P : Fin 3 → Fin n → JetPolynomial.Expression) (G : JetPolynomial.Base → JetPolynomial.Space)
    (δ τ ε : ℝ) (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K)) (q : ℕ) (A : Base → Tensor) : Base → Tensor :=
  fun x => pullbackField χ x
    (combinedMeanTensor P δ τ ε G h.smoothF h.domain K hKV R q
      (supportedTrialAmplitude h hρ hKV A) (JetPolynomial.planeCoordinateIsometry.symm (χ x)))

lemma localCombinedMean_smooth (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (hρ : 0 < ρ) (hKV : (modeSupport K : Set Base) ⊆ V)
    {P : Fin 3 → Fin n → JetPolynomial.Expression} {J : Set JetPolynomial.Base}
    {O : Set JetPolynomial.LowJet} (hJ : IsOpen J) (hO : IsOpen O)
    (hP : ∀ i l, (P i l).SmoothCoeffs O) {G : JetPolynomial.Base → JetPolynomial.Space}
    (hG : ContDiff ℝ ∞ G) (hGQ : Set.MapsTo (JetPolynomial.lowJet G) J O)
    (hKJ : (K : Set JetPolynomial.Base) ⊆ J)
    (δ τ ε : ℝ) (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K)) (q : ℕ) (A : Base → Tensor) :
    ContDiffOn ℝ ∞ (localCombinedMean h hρ hKV P G δ τ ε R q A) U := by
  have ht := JetPolynomial.Perturbation.combinedMeanTensor_smooth hJ hO hP δ τ ε hG hGQ
    h.smoothF h.domain K hKJ hKV R q (supportedTrialAmplitude h hρ hKV A)
  exact h.smoothPullback.clm_apply
    ((ht.comp JetPolynomial.planeCoordinateIsometry.symm.contDiff).comp_contDiffOn h.smoothChi)

lemma localCombinedMean_vanishes (h : LocalBounds U V s r ρ R₀ reference F ψ Q χ e)
    (hρ : 0 < ρ) (hKV : (modeSupport K : Set Base) ⊆ V) {S : Set Base}
    (hsp : ∀ x ∈ U, χ x ∈ (modeSupport K : Set Base) → x ∈ S)
    (P : Fin 3 → Fin n → JetPolynomial.Expression) (G : JetPolynomial.Base → JetPolynomial.Space)
    (δ τ ε : ℝ) (R : SupportedField (F := Ambient 4) (modeSupport K) →ₗ[ℝ]
      SupportedField (F := Fin 3 → ℂ) (modeSupport K)) (q : ℕ) (A : Base → Tensor) :
    ∀ x ∈ U, x ∉ S → localCombinedMean h hρ hKV P G δ τ ε R q A x = 0 := by
  intro x hx hn
  have hk : JetPolynomial.planeCoordinateIsometry.symm (χ x) ∉ (K : Set JetPolynomial.Base) := by
    intro hk
    apply hn (hsp x hx _)
    exact ⟨_, hk, JetPolynomial.planeCoordinateIsometry.apply_symm_apply (χ x)⟩
  have hz := image_eq_zero_of_notMem_tsupport (fun ht => hk
    (JetPolynomial.Perturbation.combinedMeanTensor_tsupport P δ τ ε G h.smoothF h.domain K hKV R q
      (supportedTrialAmplitude h hρ hKV A) ht))
  change pullbackField χ x (combinedMeanTensor P δ τ ε G h.smoothF h.domain K hKV R q
    (supportedTrialAmplitude h hρ hKV A) _) = 0
  rw [hz, map_zero]

end ClosedSurfaceR4.PhaseMean

end

end OAI
