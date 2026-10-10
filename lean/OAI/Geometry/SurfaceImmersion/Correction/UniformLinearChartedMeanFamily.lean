import OAI.Geometry.SurfaceImmersion.Correction.UniformLinearChartedMeanData
import OAI.Geometry.SurfaceImmersion.Correction.UniformGeometricMeanData
import OAI.Geometry.SurfaceImmersion.Correction.ChartedMeanFamilyData

namespace OAI

/-! A uniformly profiled three-phase mean family for nearby immersions. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal

namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseMean PhaseGeometry

def ChartedMeanData.atRadius {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {s : ℝ≥0} {G : Base → Space} {hG : ContDiff ℝ ∞ G}
    {φ : Base → ℝ} {S : Compacts Base}
    {c : PolynomialSolveData P ε G hG φ S τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    (d : ChartedMeanData c r ρ R reference) (r' : ℝ) (hr : r' ≤ r) :
    ChartedMeanData c r' ρ R reference where
  cutoff := d.cutoff
  form := d.form
  localBounds := d.localBounds.atRadius hr
  budgets := d.budgets
  compactJets := d.compactJets
  compact := d.compact
  subsetDomain := d.subsetDomain
  mapsJets := d.mapsJets
  B := d.B
  F := d.F
  oneLEB := d.oneLEB
  nonnegF := d.nonnegF
  jetsBound := d.jetsBound
  phaseBound := d.phaseBound

theorem ChartedMeanProfile.Fits.atRadius {n : ℕ} {P : Fin 3 → Fin n → Expression}
    {ε τ : ℝ} {s : ℝ≥0} {G : Base → Space} {hG : ContDiff ℝ ∞ G}
    {φ : Base → ℝ} {S : Compacts Base}
    {c : PolynomialSolveData P ε G hG φ S τ s}
    {r ρ R : ℝ} {reference : SmallModes.Base → Tensor}
    {p : ChartedMeanProfile P} {d : ChartedMeanData c r ρ R reference}
    (h : p.Fits d) (r' : ℝ) (hr : r' ≤ r) : p.Fits (d.atRadius r' hr) := by
  exact ⟨h.domain,h.coefficients,h.perturbation,h.coordinates,h.target,h.inverse,
    h.forms,h.cutoff,h.normal,h.jets,h.phase,h.range⟩

/-- Three local linear phases have one common perturbation radius and fixed
mean profiles. The maps, slow scale, frequency and smaller trial radius are
supplied only after those profiles have been chosen. -/
theorem uniform_linear_charted_mean_family_all_profiles
    {F : Base → Space} (hF : ContDiff ℝ ∞ F)
    (Ω U K : Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ j, IsOpen (Ω j)) (hU : ∀ j, IsOpen (U j))
    (hK : ∀ j, IsCompact (K j))
    (hUK : ∀ j, U j ⊆ K j) (hKΩ : ∀ j, K j ⊆ Ω j)
    (ξ : Fin 3 → SmallModes.Base) (hξ : ∀ j, ξ j ≠ 0)
    (hImm : ∀ j x, x ∈ Ω j → Function.Injective
      (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) x))
    (hgood : ∀ j x, x ∈ Ω j →
      Good (realSecondTensor (F ∘ planeCoordinateIsometry.symm) x) (ξ j))
    (S : Fin 3 → Compacts Base)
    (hS : ∀ j, (modeSupport (S j) : Set SmallModes.Base) ⊆ U j)
    {U₀ : Set Base} (hU₀ : IsOpen U₀) (K₀ : Compacts Base)
    (hU₀K : U₀ ⊆ K₀) (hSU₀ : ∀ j, (S j : Set Base) ⊆ U₀)
    (φ : Fin 3 → Base → ℝ) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hphase : ∀ j, coordinatePhase (φ j) = phaseLinear (ξ j))
    (ψ : ∀ j, SupportedField (F := ℝ)
      (chartSupport (linearPhaseChart (ξ j) (hξ j) (U j) (hU j))
        (modeSupport (S j)) (hS j)))
    (Q : Fin 3 → Tensor →L[ℝ] ℝ) {r ρ R : ℝ}
    {reference : SmallModes.Base → Tensor}
    (hmargin : ∀ j x, x ∈ U j → ρ + ‖Q j‖*r ≤ Q j (reference x) ∧
      Q j (reference x) ≤ R - ‖Q j‖*r)
    : ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (H : Fin 3 → ℕ → ℝ) (Pjet : ℕ → ℝ),
      (∀ j m, 1 ≤ H j m) → (∀ m, 0 ≤ Pjet m) →
      ∃ p : Fin 3 → ChartedMeanProfile emptyMetricPolynomial,
      (∀ j, (p j).U = U₀) ∧ (∀ j, (p j).O = univ) ∧
      (∀ j m, (p j).D m = 0) ∧
      ∀ (G : Base → Space) (_hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
        0 ≤ C₀ → C₀ < ρ₀ →
        WeightedBound univ 1 2 C₀
          ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
        ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
        (∀ j m, WeightedBound (linearPhaseChart (ξ j) (hξ j) (U j) (hU j)).target
          s m (H j m) (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
            (linearPhaseChart (ξ j) (hξ j) (U j) (hU j)).symm))) →
        (∀ m j, j ≤ m+2 → WeightedBound U₀ 1 j
          (Pjet m / (s : ℝ)^(j-2)) G) →
        ∀ (τ r' : ℝ), r' ≤ r →
        ∃ d : ChartedMeanFamilyData emptyMetricPolynomial 0 τ s r' ρ R reference,
          d.Fits p ∧ d.G = G ∧ d.phase = φ ∧ d.support = S ∧
          (∀ j, (d.solver j).e = linearPhaseChart (ξ j) (hξ j) (U j) (hU j)) ∧
          (∀ j x, (d.data j).cutoff x = ψ j x) ∧
          (∀ j, (d.data j).form = fun _ => Q j) := by
  classical
  choose a ha hall using fun j => uniform_linear_charted_mean_data_all_profiles
    hF (hΩ j) (hU j) (hK j) (hUK j) (hKΩ j) (hξ j) (hImm j) (hgood j)
    (S j) (hS j) hU₀ K₀ hU₀K (hSU₀ j) (hφ j) (hphase j) (ψ j) (Q j)
    (hmargin j)
  let ρ₀ := min (a 0) (min (a 1) (a 2))
  have hρ₀ : 0 < ρ₀ := lt_min (ha 0) (lt_min (ha 1) (ha 2))
  have hρa (j : Fin 3) : ρ₀ ≤ a j := by
    fin_cases j
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨ρ₀,hρ₀,?_⟩
  intro H Pjet hH hPjet
  choose p hpU hpO hpD hdata using fun j => hall j (H j) Pjet (hH j) hPjet
  refine ⟨p,hpU,hpO,hpD,?_⟩
  intro G hG C₀ hC₀ hCρ hclose s hs hs1 hjet hpref τ r' hr
  choose c d hfit he hcut hform using fun j => hdata j G hG C₀ hC₀
    (hCρ.trans_le (hρa j)) hclose s hs hs1 (hjet j) hpref τ
  refine ⟨{
    G := G
    smoothG := hG
    phase := φ
    support := S
    solver := c
    data := fun j => (d j).atRadius r' hr
  },?_,rfl,rfl,rfl,he,hcut,hform⟩
  exact fun j => (hfit j).atRadius r' hr

/-- Three local linear phases have one common perturbation radius and fixed
mean profiles. The maps, slow scale, frequency and smaller trial radius are
supplied only after those profiles have been chosen. -/
theorem uniform_linear_charted_mean_family
    {F : Base → Space} (hF : ContDiff ℝ ∞ F)
    (Ω U K : Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ j, IsOpen (Ω j)) (hU : ∀ j, IsOpen (U j))
    (hK : ∀ j, IsCompact (K j))
    (hUK : ∀ j, U j ⊆ K j) (hKΩ : ∀ j, K j ⊆ Ω j)
    (ξ : Fin 3 → SmallModes.Base) (hξ : ∀ j, ξ j ≠ 0)
    (hImm : ∀ j x, x ∈ Ω j → Function.Injective
      (fderiv ℝ (F ∘ planeCoordinateIsometry.symm) x))
    (hgood : ∀ j x, x ∈ Ω j →
      Good (realSecondTensor (F ∘ planeCoordinateIsometry.symm) x) (ξ j))
    (S : Fin 3 → Compacts Base)
    (hS : ∀ j, (modeSupport (S j) : Set SmallModes.Base) ⊆ U j)
    {U₀ : Set Base} (hU₀ : IsOpen U₀) (K₀ : Compacts Base)
    (hU₀K : U₀ ⊆ K₀) (hSU₀ : ∀ j, (S j : Set Base) ⊆ U₀)
    (φ : Fin 3 → Base → ℝ) (hφ : ∀ j, ContDiff ℝ ∞ (φ j))
    (hphase : ∀ j, coordinatePhase (φ j) = phaseLinear (ξ j))
    (ψ : ∀ j, SupportedField (F := ℝ)
      (chartSupport (linearPhaseChart (ξ j) (hξ j) (U j) (hU j))
        (modeSupport (S j)) (hS j)))
    (Q : Fin 3 → Tensor →L[ℝ] ℝ) {r ρ R : ℝ}
    {reference : SmallModes.Base → Tensor}
    (hmargin : ∀ j x, x ∈ U j → ρ + ‖Q j‖*r ≤ Q j (reference x) ∧
      Q j (reference x) ≤ R - ‖Q j‖*r)
    (H : Fin 3 → ℕ → ℝ) (Pjet : ℕ → ℝ)
    (hH : ∀ j m, 1 ≤ H j m) (hPjet : ∀ m, 0 ≤ Pjet m) :
    ∃ (ρ₀ : ℝ) (p : Fin 3 → ChartedMeanProfile emptyMetricPolynomial),
      0 < ρ₀ ∧ (∀ j, (p j).U = U₀) ∧ (∀ j, (p j).O = univ) ∧
      (∀ j m, (p j).D m = 0) ∧
      ∀ (G : Base → Space) (_hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
        0 ≤ C₀ → C₀ < ρ₀ →
        WeightedBound univ 1 2 C₀
          ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
        ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
        (∀ j m, WeightedBound (linearPhaseChart (ξ j) (hξ j) (U j) (hU j)).target
          s m (H j m) (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
            (linearPhaseChart (ξ j) (hξ j) (U j) (hU j)).symm))) →
        (∀ m j, j ≤ m+2 → WeightedBound U₀ 1 j
          (Pjet m / (s : ℝ)^(j-2)) G) →
        ∀ (τ r' : ℝ), r' ≤ r →
        ∃ d : ChartedMeanFamilyData emptyMetricPolynomial 0 τ s r' ρ R reference,
          d.Fits p ∧ d.G = G ∧ d.phase = φ ∧ d.support = S ∧
          (∀ j, (d.solver j).e = linearPhaseChart (ξ j) (hξ j) (U j) (hU j)) ∧
          (∀ j x, (d.data j).cutoff x = ψ j x) ∧
          (∀ j, (d.data j).form = fun _ => Q j) := by
  obtain ⟨ρ₀,hρ₀,hall⟩ := uniform_linear_charted_mean_family_all_profiles hF Ω U K hΩ hU hK
    hUK hKΩ ξ hξ hImm hgood S hS hU₀ K₀ hU₀K hSU₀ φ hφ hphase ψ Q hmargin
  obtain ⟨p,hU,hO,hD,hdata⟩ := hall H Pjet hH hPjet
  exact ⟨ρ₀,p,hρ₀,hU,hO,hD,hdata⟩

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
