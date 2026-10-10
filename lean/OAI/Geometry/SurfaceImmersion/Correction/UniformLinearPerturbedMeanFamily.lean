import OAI.Geometry.SurfaceImmersion.Correction.UniformLinearPerturbedMeanData
import OAI.Geometry.SurfaceImmersion.Correction.UniformLinearChartedMeanFamily

namespace OAI

/-! A three-phase perturbed mean family with a common geometric radius.
The radius precedes all derivative profiles, and the actual family retains
the fixed phase charts, cutoffs and coefficient forms. -/
noncomputable section
open Set TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open WeightedEstimates RealModes PhaseMean PhaseGeometry

theorem uniform_linear_perturbed_mean_family_all_profiles {n : ℕ}
    (P : Fin 3 → Fin n → Expression) (hP : ∀ k j, (P k j).SmoothCoeffs univ)
    {F : Base → Space} (hF : ContDiff ℝ ∞ F)
    (Ω U K : Fin 3 → Set SmallModes.Base)
    (hΩ : ∀ j, IsOpen (Ω j)) (hU : ∀ j, IsOpen (U j))
    (hK : ∀ j, IsCompact (K j)) (hUK : ∀ j, U j ⊆ K j) (hKΩ : ∀ j, K j ⊆ Ω j)
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
    (hmargin : ∀ j x, x ∈ U j → ρ + ‖Q j‖ * r ≤ Q j (reference x) ∧
      Q j (reference x) ≤ R - ‖Q j‖ * r) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ (H : Fin 3 → ℕ → ℝ) (Pjet : ℕ → ℝ),
      (∀ j m, 1 ≤ H j m) → (∀ m, 0 ≤ Pjet m) →
      ∃ p : Fin 3 → ChartedMeanProfile P,
        (∀ j, (p j).U = U₀) ∧ (∀ j, (p j).O = univ) ∧
        (∀ j m, 0 ≤ (p j).D m) ∧
      ∀ (G : Base → Space) (_hG : ContDiff ℝ ∞ G) (C₀ : ℝ),
      0 ≤ C₀ → C₀ < ρ₀ →
      WeightedBound univ 1 2 C₀
        ((G ∘ planeCoordinateIsometry.symm) - (F ∘ planeCoordinateIsometry.symm)) →
      ∀ s : ℝ≥0, 0 < (s : ℝ) → s ≤ 1 →
      (∀ j m, WeightedBound (linearPhaseChart (ξ j) (hξ j) (U j) (hU j)).target
        s m (H j m) (realTwoJet ((G ∘ planeCoordinateIsometry.symm) ∘
          (linearPhaseChart (ξ j) (hξ j) (U j) (hU j)).symm))) →
      (∀ m j, j ≤ m + 2 → WeightedBound U₀ 1 j
        (Pjet m / (s : ℝ) ^ (j - 2)) G) →
      ∀ (τ ε r' : ℝ), r' ≤ r → 0 < τ → τ ≤ s → 0 ≤ ε → ε ≤ 1 →
      ∃ d : ChartedMeanFamilyData P ε τ s r' ρ R reference,
        d.Fits p ∧ d.G = G ∧ d.phase = φ ∧ d.support = S ∧
        (∀ j, (d.solver j).e = linearPhaseChart (ξ j) (hξ j) (U j) (hU j)) ∧
        (∀ j x, (d.data j).cutoff x = ψ j x) ∧
        (∀ j, (d.data j).form = fun _ => Q j) := by
  classical
  choose a ha hall using fun j => uniform_linear_perturbed_mean_data_all_profiles
    P hP hF (hΩ j) (hU j) (hK j) (hUK j) (hKΩ j) (hξ j) (hImm j) (hgood j)
    (S j) (hS j) hU₀ K₀ hU₀K (hSU₀ j) (hφ j) (hphase j) (ψ j) (Q j) (hmargin j)
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
  intro G hG C₀ hC₀ hCρ hclose s hs hs1 hjet hpref τ ε r' hr hτ hτs hε hε1
  choose c d hfit he hcut hform using fun j => hdata j G hG C₀ hC₀
    (hCρ.trans_le (hρa j)) hclose s hs hs1 (hjet j) hpref τ ε hτ hτs hε hε1
  refine ⟨{
    G := G
    smoothG := hG
    phase := φ
    support := S
    solver := c
    data := fun j => (d j).atRadius r' hr
  },?_,rfl,rfl,rfl,he,hcut,hform⟩
  exact fun j => (hfit j).atRadius r' hr

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
