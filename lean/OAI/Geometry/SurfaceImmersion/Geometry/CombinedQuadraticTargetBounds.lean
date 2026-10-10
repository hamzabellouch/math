import OAI.Geometry.SurfaceImmersion.Geometry.SupportedQuadraticFamily
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledQuadraticTargets
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledMetricQuadraticTargets

namespace OAI

/-! The actual combined doubled/mixed-phase targets have size delta squared.
The polynomial is evaluated in the original coordinates. -/
noncomputable section
open TopologicalSpace
open scoped ContDiff NNReal
namespace ClosedSurfaceR4.JetPolynomial.Perturbation
open PhaseMean RealModes WeightedEstimates

theorem combinedQuadraticTarget_bounds {n : ℕ} {ι : Type*}
    {U : Set Base} {O Q : Set LowJet} (hU : IsOpen U) (hO : IsOpen O)
    (hQ : IsCompact Q) (hQO : Q ⊆ O) (P : Fin 3 → Fin n → Expression)
    (hP : ∀ k j, (P k j).SmoothCoeffs O) (m : ℕ) (B F M A : ℝ)
    (hB : 1 ≤ B) (hF : 0 ≤ F) (hM : 0 ≤ M) (hA : 0 < A) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ {G : Base → Space} (hG : ContDiff ℝ ∞ G)
      (φ : ι → Base → ℝ) (hφ : ∀ i, ContDiff ℝ ∞ (φ i))
      (K : ι → Compacts Base) (H : ∀ i, SupportedField (F := Fin 4 → ℂ) (K i))
      (s : ℝ≥0) (δ τ ε : ℝ), 0 < δ → 0 < τ → 0 < (s : ℝ) → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → τ / s + ε / τ ^ tensorLoss P ≤ 1 →
      (hGQ : Set.MapsTo (lowJet G) U Q) →
      WeightedBound U s (m + tensorOrder P) B (lowJet G) →
      (∀ i, WeightedBound Set.univ s (m + tensorOrder P + 1) (A * (δ * τ)) (H i)) →
      (∀ i v, WeightedBound U s (m + tensorOrder P) F
        (fun x => fderiv ℝ (φ i) x (coordinateVector v))) →
      (∀ i v, ‖v‖ ≤ 1 → WeightedBound Set.univ s m M
        (SmallModes.coordDeriv v (coordinatePhase (φ i)))) →
      ∀ (l : QuadraticLabel ι) (hKU : (quadraticCompacts K l : Set Base) ⊆ U),
      WeightedBound Set.univ s m (δ ^ 2 * E)
        (combinedQuadraticTarget hU hO P hP hG φ hφ H
          (fun _ hx => hQO (hGQ hx)) l hKU ε τ 0) := by
  obtain ⟨E,hE,he⟩ := scaled_quadraticFamilyTensor_bound (ι := ι) hU hO hQ hQO P hP m B F hB hF
  let D := (4 : ℝ) * 2 ^ m * ((1 + 2 ^ m * M) * A) ^ 2
  refine ⟨D + E * A ^ 2,by dsimp [D]; positivity,?_⟩
  intro G hG φ hφ K H s δ τ ε hδ hτ hs hτs hs1 hε hε1 hsmall hGQ hGb hHb hφb hφm l hKU
  have hmetric := scaled_quadraticAmplitude_bound isOpen_univ
    (fun i => ((hφ i).comp planeCoordinateIsometry.symm.contDiff).contDiffOn)
    (fun i => ((H i).contDiff.comp planeCoordinateIsometry.symm.contDiff).contDiffOn)
    hτ hs hτs hδ.le hA.le hM m
    (fun i => weightedBound_comp_isometry planeCoordinateIsometry.symm (H i).contDiff
      ((hHb i).mono_order (by omega))) hφm l
  let f := polynomialQuadraticTarget hU hO hP hG hφ (fun i => (H i).contDiff)
    (fun x hx => hQO (hGQ hx)) (fun i => (K i).isCompact.isClosed) (fun i => (H i).tsupport_subset)
    l (quadraticCompacts K l) hKU (quadraticCompacts_coe K l).symm.subset ε τ 0
  have hpol : WeightedBound U s m (δ ^ 2 * (τ / s + ε / τ ^ tensorLoss P) * E * A ^ 2) f :=
    he G φ (fun i => H i) s δ τ ε A (tensorLoss P) hδ hτ hs hτs hs1 hε hε1 hA le_rfl hG hφ
      (fun i => (H i).contDiff) hGQ hGb
      (fun i => ((hHb i).mono_order (by omega)).restrict_open hU) hφb l 0 (by simp)
  have hp : WeightedBound Set.univ s m (δ ^ 2 * (E * A ^ 2)) f := by
    apply (hpol.extend_support hU (f.tsupport_subset.trans hKU) (by positivity)).mono_const
    calc
      _ = (τ / s + ε / τ ^ tensorLoss P) * (δ ^ 2 * E * A ^ 2) := by ring
      _ ≤ 1 * (δ ^ 2 * E * A ^ 2) := mul_le_mul_of_nonneg_right hsmall (by positivity)
      _ = _ := by ring
  have hpc := weightedBound_comp_isometry planeCoordinateIsometry.symm f.contDiff hp
  have hh := hmetric.add isOpen_univ.uniqueDiffOn s.coe_nonneg
    (metricQuadraticTarget φ hφ H τ l).contDiff.contDiffOn
    (f.contDiff.comp planeCoordinateIsometry.symm.contDiff).contDiffOn hpc
  convert hh using 1
  · dsimp [D]
    ring
  · rfl

end ClosedSurfaceR4.JetPolynomial.Perturbation

end

end OAI
