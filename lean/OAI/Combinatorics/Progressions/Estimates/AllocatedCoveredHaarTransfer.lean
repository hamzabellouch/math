import OAI.Combinatorics.Progressions.Sampling.AllocatedCoefficientSampler
import OAI.Combinatorics.Progressions.Sampling.ControlledJointGrid

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory Module Submodule
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (Q : Fin m → Type*) [∀ j, Fintype (Q j)]
variable (bW : ∀ j, Basis (Q j) ℤ
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))))
variable (d : ℕ) [NeZero d]
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable [CompactSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [MeasurableSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable [BorelSpace (CoefficientTorus (K := LayerSamplerVariables G I n B) U)]
variable (μ : Measure (CoefficientTorus (K := LayerSamplerVariables G I n B) U))
variable [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
variable (ν : ∀ j, Measure (euclideanSubspace (U j) ⧸
  (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j))).toAddSubgroup))
variable [∀ j, (ν j).IsAddLeftInvariant] [∀ j, IsProbabilityMeasure (ν j)]
variable (hσ1 : ∀ j, σ j ≤ 1) (C : Fin m → ℝ) (hC : ∀ j, 0 ≤ C j)
variable (hchart : ∀ j v, ‖(normalizedOrthogonalChart (euclideanSubspace (U j)) (b j)).symm v‖ ≤ C j * ‖v‖)
variable (hsmall : ∀ j, C j * ((Fintype.card (I j) : ℝ) + 1) * R j ≤ 1 / 4)

local notation "source" => allocatedCoefficientSource B U b hR hσ S
local notation "deck" => PMF.uniformOfFintype (CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d)
local notation "sample" => (fun p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
  CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d =>
  canonicalCoefficientDeckSample U bW b hb o d (Nat.pos_of_ne_zero (NeZero.ne d)) (Prod.fst p) (Prod.snd p))
local notation "density" => (fun t => allocatedCoefficientDensity B U b hb o hR hσ S
  (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d t))

omit [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))] in
theorem allocatedCoveredDeck_relabel
    [Fintype (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d).ker] :
    ((source).prod (deck).toMeasure).map sample =
      finiteKernelLiftLaw (G := CoefficientTorus (K := LayerSamplerVariables G I n B) U)
        (H := CoefficientTorus (K := LayerSamplerVariables G I n B) U) (quotientIntegerCover
        (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d)
        source (canonicalCoefficientCoverLift U b hb o d) := by
  let : IsProbabilityMeasure source := allocatedCoefficientSource_probability B U b hR hσ S
  let : SigmaFinite source := IsFiniteMeasure.toSigmaFinite _
  let : SFinite source := inferInstance
  let e : CoefficientDeckResidues (K := LayerSamplerVariables G I n B) Q d ≃
      (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d).ker :=
    (coefficientDeckKernelEquiv (K := LayerSamplerVariables G I n B) (J := J) (B := Q)
      U bW d (Nat.pos_of_ne_zero (NeZero.ne d))).toEquiv
  have he : Measurable e := measurable_of_finite _
  have hm : (deck).toMeasure.map e =
      (PMF.uniformOfFintype
        (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d).ker).toMeasure := by
    rw [PMF.toMeasure_map e _ he, uniformPMF_map_equiv e]
  have hp := Measure.map_prod_map source (deck).toMeasure measurable_id he
  rw [Measure.map_id, hm] at hp
  have hg : Measurable (fun p : CoefficientSamplerArrays (K := LayerSamplerVariables G I n B) I n ×
      (quotientIntegerCover (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d).ker =>
        canonicalCoefficientCoverLift U b hb o d p.1 + p.2.val) :=
    ((canonicalCoefficientCoverLift_measurable (K := LayerSamplerVariables G I n B)
      U b hb o d).comp measurable_fst).add (measurable_subtype_coe.comp measurable_snd)
  rw [finiteKernelLiftLaw, hp, Measure.map_map hg (measurable_id.prodMap he)]
  rfl

include ν hσ1 hC hchart hsmall

theorem allocatedCoefficientCover_density :
    letI := coefficientCoverKernelFintype (K := LayerSamplerVariables G I n B) U d
      (Nat.pos_of_ne_zero (NeZero.ne d))
    finiteKernelLiftLaw (G := CoefficientTorus (K := LayerSamplerVariables G I n B) U)
      (H := CoefficientTorus (K := LayerSamplerVariables G I n B) U) (quotientIntegerCover
      (coefficientIntegerLattice (K := LayerSamplerVariables G I n B) U) d)
      source (canonicalCoefficientCoverLift U b hb o d) = realDensityMeasure μ density := by
  have hw := allocatedLayerWidths_pos B U b hR hσ S
  have hs := allocatedLayerColumns_chart B U b hR hσ S o hσ1 C hC hchart hsmall
  exact canonicalCoefficientCoverLaw (K := LayerSamplerVariables G I n B)
    (m := m) (J := J) (I := I) (n := n) U b hb o μ ν
    (allocatedLayerCenters B U b S) (allocatedLayerWidths B U b S)
    (allocatedLayerIntegerPMFs B U b hR hσ S) hw hs d (Nat.pos_of_ne_zero (NeZero.ne d))

theorem allocatedCoveredHaar_law :
    ((source).prod (deck).toMeasure).map sample = realDensityMeasure μ density := by
  let _ := coefficientCoverKernelFintype (K := LayerSamplerVariables G I n B) U d
    (Nat.pos_of_ne_zero (NeZero.ne d))
  exact (allocatedCoveredDeck_relabel B U b hb o hR hσ S Q bW d).trans
    (allocatedCoefficientCover_density B U b hb o hR hσ S d μ ν hσ1 C hC hchart hsmall)

theorem allocatedCoveredHaar_integral
    (F : CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℂ) (hF : Measurable F) :
    (∫ p, F (sample p) ∂(source).prod (deck).toMeasure) =
      ∫ t, (density t : ℂ) * F t ∂μ := by
  have hD : Measurable density :=
    (canonicalCoefficientDensity_measurable (K := LayerSamplerVariables G I n B) U b hb o _ _ _).comp
      (quotientIntegerCover_continuous _ d).measurable
  have hD0 (t) : 0 ≤ density t :=
    canonicalCoefficientDensity_nonneg (K := LayerSamplerVariables G I n B) U b hb o _ _ _
      (allocatedLayerWidths_pos B U b hR hσ S) _
  rw [← realDensityMeasure_integral_complex μ density hD hD0,
    ← allocatedCoveredHaar_law B U b hb o hR hσ S Q bW d μ ν hσ1 C hC hchart hsmall]
  exact (integral_map (canonicalCoefficientDeckSample_measurable
    (K := LayerSamplerVariables G I n B) U bW b hb o d).aemeasurable
    hF.aestronglyMeasurable).symm

theorem allocatedCoveredHaar_finite_mean {T : Type*} [Fintype T]
    (w : FiniteProbabilityWeights T)
    (F : T → CoefficientTorus (K := LayerSamplerVariables G I n B) U → ℂ)
    (hF : ∀ t, Measurable (F t)) :
    (∫ p, w.complexMean (fun t => F t (sample p)) ∂(source).prod (deck).toMeasure) =
      ∫ a, (density a : ℂ) * w.complexMean (fun t => F t a) ∂μ :=
  allocatedCoveredHaar_integral B U b hb o hR hσ S Q bW d μ ν hσ1 C hC hchart hsmall
    _ (w.complexMean_measurable _ hF)

theorem allocatedCoveredDensity_finite_mean {T Y : Type*} [Fintype T] [MeasurableSpace Y]
    (w : FiniteProbabilityWeights T)
    (ψ : T → CoefficientTorus (K := LayerSamplerVariables G I n B) U → Y)
    (hψ : ∀ t, Measurable (ψ t)) (ξ : Measure Y)
    (g : T → Y → ℝ) (hg : ∀ t, Measurable (g t)) (hg0 : ∀ t z, 0 ≤ g t z)
    (hlaw : ∀ t, (realDensityMeasure μ density).map (ψ t) = realDensityMeasure ξ (g t))
    (F : T → Y → ℂ) (hF : ∀ t, Measurable (F t))
    {K : ℝ} (hbound : ∀ t z, ‖F t z‖ ≤ K) :
    (∫ p, w.complexMean (fun t => F t (ψ t (sample p))) ∂(source).prod (deck).toMeasure) =
      w.complexMean (fun t => ∫ z, (g t z : ℂ) * F t z ∂ξ) := by
  let : IsProbabilityMeasure source := allocatedCoefficientSource_probability B U b hR hσ S
  have hs := canonicalCoefficientDeckSample_measurable (K := LayerSamplerVariables G I n B) U bW b hb o d
  have hi (t) : Integrable (fun p => F t (ψ t (sample p))) ((source).prod (deck).toMeasure) :=
    Integrable.of_bound ((hF t).comp ((hψ t).comp hs)).aestronglyMeasurable K
      (ae_of_all _ (fun p => hbound t _))
  rw [w.integral_complexMean _ _ hi]
  apply congrArg w.complexMean
  funext t
  have hm : ((source).prod (deck).toMeasure).map (ψ t ∘ sample) = realDensityMeasure ξ (g t) := by
    rw [← Measure.map_map (hψ t) hs,
      allocatedCoveredHaar_law B U b hb o hR hσ S Q bW d μ ν hσ1 C hC hchart hsmall]
    exact hlaw t
  rw [← realDensityMeasure_integral_complex ξ (g t) (hg t) (hg0 t), ← hm]
  exact (integral_map ((hψ t).comp hs).aemeasurable (hF t).aestronglyMeasurable).symm

end Erdos3.VectorPolynomial

end

end OAI
