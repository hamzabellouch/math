import OAI.Combinatorics.Progressions.Probability.OneCubePairLaw
import OAI.Combinatorics.Progressions.Probability.PreparedModularGeneralCenteredLaw

namespace OAI

section

namespace Erdos3.VectorPolynomial

open Module Submodule MeasureTheory BooleanCubeKernel
open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G] [DecidableEq G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable (hb : ∀ j, span ℤ (Set.range (b j)) = projectedIntegerLattice (euclideanSubspace (U j)))
variable (o : ∀ j, OrthonormalBasis (I j) ℝ (euclideanSubspace (U j)))
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable (X : Type*) [Fintype X]
variable (poly : ∀ j, VectorPolynomial X ℝ (J j → ℝ))
variable (hmem : ∀ j e, coefficients (poly j) e ∈ U j)
variable [∀ j, IsZLattice ℝ (latticeSection (standardEuclideanLattice (J j)) (euclideanSubspace (U j)))]
variable (N : X → ℕ) (hN : ∀ t, 0 < N t)
variable {W τ ξ : ℝ} (hW : 0 ≤ W) (hτ : 0 < τ) (hξ : 0 < ξ)
variable (stride : X → ℕ)
variable (cells : Finset (ColumnResiduePattern (Option (LayerSamplerVariables G I n B)) X stride))

local notation "widths" => narrowTrimmedSpatialWidths (G := G)
  (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N

variable (hmass : 0 < ∑' z, selectedResidueSmoothWeight stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N) z)
variable (bases : Finset (X → ℤ)) (hbases : bases.Nonempty)
variable (htotal : 0 < selectedJointDensityMass bases stride cells
  (narrowTrimmedSpatialWidths (G := G) (J := PrincipalTupleIndex B (layerSamplerDegree I n)) W τ ξ N)
  (allocatedJointBaseDensity B U b hb o hR hσ S X poly hmem))

local notation "pathLaw" => allocatedOriginalPathLaw B U b hb o hR hσ S X poly hmem
  N hN hW hτ hξ stride cells hmass bases hbases htotal

theorem allocatedSlicedOneCube_eq_mean_square
    (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
    (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ) (f : (X → ℤ) → ℂ) :
    allocatedSlicedCubeSource (dim := 1) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f =
      (pathLaw).complexMean (fun z =>
        (‖𝔼 t ∈ integerBox H,
          f (jointIntegerPhysicalSite (commonStridePoint c step t) (z.1.val, z.2.val))‖ ^ 2 : ℝ)) := by
  rw [← allocatedOriginalPathLaw_sliced_cube_source B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal H hH c step f]
  apply congrArg (pathLaw).complexMean
  funext z
  exact normalizedSupportedCubeSum_one_self _ _

include hbases htotal in
theorem allocatedSlicedOneCube_re_nonneg
    (H : LayerSamplerVariables G I n B → ℕ) (hH : ∀ k, 0 < H k)
    (c : LayerSamplerVariables G I n B → ℤ) (step : ℕ) (f : (X → ℤ) → ℂ) :
    0 ≤ (allocatedSlicedCubeSource (dim := 1) B U b hb o hR hσ S X poly hmem
      N hN hW hτ hξ stride cells hmass bases H hH c step f).re := by
  rw [allocatedSlicedOneCube_eq_mean_square B U b hb o hR hσ S X poly hmem
    N hN hW hτ hξ stride cells hmass bases hbases htotal H hH c step f,
    FiniteProbabilityWeights.complexMean_re]
  exact (pathLaw).mean_nonneg (fun _ => by simp only [Complex.ofReal_re]; positivity)

end Erdos3.VectorPolynomial

end

end OAI
