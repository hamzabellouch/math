import OAI.Geometry.SurfaceImmersion.Correction.PhaseMeanDomains
import OAI.Geometry.SurfaceImmersion.Atlas.AtlasSupportedWeights
import OAI.Geometry.Immersion.ClosedSurface.AtlasPartition
import OAI.Geometry.SurfaceImmersion.Geometry.VectorReadBounds

namespace OAI

/-! Fixed mean domains and common margins obtained from compact atlas geometry. -/
noncomputable section
open Set Manifold TopologicalSpace
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean PhaseGeometry WeightedEstimates RealModes
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

structure PhaseMeanDomains (F : M → Space) (Q : A.centers → PhaseBasis)
    (reference : A.centers → SmallModes.Base → Tensor) where
  r : ℝ
  ρ : ℝ
  R : ℝ
  r_pos : 0 < r
  ρ_pos : 0 < ρ
  R_pos : 0 < R
  Ω : A.centers → Fin 3 → Set SmallModes.Base
  U : A.centers → Fin 3 → Set SmallModes.Base
  K : A.centers → Fin 3 → Set SmallModes.Base
  openΩ : ∀ i j, IsOpen (Ω i j)
  openU : ∀ i j, IsOpen (U i j)
  compactK : ∀ i j, IsCompact (K i j)
  UK : ∀ i j, U i j ⊆ K i j
  KΩ : ∀ i j, K i j ⊆ Ω i j
  support : ∀ i j, (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) ⊆ U i j
  immersion : ∀ i j x, x ∈ Ω i j →
    Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x)
  good : ∀ i j x, x ∈ Ω i j →
    Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j)
  U₀ : A.centers → Set JetPolynomial.Base
  K₀ : A.centers → Compacts JetPolynomial.Base
  openU₀ : ∀ i, IsOpen (U₀ i)
  U₀K₀ : ∀ i, U₀ i ⊆ K₀ i
  supportU₀ : ∀ i, (A.chartWeightCompact i : Set JetPolynomial.Base) ⊆ U₀ i
  margin : ∀ i j x, x ∈ U i j →
    ρ + ‖(Q i).Q j‖*r ≤ (Q i).Q j (reference i x) ∧
      (Q i).Q j (reference i x) ≤ R - ‖(Q i).Q j‖*r

/-- Strict positivity and good geometry on the actual compact supports
supply all domain and margin data for the mean constructor. -/
theorem exists_phaseMeanDomains (F : M → Space)
    (hF : ContMDiff planeModel spaceModel ∞ F) (Q : A.centers → PhaseBasis)
    (hImm : ∀ i x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Function.Injective (fderiv ℝ (spaceCoordinates ∘ A.vectorPlaneRead i F) x))
    (hgood : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      Good (realSecondTensor (spaceCoordinates ∘ A.vectorPlaneRead i F) x) ((Q i).ξ j))
    (reference : A.centers → SmallModes.Base → Tensor)
    (href : ∀ i, Continuous (reference i))
    (hpos : ∀ i j x, x ∈ (modeSupport (A.chartWeightCompact i) : Set SmallModes.Base) →
      0 < (Q i).Q j (reference i x)) : Nonempty (A.PhaseMeanDomains F Q reference) := by
  classical
  choose r ρ R hr hρ hR U K Ω hU hK hΩ hs hUK hKΩ hg hm using fun i : A.centers =>
    compact_phase_mean_domains
      (spaceCoordinates.contDiff.comp (A.vectorPlaneRead_smooth i hF))
      (modeSupport (A.chartWeightCompact i)) (hImm i) (Q i).ξ (hgood i)
      (Q i).Q (reference i) (href i) (hpos i)
  obtain ⟨r₀,hr₀,_,hrr⟩ := finite_positive_threshold r hr
  obtain ⟨ρ₀,hρ₀,_,hρρ⟩ := finite_positive_threshold ρ hρ
  let R₀ : ℝ := 1 + ∑ i : A.centers, R i
  have hR₀ : 0 < R₀ := by
    have hsum : 0 ≤ ∑ i : A.centers, R i := Finset.sum_nonneg (fun i _ => (hR i).le)
    exact add_pos_of_pos_of_nonneg zero_lt_one hsum
  have hRR (i : A.centers) : R i ≤ R₀ := by
    have hh := Finset.single_le_sum (fun j _ => (hR j).le) (Finset.mem_univ i)
    exact hh.trans (le_add_of_nonneg_left zero_le_one)
  choose U₀ hU₀ hKU₀ hUc₀ _ using fun i : A.centers =>
    CollarVelocity.compact_open_thickening (A.chartWeightCompact i).isCompact
      isOpen_univ (subset_univ _)
  refine ⟨{
    r := r₀, ρ := ρ₀, R := R₀, r_pos := hr₀, ρ_pos := hρ₀, R_pos := hR₀
    Ω := Ω, U := U, K := K, openΩ := hΩ, openU := hU, compactK := hK
    UK := hUK, KΩ := hKΩ, support := hs
    immersion := fun i j x hx => (hg i j x hx).1
    good := fun i j x hx => (hg i j x hx).2
    U₀ := U₀, K₀ := fun i => ⟨closure (U₀ i),hUc₀ i⟩
    openU₀ := hU₀, U₀K₀ := fun _ => subset_closure, supportU₀ := hKU₀
    margin := ?_
  }⟩
  intro i j x hx
  have hh := hm i j x (hUK i j hx)
  have hn := mul_le_mul_of_nonneg_left (hrr i) (norm_nonneg ((Q i).Q j))
  have hl := hρρ i
  have hu := hRR i
  constructor <;> linarith

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
