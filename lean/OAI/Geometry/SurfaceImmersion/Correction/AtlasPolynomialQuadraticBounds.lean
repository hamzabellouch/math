import OAI.Geometry.SurfaceImmersion.Atlas.AtlasQuadraticBounds
import OAI.Geometry.SurfaceImmersion.Atlas.CutoffQuadraticBounds
import OAI.Geometry.SurfaceImmersion.Correction.AtlasCombinedModes
import OAI.Geometry.SurfaceImmersion.Geometry.ScaledQuadraticTargets

namespace OAI

/-! Uniform delta-squared bounds for the actual global quadratic targets. -/
noncomputable section
open Set Manifold Bundle
open scoped ContDiff Manifold Topology BigOperators NNReal
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial JetPolynomial.Perturbation PhaseMean

local instance polynomialQuadraticBoundsFiberNormed : NormedAddCommGroup TensorFiber := inferInstance
local instance polynomialQuadraticBoundsFiberSpace : NormedSpace ℝ TensorFiber := inferInstance
variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M] [CompactSpace M]
local instance polynomialQuadraticBoundsDualAdd : ∀ p : M, ContinuousAdd (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousAdd (Plane →L[ℝ] ℝ))
local instance polynomialQuadraticBoundsDualSmul : ∀ p : M, ContinuousSMul ℝ (TangentSpace planeModel p →L[ℝ] ℝ) :=
  fun _ => inferInstanceAs (ContinuousSMul ℝ (Plane →L[ℝ] ℝ))
local instance polynomialQuadraticBoundsSectionNormed (p : M) : NormedAddCommGroup (CovariantTwoTensor p) :=
  inferInstanceAs (NormedAddCommGroup TensorFiber)
local instance polynomialQuadraticBoundsSectionSpace (p : M) : NormedSpace ℝ (CovariantTwoTensor p) :=
  inferInstanceAs (NormedSpace ℝ TensorFiber)

namespace SmoothingAtlas
variable (A : SmoothingAtlas M)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]


omit [Fintype ι] [DecidableEq ι] in
theorem globalPolynomialQuadraticTarget_bound {n : ℕ}
    (Q : A.centers → Fin 3 → Fin n → Expression)
    (hQ : ∀ i k l, (Q i k l).SmoothCoeffs univ) (k : A.centers)
    {U : Set Base} (hU : IsOpen U) (hKU : (A.chartWeightCompact k : Set Base) ⊆ U)
    {K : Set LowJet} (hK : IsCompact K) (m : ℕ)
    (B F₀ A₀ P₀ : ℝ) (hB : 1 ≤ B) (hF₀ : 0 ≤ F₀) (hA₀ : 0 < A₀) (hP₀ : 0 ≤ P₀) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ (F : M → Space) (hF : ContMDiff planeModel spaceModel ∞ F)
      (φ : ι → M → ℝ) (Z : ι → M → Fin 4 → ℂ)
      (hφ : ∀ a, ContMDiff planeModel 𝓘(ℝ) ∞ (φ a))
      (hZ : ∀ a, ContMDiff planeModel 𝓘(ℝ,Fin 4 → ℂ) ∞ (Z a))
      (s δ τ ε : ℝ), 0 < δ → 0 < τ → 0 < s → τ ≤ s → s ≤ 1 →
      0 ≤ ε → ε ≤ 1 → τ/s+ε/τ^tensorLoss (Q k) ≤ 1 →
      MapsTo (lowJet (A.jetChartMap k F)) U K →
      WeightedEstimates.WeightedBound U s (m+tensorOrder (Q k)) B (lowJet (A.jetChartMap k F)) →
      (∀ a, WeightedEstimates.WeightedBound univ s (m+tensorOrder (Q k)+1)
        (A₀*(δ*τ)) (A.vectorChartRead k (Z a))) →
      (∀ a v, WeightedEstimates.WeightedBound U s (m+tensorOrder (Q k)) F₀
        (fun x => fderiv ℝ (A.vectorChartRead k (φ a)) x (coordinateVector v))) →
      (∀ a v, ‖v‖ ≤ 1 → WeightedEstimates.WeightedBound univ s m P₀
        (SmallModes.coordDeriv v (A.vectorPlaneRead k (φ a)))) →
      ∀ l : RealModes.QuadraticLabel ι, WeightedEstimates.WeightedBound univ s m (E*δ^2)
        (A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ k l) := by
  obtain ⟨M,hM,hm⟩ := A.globalQuadraticTarget_bound (ι := ι) k m A₀ P₀
  obtain ⟨D,hD,hd⟩ := A.planeWeight_square_bound k m
  obtain ⟨E,hE,he⟩ := scaled_quadraticFamilyTensor_bound (ι := ι)
    hU isOpen_univ hK (subset_univ _) (Q k) (hQ k) m B F₀ hB hF₀
  let C := 2^m*D*(E*A₀^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨M+C,add_nonneg hM hC,?_⟩
  intro F hF φ Z hφ hZ s δ τ ε hδ hτ hs hτs hs1 hε hε1 hsmall hjet hb hZb hφb hφm l
  have hpoly := he (A.jetChartMap k F) (fun a => A.vectorChartRead k (φ a))
    (fun a => A.vectorChartRead k (Z a)) s δ τ ε A₀ (tensorLoss (Q k))
    hδ hτ hs hτs hs1 hε hε1 hA₀ le_rfl (A.jetChartMap_smooth k hF)
    (fun a => A.vectorChartRead_smooth k (hφ a)) (fun a => A.vectorChartRead_smooth k (hZ a))
    hjet hb (fun a => ((hZb a).mono_order (by omega)).restrict_open hU) hφb l 0 (by simp)
  have hpoly' := hpoly.mono_const
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsmall (sq_nonneg δ)) hE) (sq_nonneg A₀))
  simp only [mul_one] at hpoly'
  have hsm : ContDiff ℝ ∞ (quadraticFamilyTensor (Q k) ε (A.jetChartMap k F)
      (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l) := by
    apply contDiff_pi.mpr
    intro j
    exact contDiffOn_univ.mp (quadraticFamilyCoefficient_smooth isOpen_univ (hQ k j)
      (A.jetChartMap_smooth k hF) (fun a => A.vectorChartRead_smooth k (hφ a))
      (fun a => A.vectorChartRead_smooth k (hZ a)) (fun _ _ => mem_univ _) ε τ 0 l)
  let V := planeCoordinateIsometry.symm ⁻¹' U
  have hV : IsOpen V := hU.preimage planeCoordinateIsometry.symm.continuous
  have hpc := weightedBound_comp_isometry_on planeCoordinateIsometry.symm hU hsm hpoly'
  have hcs : ContDiff ℝ ∞ (coordinateQuadraticCoefficient (Q k) ε (A.jetChartMap k F)
      (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l) :=
    hsm.comp planeCoordinateIsometry.symm.contDiff
  let T := fun x => (A.planeWeight k x)^2 •
    coordinateQuadraticCoefficient (Q k) ε (A.jetChartMap k F)
      (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l x
  have hT : ContDiff ℝ ∞ T := ((A.planeWeight_smooth k).pow 2).smul hcs
  have hprod := ((hd s hs hs1).restrict_open hV).smul_real hV.uniqueDiffOn hs.le hD
    (by positivity : 0 ≤ δ^2*E*A₀^2) ((A.planeWeight_smooth k).pow 2).contDiffOn hcs.contDiffOn hpc
  have hsp : tsupport T ⊆ V := by
    intro x hx
    have hw := tsupport_smul_subset_left (fun x => (A.planeWeight k x)^2) _ hx
    have hw' : x ∈ tsupport (A.planeWeight k) := by
      apply (show tsupport (fun x => (A.planeWeight k x)^2) ⊆ tsupport (A.planeWeight k) from ?_) hw
      simpa only [pow_two] using (tsupport_mul_subset_left (f := A.planeWeight k) (g := A.planeWeight k))
    obtain ⟨y,hy,heq⟩ := (A.supportedPlaneWeight k).tsupport_subset hw'
    change planeCoordinateIsometry.symm x ∈ U
    rw [← heq,planeCoordinateIsometry.symm_apply_apply]
    exact hKU hy
  have hpg : WeightedEstimates.WeightedBound univ s m (C*δ^2) T := by
    have hh := hprod.extend_support hV hsp (by positivity)
    convert hh using 1
    dsimp [C]
    ring
  have hmetric := hm τ s δ φ Z hφ hZ hτ hs hτs hs1 hδ.le hA₀.le hP₀
    (fun a => weightedBound_comp_isometry planeCoordinateIsometry.symm
      (A.vectorChartRead_smooth k (hZ a)) ((hZb a).mono_order (by omega))) hφm l
  have hms := (A.globalQuadraticTarget τ φ Z hφ hZ k l).contDiff
  have hadd := hmetric.add uniqueDiffOn_univ hs.le hms.contDiffOn hT.contDiffOn hpg
  have heq : A.globalPolynomialQuadraticTarget Q hQ F hF ε τ φ Z hφ hZ k l =
      (fun x => A.globalQuadraticTarget τ φ Z hφ hZ k l x+T x) := by
    funext x
    exact smul_add ((A.planeWeight k x)^2)
      (RealModes.quadraticAmplitude τ (fun a => A.vectorPlaneRead k (φ a))
        (fun a => A.vectorPlaneRead k (Z a)) l x)
      (coordinateQuadraticCoefficient (Q k) ε (A.jetChartMap k F)
        (fun a => A.vectorChartRead k (φ a)) (fun a => A.vectorChartRead k (Z a)) τ 0 l x)
  rw [heq]
  convert hadd using 1
  ring

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
