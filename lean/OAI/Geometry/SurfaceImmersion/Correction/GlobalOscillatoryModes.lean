import OAI.Geometry.SurfaceImmersion.Atlas.VectorChartRead
import OAI.Geometry.SurfaceImmersion.Atlas.SupportedAtlasRestore
import OAI.Geometry.Immersion.ClosedSurface.CrossModes

namespace OAI

/-! Global phase/amplitude representatives of the actual supported oscillations. -/
noncomputable section
open Set Manifold
open scoped ContDiff Manifold Topology BigOperators
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (planeCoordinateIsometry)
open QuadraticMean (realMode realPartCLM)

lemma realMode_smul {n : ℕ} (θ a : ℝ) (Z : Fin n → ℂ) :
    realMode θ (a • Z) = a • realMode θ Z := by
  change realPartCLM n (QuadraticMean.phase θ • (a • Z)) =
    a • realPartCLM n (QuadraticMean.phase θ • Z)
  rw [smul_comm, map_smul]

lemma realMode_zero {n : ℕ} (θ : ℝ) : realMode θ (0 : Fin n → ℂ) = 0 := by
  change realPartCLM n (QuadraticMean.phase θ • (0 : Fin n → ℂ)) = 0
  rw [smul_zero,map_zero]

lemma realMode_contDiff {n : ℕ} (τ : ℝ) :
    ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) => realMode (p.1/τ) p.2) := by
  change ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) =>
    realPartCLM n (QuadraticMean.phase (p.1/τ) • p.2))
  apply (realPartCLM n).contDiff.comp
  apply ContDiff.smul (f := fun p : ℝ × (Fin n → ℂ) => QuadraticMean.phase (p.1/τ))
    (g := fun p : ℝ × (Fin n → ℂ) => p.2)
  · have ha : ContDiff ℝ ∞ (fun p : ℝ × (Fin n → ℂ) => ((p.1/τ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_fst.div_const τ)
    exact Complex.contDiff_exp.comp (ha.mul contDiff_const)
  · exact contDiff_snd

def surfaceMode {X : Type*} {n : ℕ} (τ : ℝ) (φ : X → ℝ) (Z : X → Fin n → ℂ) :
    X → Fin n → ℝ := fun p => realMode (φ p/τ) (Z p)

lemma surfaceMode_tsupport {X : Type*} [TopologicalSpace X] {n : ℕ}
    (τ : ℝ) (φ : X → ℝ) (Z : X → Fin n → ℂ) :
    tsupport (surfaceMode τ φ Z) ⊆ tsupport Z := by
  apply closure_mono
  intro x hx
  change Z x ≠ 0
  intro hz
  exact hx (by simp only [surfaceMode,hz,realMode_zero])

variable {M : Type*} [TopologicalSpace M] [ChartedSpace Plane M]
  [IsManifold planeModel ∞ M]

omit [IsManifold planeModel ∞ M] in
lemma surfaceMode_smooth {n : ℕ} (τ : ℝ) {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z) :
    ContMDiff planeModel 𝓘(ℝ,Fin n → ℝ) ∞ (surfaceMode τ φ Z) :=
  (realMode_contDiff τ).contMDiff.comp (hφ.prodMk_space hZ)

variable [CompactSpace M]
namespace SmoothingAtlas
variable (A : SmoothingAtlas M)

lemma restore_displacement {n : ℕ} (i : A.centers) (τ : ℝ)
    (φ : SmallModes.Base → ℝ) (Z : SmallModes.Base → Fin n → ℂ)
    (hZ : tsupport Z ⊆ (JetPolynomial.Perturbation.modeSupport (A.chartWeightCompact i) : Set SmallModes.Base)) :
    restore (i : M) (A.outer i) (QuadraticMean.displacement τ φ Z ∘ planeCoordinateIsometry) =
      surfaceMode τ (restore (i : M) (A.outer i) (φ ∘ planeCoordinateIsometry))
        (restore (i : M) (A.outer i) (Z ∘ planeCoordinateIsometry)) := by
  funext p
  by_cases hp : p ∈ (chart (i : M)).source
  · simp only [restore,indicator_of_mem hp,Function.comp_apply,surfaceMode,
      QuadraticMean.displacement]
    by_cases hz : Z (planeCoordinateIsometry (chart (i : M) p)) = 0
    · simp only [hz,realMode_zero,smul_zero]
    · rw [A.outer_one i p (A.mem_weight_support_of_plane i hp (hZ (subset_tsupport Z hz))),
        one_smul,one_smul,one_smul]
  · simp only [restore,indicator_of_notMem hp,surfaceMode,realMode_zero]

lemma vectorChartRead_mode_on_support {n : ℕ} (i : A.centers) (τ : ℝ)
    (φ : M → ℝ) (Z : M → Fin n → ℂ) {x : JetPolynomial.Base}
    (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    A.vectorChartRead i (surfaceMode τ φ Z) x =
      realMode (A.vectorChartRead i φ x/τ) (A.vectorChartRead i Z x) := by
  rw [A.vectorChartRead_on_support i _ hx,A.vectorChartRead_on_support i _ hx,
    A.vectorChartRead_on_support i _ hx]
  rfl

lemma vectorChartRead_mode_jets {n : ℕ} (i : A.centers) (τ : ℝ)
    {φ : M → ℝ} {Z : M → Fin n → ℂ}
    (hφ : ContMDiff planeModel 𝓘(ℝ) ∞ φ)
    (hZ : ContMDiff planeModel 𝓘(ℝ,Fin n → ℂ) ∞ Z) (m : ℕ)
    {x : JetPolynomial.Base} (hx : x ∈ (A.chartWeightCompact i : Set JetPolynomial.Base)) :
    iteratedFDeriv ℝ m (A.vectorChartRead i (surfaceMode τ φ Z)) x =
      iteratedFDeriv ℝ m (fun y =>
        realMode (A.vectorChartRead i φ y/τ) (A.vectorChartRead i Z y)) x := by
  apply iteratedFDeriv_eq_on_tsupport (A.chartWeight_smooth i).continuous
    isOpen_univ (subset_univ _) (A.vectorChartRead_smooth i (surfaceMode_smooth τ hφ hZ)).contDiffOn
    ((realMode_contDiff τ).comp ((A.vectorChartRead_smooth i hφ).prodMk
      (A.vectorChartRead_smooth i hZ))).contDiffOn
    (fun y hy => A.vectorChartRead_mode_on_support i τ φ Z (A.chartWeight_tsupport i ▸ hy)) m
  rwa [A.chartWeight_tsupport]

end SmoothingAtlas
end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
