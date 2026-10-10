import OAI.Analysis.MatrixScaling.Expansion
import OAI.Geometry.ComplexBundle.Hom

namespace OAI

noncomputable section

/-! Coordinates and realization of Hermitian scaling sections. -/

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky
variable {n d r : ℕ} {Y : Type*} [TopologicalSpace Y]
variable {E F : Y → Type*}
variable [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [∀ y, NormedAddCommGroup (F y)] [∀ y, InnerProductSpace ℂ (F y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]
variable [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
variable [FiberBundle (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
variable [FiberBundle (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]

/-- Coordinates of genuine fiber maps in the constructed orthonormal frames. -/
def bundleMapCoordinates (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (a y : Y) :
    Fin n → Matrix (Fin r) (Fin d) ℂ :=
  fun i k j => inner ℂ
    (bundleOrthonormalFrame (trivializationAt (Fin r → ℂ) F a) y k)
    (T y i (bundleOrthonormalFrame (trivializationAt (Fin d → ℂ) E a) y j))

theorem bundleMapCoordinates_eq (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (a y : Y)
    (hy : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a) (i : Fin n) :
    bundleMapCoordinates (d := d) (r := r) T a y i = LinearMap.toMatrix
      (bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E a) y hy.1).toBasis
      (bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F a) y hy.2).toBasis (T y i) := by
  ext k j
  simp only [bundleMapCoordinates, LinearMap.toMatrix_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply,
    OrthonormalBasis.coe_toBasis, bundleOrthonormalBasis_apply]

theorem continuousOn_bundleMapCoordinates
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y)
    (hT : ∀ i, Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (T z.proj i z.2))) (a : Y) :
    ContinuousOn (bundleMapCoordinates (d := d) (r := r) T a) (hermitianChartSet (d := d) (r := r) (E := E) (F := F) a) := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro k
  apply continuousOn_pi.mpr
  intro j
  apply hF
  · exact (continuousOn_bundleOrthonormalFrame hF _ k).mono Set.inter_subset_right
  · exact (hT i).comp_continuousOn
      ((continuousOn_bundleOrthonormalFrame hE _ j).mono Set.inter_subset_left)

theorem bundleMapCoordinates_expanding
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (hT : ∀ y, IntrinsicExpanding (T y))
    (a y : Y) (hy : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a) :
    Expanding (bundleMapCoordinates (d := d) (r := r) T a y) := by
  have he : bundleMapCoordinates (d := d) (r := r) T a y = fun i => LinearMap.toMatrix
      (bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E a) y hy.1).toBasis
      (bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F a) y hy.2).toBasis (T y i) :=
    funext (bundleMapCoordinates_eq T a y hy)
  rw [he]
  exact expanding_in_basis _ _ _ (hT y)

theorem bundleUnitaryTransition_star
    {k : ℕ} {V : Y → Type*} [∀ y, NormedAddCommGroup (V y)] [∀ y, InnerProductSpace ℂ (V y)]
    [TopologicalSpace (TotalSpace (Fin k → ℂ) V)]
    [FiberBundle (Fin k → ℂ) V] [VectorBundle ℂ (Fin k → ℂ) V]
    (a b : Trivialization (Fin k → ℂ) (π (Fin k → ℂ) V)) [a.IsLinear ℂ] [b.IsLinear ℂ]
    (y : Y) : (bundleUnitaryTransition a b y)ᴴ = bundleUnitaryTransition b a y := by
  apply Matrix.ext
  intro i j
  exact inner_conj_symm _ _

theorem bundleMapCoordinates_compatible
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (a b y : Y)
    (ha : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a)
    (hb : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) b) :
    bundleMapCoordinates (d := d) (r := r) T b y = frameTuple (bundleMapCoordinates (d := d) (r := r) T a y)
      (hermitianSourceTransition (d := d) (E := E) a b y)
      (hermitianTargetTransition (r := r) (F := F) a b y) := by
  funext i
  dsimp only [frameTuple, hermitianSourceTransition, hermitianTargetTransition]
  rw [bundleUnitaryTransition_star, bundleMapCoordinates_eq T a y ha i,
    bundleMapCoordinates_eq T b y hb i,
    bundleUnitaryTransition_eq _ _ y hb.1 ha.1,
    bundleUnitaryTransition_eq _ _ y ha.2 hb.2]
  symm
  exact basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix
    (bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E b) y hb.1).toBasis
    (bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E a) y ha.1).toBasis
    (bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F b) y hb.2).toBasis
    (bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F a) y ha.2).toBasis (T y i)

omit [∀ y, InnerProductSpace ℂ (E y)] [∀ y, InnerProductSpace ℂ (F y)]
    [VectorBundle ℂ (Fin d → ℂ) E] [VectorBundle ℂ (Fin r → ℂ) F] in
theorem mem_hermitianChartSet (y : Y) :
    y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) y :=
  ⟨mem_baseSet_trivializationAt (Fin d → ℂ) E y,
    mem_baseSet_trivializationAt (Fin r → ℂ) F y⟩

/-- Interpret a section of the constructed core as linear maps between
its original bundles, using the core's selected chart in each fiber. -/
def realizeHomSection
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (s : ∀ y, (hermitianHomCore (n := n) hE hF).Fiber y) (y : Y) (i : Fin n) :
    E y →ₗ[ℂ] F y :=
  Matrix.toLin
    (bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E y) y
      (mem_baseSet_trivializationAt (Fin d → ℂ) E y)).toBasis
    (bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F y) y
      (mem_baseSet_trivializationAt (Fin r → ℂ) F y)).toBasis (s y i)

theorem realizeHomSection_at
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (s : ∀ y, (hermitianHomCore (n := n) hE hF).Fiber y) (y : Y) :
    bundleMapCoordinates (d := d) (r := r) (realizeHomSection hE hF s) y y = s y := by
  funext i
  rw [bundleMapCoordinates_eq _ y y (mem_hermitianChartSet (d := d) (r := r) y) i]
  exact LinearMap.toMatrix_toLin _ _ (s y i)

theorem realizeHomSection_coordinates
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (s : ∀ y, (hermitianHomCore (n := n) hE hF).Fiber y) (a y : Y)
    (hy : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a) :
    bundleMapCoordinates (d := d) (r := r) (realizeHomSection hE hF s) a y =
      ((hermitianHomCore hE hF).localTriv a ⟨y,s y⟩).2 := by
  rw [bundleMapCoordinates_compatible _ y a y
    (mem_hermitianChartSet (d := d) (r := r) y) hy, realizeHomSection_at]
  rfl

theorem continuousOn_realizeHomSection_coordinates
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (s : ∀ y, (hermitianHomCore (n := n) hE hF).Fiber y)
    (hs : Continuous (fun y => TotalSpace.mk' (Fin n → Matrix (Fin r) (Fin d) ℂ) y (s y)))
    (a : Y) :
    ContinuousOn (bundleMapCoordinates (d := d) (r := r) (realizeHomSection hE hF s) a)
      (hermitianChartSet (d := d) (r := r) (E := E) (F := F) a) := by
  have hc := ((hermitianHomCore hE hF).localTriv a).continuousOn.comp hs.continuousOn
    (show Set.MapsTo (fun y => TotalSpace.mk' (Fin n → Matrix (Fin r) (Fin d) ℂ) y (s y))
      (hermitianChartSet (d := d) (r := r) (E := E) (F := F) a)
      ((hermitianHomCore hE hF).localTriv a).source from fun y hy =>
        ((hermitianHomCore hE hF).localTriv a).mem_source.mpr hy)
  exact hc.snd.congr (fun y hy => realizeHomSection_coordinates hE hF s a y hy)

end Kaplansky

end

open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator
open Matrix Bundle Topology
namespace Kaplansky
variable {n d r : ℕ} {Y : Type*} [TopologicalSpace Y] [LocallyCompactSpace Y]
variable {E F : Y → Type*}
variable [∀ y, NormedAddCommGroup (E y)] [∀ y, InnerProductSpace ℂ (E y)]
variable [∀ y, NormedAddCommGroup (F y)] [∀ y, InnerProductSpace ℂ (F y)]
variable [TopologicalSpace (TotalSpace (Fin d → ℂ) E)]
variable [TopologicalSpace (TotalSpace (Fin r → ℂ) F)]
variable [FiberBundle (Fin d → ℂ) E] [VectorBundle ℂ (Fin d → ℂ) E]
variable [FiberBundle (Fin r → ℂ) F] [VectorBundle ℂ (Fin r → ℂ) F]

/-- Normalization of intrinsic expanding maps descends in the constructed
Hom-tuple bundle. The ordinary input bundles may be nontrivial. -/
theorem exists_hermitian_scaled_section
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y)
    (hT : ∀ i, Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (T z.proj i z.2)))
    (hexp : ∀ y, IntrinsicExpanding (T y)) :
    ∃ s : ∀ y, (hermitianHomCore (n := n) hE hF).Fiber y,
      Continuous (fun y => TotalSpace.mk' (Fin n → Matrix (Fin r) (Fin d) ℂ) y (s y)) ∧
      ∀ a y, y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a →
        let X := ((hermitianHomCore hE hF).localTriv a ⟨y,s y⟩).2
        (∑ i, (X i)ᴴ * X i) = 1 ∧
        ((2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) - ∑ i, X i * (X i)ᴴ).PosSemidef := by
  exact exists_scaled_core_section (hermitianHomCore hE hF)
    (bundleMapCoordinates (d := d) (r := r) T)
    (continuousOn_bundleMapCoordinates hE hF T hT)
    (bundleMapCoordinates_expanding T hexp)
    (hermitianSourceTransition (d := d) (E := E))
    (hermitianTargetTransition (r := r) (F := F))
    (hermitianHomCore_unitary (d := d) (r := r))
    (fun a b y _ _ M => hermitianHomCore_coordChange hE hF a b y M)
    (bundleMapCoordinates_compatible T)

end Kaplansky

end

end OAI
