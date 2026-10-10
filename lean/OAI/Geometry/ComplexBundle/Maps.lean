import OAI.Geometry.ComplexBundle.Coordinates
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace OAI

noncomputable section

/-! Continuous bundle maps, adjoints, and normalized Hermitian scaling. -/

section
open Bundle Topology
namespace Kaplansky
variable {𝕜 Y V X : Type*} [NontriviallyNormedField 𝕜] [TopologicalSpace Y] [TopologicalSpace X]
variable [NormedAddCommGroup V] [NormedSpace 𝕜 V]
variable {E : Y → Type*} [∀ y, AddCommGroup (E y)] [∀ y, Module 𝕜 (E y)]
variable [∀ y, TopologicalSpace (E y)] [TopologicalSpace (TotalSpace V E)]
variable [FiberBundle V E] [VectorBundle 𝕜 V E]

include 𝕜 in
theorem continuousOn_bundle_sum_over {ι : Type*} (b : X → Y) {s : Set X}
    (hb : ContinuousOn b s) (u : Finset ι) (v : ι → ∀ x, E (b x))
    (hv : ∀ i ∈ u, ContinuousOn (fun x => TotalSpace.mk' V (b x) (v i x)) s) :
    ContinuousOn (fun x => TotalSpace.mk' V (b x) (∑ i ∈ u, v i x)) s := by
  intro x hx
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨hb x hx, ?_⟩
  have hc : ContinuousWithinAt
      (fun z => ∑ i ∈ u, ((trivializationAt V E (b x)) ⟨b z,v i z⟩).2) s x :=
    tendsto_finsetSum u (fun i hi =>
      ((FiberBundle.continuousWithinAt_totalSpace V _).mp (hv i hi x hx)).2)
  apply hc.congr_of_eventuallyEq
  · have hn := (trivializationAt V E (b x)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt V E (b x))
    filter_upwards [(hb x hx) hn] with z hz
    exact map_sum (((trivializationAt V E (b x)).linear 𝕜 hz).mk' _) (fun i => v i z) u
  · exact map_sum (((trivializationAt V E (b x)).linear 𝕜
      (mem_baseSet_trivializationAt V E (b x))).mk' _) (fun i => v i x) u

theorem continuousOn_bundle_smul_over (b : X → Y) {s : Set X} (hb : ContinuousOn b s)
    (f : X → 𝕜) (v : ∀ x, E (b x)) (hf : ContinuousOn f s)
    (hv : ContinuousOn (fun x => TotalSpace.mk' V (b x) (v x)) s) :
    ContinuousOn (fun x => TotalSpace.mk' V (b x) (f x • v x)) s := by
  intro x hx
  rw [FiberBundle.continuousWithinAt_totalSpace]
  refine ⟨hb x hx, ?_⟩
  have hc := (hf x hx).smul
    (((FiberBundle.continuousWithinAt_totalSpace V _).mp (hv x hx)).2)
  apply hc.congr_of_eventuallyEq
  · have hn := (trivializationAt V E (b x)).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt V E (b x))
    filter_upwards [(hb x hx) hn] with z hz
    exact ((trivializationAt V E (b x)).linear 𝕜 hz).map_smul (f z) (v z)
  · exact ((trivializationAt V E (b x)).linear 𝕜
      (mem_baseSet_trivializationAt V E (b x))).map_smul (f x) (v x)

end Kaplansky

end

section
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace
open Matrix
namespace Kaplansky
variable {n d r : ℕ} {E F : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]

omit [FiniteDimensional ℂ E] in
theorem inner_toMatrix (b : OrthonormalBasis (Fin d) ℂ E) (A : E →ₗ[ℂ] E) (v : E) :
    inner ℂ v (A v) = star (b.toBasis.repr v) ⬝ᵥ
      (LinearMap.toMatrix b.toBasis b.toBasis A) *ᵥ b.toBasis.repr v := by
  rw [LinearMap.toMatrix_mulVec_repr]
  calc
    inner ℂ v (A v) = ∑ i, star (b.repr v i) * b.repr (A v) i := by
      simpa only [PiLp.inner_apply, RCLike.inner_apply, starRingEnd_apply, mul_comm] using
        (b.repr.inner_map_map v (A v)).symm
    _ = _ := by simp only [dotProduct, Pi.star_apply, OrthonormalBasis.coe_toBasis_repr_apply]

/-- Transfer the normalized matrix relations to actual adjoints on the
original finite-dimensional Hermitian fibers. -/
theorem intrinsic_relations_of_matrix
    (b : OrthonormalBasis (Fin d) ℂ E) (c : OrthonormalBasis (Fin r) ℂ F)
    (X : Fin n → E →ₗ[ℂ] F)
    (hcol : (∑ i, (LinearMap.toMatrix b.toBasis c.toBasis (X i))ᴴ *
      LinearMap.toMatrix b.toBasis c.toBasis (X i)) = 1)
    (hrow : ((2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
      ∑ i, LinearMap.toMatrix b.toBasis c.toBasis (X i) *
        (LinearMap.toMatrix b.toBasis c.toBasis (X i))ᴴ).PosSemidef) :
    (∑ i, (LinearMap.adjoint (X i)).comp (X i)) = LinearMap.id ∧
      ∀ v : F, 0 ≤ inner ℂ v (((2/3 : ℂ) • (LinearMap.id : F →ₗ[ℂ] F) -
        ∑ i, (X i).comp (LinearMap.adjoint (X i))) v) := by
  constructor
  · apply (LinearMap.toMatrix b.toBasis b.toBasis).injective
    simpa only [map_sum, LinearMap.toMatrix_comp b.toBasis c.toBasis b.toBasis,
      LinearMap.toMatrix_adjoint, LinearMap.toMatrix_id] using hcol
  · intro v
    rw [inner_toMatrix c]
    have he : LinearMap.toMatrix c.toBasis c.toBasis
        ((2/3 : ℂ) • (LinearMap.id : F →ₗ[ℂ] F) - ∑ i, (X i).comp (LinearMap.adjoint (X i))) =
        (2/3 : ℂ) • (1 : Matrix (Fin r) (Fin r) ℂ) -
          ∑ i, LinearMap.toMatrix b.toBasis c.toBasis (X i) *
            (LinearMap.toMatrix b.toBasis c.toBasis (X i))ᴴ := by
      simp only [map_sub, map_smul, map_sum, LinearMap.toMatrix_id,
        LinearMap.toMatrix_comp c.toBasis b.toBasis c.toBasis, LinearMap.toMatrix_adjoint]
    rw [he]
    exact hrow.dotProduct_mulVec_nonneg _

end Kaplansky

end

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

theorem bundleMap_apply_eq
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (a y : Y)
    (hy : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a)
    (i : Fin n) (v : E y) :
    T y i v = ∑ k, (∑ j, bundleMapCoordinates (d := d) (r := r) T a y i k j *
      inner ℂ (bundleOrthonormalFrame (trivializationAt (Fin d → ℂ) E a) y j) v) •
      bundleOrthonormalFrame (trivializationAt (Fin r → ℂ) F a) y k := by
  simp only [bundleMapCoordinates_eq T a y hy i]
  let b := bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E a) y hy.1
  let c := bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F a) y hy.2
  have he := congrArg (fun L : E y →ₗ[ℂ] F y => L v)
    (Matrix.toLin_toMatrix b.toBasis c.toBasis (T y i))
  rw [Matrix.toLin_apply] at he
  symm
  simpa only [Matrix.mulVec, dotProduct, OrthonormalBasis.coe_toBasis_repr_apply,
    OrthonormalBasis.repr_apply_apply, OrthonormalBasis.coe_toBasis, b, c,
    bundleOrthonormalBasis_apply] using he

/-- Continuous coordinate matrices act continuously on local sections of
the original bundles. -/
theorem continuousOn_bundleMap_apply_section
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (a : Y) {s : Set Y}
    (hsub : s ⊆ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a)
    (hT : ContinuousOn (bundleMapCoordinates (d := d) (r := r) T a) s)
    (v : ∀ y, E y) (hv : ContinuousOn (fun y => TotalSpace.mk' (Fin d → ℂ) y (v y)) s)
    (i : Fin n) :
    ContinuousOn (fun y => TotalSpace.mk' (Fin r → ℂ) y (T y i (v y))) s := by
  have hc : ContinuousOn (fun y => TotalSpace.mk' (Fin r → ℂ) y
      (∑ k, (∑ j, bundleMapCoordinates (d := d) (r := r) T a y i k j *
        inner ℂ (bundleOrthonormalFrame (trivializationAt (Fin d → ℂ) E a) y j) (v y)) •
        bundleOrthonormalFrame (trivializationAt (Fin r → ℂ) F a) y k)) s := by
    apply continuousOn_bundle_sum (𝕜 := ℂ)
    intro k _
    apply continuousOn_bundle_smul
    · apply continuousOn_finsetSum
      intro j _
      have hm := (continuous_apply j).comp_continuousOn
        ((continuous_apply k).comp_continuousOn ((continuous_apply i).comp_continuousOn hT))
      exact hm.mul (hE s _ v
        ((continuousOn_bundleOrthonormalFrame hE _ j).mono (fun _ hy => (hsub hy).1)) hv)
    · exact (continuousOn_bundleOrthonormalFrame hF _ k).mono (fun _ hy => (hsub hy).2)
  apply hc.congr
  intro y hy
  exact congrArg (TotalSpace.mk' (Fin r → ℂ) y) (bundleMap_apply_eq T a y (hsub hy) i (v y))

theorem bundleChartFrame_sum (a : Y) (y : Y)
    (hy : y ∈ (trivializationAt (Fin d → ℂ) E a).baseSet) (v : E y) :
    (∑ j, ((trivializationAt (Fin d → ℂ) E a) ⟨y,v⟩).2 j •
      bundleChartFrame (trivializationAt (Fin d → ℂ) E a) y j) = v := by
  let b := bundleChartBasis (trivializationAt (Fin d → ℂ) E a) y hy
  have he := b.sum_repr v
  simpa [b, bundleChartBasis, bundleChartFrame, hy] using he

/-- Continuity on the actual total spaces follows from the constructed
coordinate matrices. No simultaneous trivialization is assumed. -/
theorem continuous_bundleMap_of_coordinates
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y)
    (hT : ∀ a, ContinuousOn (bundleMapCoordinates (d := d) (r := r) T a)
      (hermitianChartSet (d := d) (r := r) (E := E) (F := F) a)) (i : Fin n) :
    Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (T z.proj i z.2)) := by
  apply continuous_iff_continuousAt.mpr
  intro z₀
  let a := z₀.proj
  let e := trivializationAt (Fin d → ℂ) E a
  let O := hermitianChartSet (d := d) (r := r) (E := E) (F := F) a
  let S : Set (TotalSpace (Fin d → ℂ) E) := π (Fin d → ℂ) E ⁻¹' O
  have hp : Continuous (π (Fin d → ℂ) E) := FiberBundle.continuous_proj (Fin d → ℂ) E
  have hO : IsOpen O := e.open_baseSet.inter (trivializationAt (Fin r → ℂ) F a).open_baseSet
  have hz₀ : z₀ ∈ S := mem_hermitianChartSet (d := d) (r := r) a
  have hec : ContinuousOn e S := e.continuousOn.mono
    (fun z hz => e.mem_source.mpr hz.1)
  have hsec (j : Fin d) : ContinuousOn
      (fun y => TotalSpace.mk' (Fin r → ℂ) y (T y i (bundleChartFrame e y j))) O :=
    continuousOn_bundleMap_apply_section hE hF T a (Set.Subset.refl _) (hT a)
      (fun y => bundleChartFrame e y j)
      ((continuousOn_bundleChartFrame e j).mono Set.inter_subset_left) i
  have hc : ContinuousOn (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj
        (∑ j, (e z).2 j • T z.proj i (bundleChartFrame e z.proj j))) S := by
    apply continuousOn_bundle_sum_over (𝕜 := ℂ) _ hp.continuousOn
    intro j _
    apply continuousOn_bundle_smul_over _ hp.continuousOn
    · exact (continuous_apply j).comp_continuousOn hec.snd
    · exact (hsec j).comp hp.continuousOn (fun _ hz => hz)
  have hc' : ContinuousOn (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (T z.proj i z.2)) S := by
    apply hc.congr
    intro z hz
    apply congrArg (TotalSpace.mk' (Fin r → ℂ) z.proj)
    simp only [← map_smul, ← map_sum]
    exact congrArg (T z.proj i) (bundleChartFrame_sum a z.proj hz.1 z.2).symm
  exact (hc' z₀ hz₀).continuousAt ((hO.preimage hp).mem_nhds hz₀)

theorem continuous_realizeHomSection
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (s : ∀ y, (hermitianHomCore (n := n) hE hF).Fiber y)
    (hs : Continuous (fun y => TotalSpace.mk' (Fin n → Matrix (Fin r) (Fin d) ℂ) y (s y)))
    (i : Fin n) :
    Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (realizeHomSection hE hF s z.proj i z.2)) :=
  continuous_bundleMap_of_coordinates hE hF _ (continuousOn_realizeHomSection_coordinates hE hF s hs) i

include d in
/-- Finite-dimensionality is derived from the ordinary bundle chart. -/
theorem bundleFiberFiniteDimensional (y : Y) : FiniteDimensional ℂ (E y) :=
  Module.Finite.of_basis (bundleChartBasis (trivializationAt (Fin d → ℂ) E y) y
    (mem_baseSet_trivializationAt (Fin d → ℂ) E y))

/-- The actual fiberwise adjoint, with finite-dimensionality supplied by
the original bundle rather than a new hypothesis. -/
def bundleAdjoint (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (y : Y) (i : Fin n) : F y →ₗ[ℂ] E y := by
  letI := bundleFiberFiniteDimensional (d := d) (E := E) y
  letI := bundleFiberFiniteDimensional (d := r) (E := F) y
  exact LinearMap.adjoint (T y i)

theorem bundleAdjoint_inner (T : ∀ y, Fin n → E y →ₗ[ℂ] F y)
    (y : Y) (i : Fin n) (v : E y) (w : F y) :
    inner ℂ (bundleAdjoint (d := d) (r := r) T y i w) v = inner ℂ w (T y i v) := by
  let := bundleFiberFiniteDimensional (d := d) (E := E) y
  let := bundleFiberFiniteDimensional (d := r) (E := F) y
  exact LinearMap.adjoint_inner_left (T y i) v w

theorem bundleAdjoint_coordinates (T : ∀ y, Fin n → E y →ₗ[ℂ] F y) (a y : Y)
    (hy : y ∈ hermitianChartSet (d := d) (r := r) (E := E) (F := F) a) (i : Fin n) :
    bundleMapCoordinates (d := r) (r := d) (bundleAdjoint (d := d) (r := r) T) a y i =
      (bundleMapCoordinates (d := d) (r := r) T a y i)ᴴ := by
  let := bundleFiberFiniteDimensional (d := d) (E := E) y
  let := bundleFiberFiniteDimensional (d := r) (E := F) y
  rw [bundleMapCoordinates_eq _ a y ⟨hy.2,hy.1⟩ i, bundleMapCoordinates_eq _ a y hy i]
  exact LinearMap.toMatrix_adjoint
    (bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E a) y hy.1)
    (bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F a) y hy.2) (T y i)

theorem continuous_bundleAdjoint
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y)
    (hT : ∀ i, Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (T z.proj i z.2))) (i : Fin n) :
    Continuous (fun z : TotalSpace (Fin r → ℂ) F =>
      TotalSpace.mk' (Fin d → ℂ) z.proj (bundleAdjoint (d := d) (r := r) T z.proj i z.2)) := by
  apply continuous_bundleMap_of_coordinates hF hE _ _ i
  intro a
  apply continuousOn_pi.mpr
  intro k
  have hc := (continuousOn_bundleMapCoordinates hE hF T hT a).mono
    (show hermitianChartSet (d := r) (r := d) (E := F) (F := E) a ⊆
      hermitianChartSet (d := d) (r := r) (E := E) (F := F) a from fun _ h => ⟨h.2,h.1⟩)
  have hh : ContinuousOn (fun y => (bundleMapCoordinates (d := d) (r := r) T a y k)ᴴ)
      (hermitianChartSet (d := r) (r := d) (E := F) (F := E) a) := by
    rw [continuousOn_iff_continuous_domRestrict]
    exact (((continuous_apply k).comp (continuousOn_iff_continuous_domRestrict.mp hc))).matrix_conjTranspose
  exact hh.congr (fun y hy => bundleAdjoint_coordinates T a y ⟨hy.2,hy.1⟩ k)

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

theorem exists_continuous_normalized_bundle_maps
    (hE : ContinuousHermitianMetric (d := d) (E := E))
    (hF : ContinuousHermitianMetric (d := r) (E := F))
    (T : ∀ y, Fin n → E y →ₗ[ℂ] F y)
    (hT : ∀ i, Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
      TotalSpace.mk' (Fin r → ℂ) z.proj (T z.proj i z.2)))
    (hexp : ∀ y, IntrinsicExpanding (T y)) :
    ∃ X : ∀ y, Fin n → E y →ₗ[ℂ] F y,
      (∀ i, Continuous (fun z : TotalSpace (Fin d → ℂ) E =>
        TotalSpace.mk' (Fin r → ℂ) z.proj (X z.proj i z.2))) ∧
      (∀ i, Continuous (fun z : TotalSpace (Fin r → ℂ) F =>
        TotalSpace.mk' (Fin d → ℂ) z.proj (bundleAdjoint (d := d) (r := r) X z.proj i z.2))) ∧
      ∀ y, (∑ i, (bundleAdjoint (d := d) (r := r) X y i).comp (X y i)) = LinearMap.id ∧
        ∀ v : F y, 0 ≤ inner ℂ v (((2/3 : ℂ) • (LinearMap.id : F y →ₗ[ℂ] F y) -
          ∑ i, (X y i).comp (bundleAdjoint (d := d) (r := r) X y i)) v) := by
  obtain ⟨s,hs,hr⟩ := exists_hermitian_scaled_section hE hF T hT hexp
  let X := realizeHomSection hE hF s
  have hX := continuous_realizeHomSection hE hF s hs
  refine ⟨X,hX,continuous_bundleAdjoint hE hF X hX,?_⟩
  intro y
  let := bundleFiberFiniteDimensional (d := d) (E := E) y
  let := bundleFiberFiniteDimensional (d := r) (E := F) y
  have hy := mem_hermitianChartSet (d := d) (r := r) (E := E) (F := F) y
  let b := bundleOrthonormalBasis (trivializationAt (Fin d → ℂ) E y) y hy.1
  let c := bundleOrthonormalBasis (trivializationAt (Fin r → ℂ) F y) y hy.2
  have he : ((hermitianHomCore hE hF).localTriv y ⟨y,s y⟩).2 =
      fun i => LinearMap.toMatrix b.toBasis c.toBasis (X y i) := by
    rw [← realizeHomSection_coordinates hE hF s y y hy]
    exact funext (bundleMapCoordinates_eq X y y hy)
  have hm := hr y y hy
  dsimp only at hm
  rw [he] at hm
  exact intrinsic_relations_of_matrix b c (X y) hm.1 hm.2

end Kaplansky

end

end OAI
