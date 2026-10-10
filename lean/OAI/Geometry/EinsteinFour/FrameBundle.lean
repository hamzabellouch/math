import OAI.Geometry.EinsteinFour.OrthonormalFrame

namespace OAI

/-! Actual orthonormal frames with the topology inherited from tangent
vectors. Using the tangent-bundle topology is essential: chart coordinates
at varying base points do not give a global product trivialization. -/

namespace PositiveEinsteinFour.Geometry

open EinsteinFour Bundle
open scoped Manifold ContDiff

noncomputable section

variable {M : Type*} [TopologicalSpace M] [ChartedSpace FourSpace M]
  [IsManifold I4 ∞ M]

structure FrameBundle (g : SmoothMetric M) where
  base : M
  frame : OrthonormalFrame g base

def frameRealization {g : SmoothMetric M} (e : FrameBundle g) :
    M × (Fin 4 → TangentBundle I4 M) :=
  (e.base, fun i => ⟨e.base, e.frame.vector i⟩)

instance (g : SmoothMetric M) : TopologicalSpace (FrameBundle g) :=
  TopologicalSpace.induced frameRealization inferInstance

theorem continuous_frameRealization (g : SmoothMetric M) :
    Continuous (frameRealization : FrameBundle g → M × (Fin 4 → TangentBundle I4 M)) :=
  continuous_induced_dom

theorem continuous_frameBase (g : SmoothMetric M) :
    Continuous (FrameBundle.base : FrameBundle g → M) :=
  continuous_fst.comp (continuous_frameRealization g)

theorem frameRealization_injective (g : SmoothMetric M) :
    Function.Injective (frameRealization : FrameBundle g → M × (Fin 4 → TangentBundle I4 M)) := by
  rintro ⟨x, e⟩ ⟨y, f⟩ h
  have hxy : x = y := congrArg Prod.fst h
  subst y
  have hv (i : Fin 4) : e.vector i = f.vector i := by
    apply TotalSpace.mk_injective x
    exact congrArg (fun z : M × (Fin 4 → TangentBundle I4 M) => z.2 i) h
  have hm : e.matrix = f.matrix := by
    ext i j
    exact congrArg (fun v : FourSpace => v i) (hv j)
  cases e with
  | mk A hA =>
    cases f with
    | mk B hB =>
      dsimp at hm
      subst B
      rfl

theorem isEmbedding_frameRealization (g : SmoothMetric M) :
    Topology.IsEmbedding (frameRealization : FrameBundle g →
      M × (Fin 4 → TangentBundle I4 M)) where
  eq_induced := rfl
  injective := frameRealization_injective g

private theorem tangentBundle_t2Space [T2Space M] : T2Space (TangentBundle I4 M) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro x y hne
  by_cases hbase : x.proj = y.proj
  · let e := trivializationAt FourSpace (TangentSpace I4 : M → Type _) x.proj
    have hx : x ∈ e.source := e.mem_source.mpr
      (mem_baseSet_trivializationAt FourSpace (TangentSpace I4) x.proj)
    have hy : y ∈ e.source := e.mem_source.mpr (by
      rw [← hbase]
      exact mem_baseSet_trivializationAt FourSpace (TangentSpace I4) x.proj)
    have hxy : e x ≠ e y := fun heq => hne (e.toOpenPartialHomeomorph.injOn hx hy heq)
    exact (e.toOpenPartialHomeomorph.continuousAt hx).disjoint
      (disjoint_nhds_nhds.mpr hxy) (e.toOpenPartialHomeomorph.continuousAt hy)
  · exact (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).continuousAt.disjoint
      (disjoint_nhds_nhds.mpr hbase)
      (FiberBundle.continuous_proj FourSpace (TangentSpace I4)).continuousAt

instance [T2Space M] (g : SmoothMetric M) : T2Space (FrameBundle g) := by
  let := tangentBundle_t2Space (M := M)
  exact (isEmbedding_frameRealization g).t2Space

instance (g : SmoothMetric M) : MeasurableSpace (FrameBundle g) :=
  borel (FrameBundle g)

instance (g : SmoothMetric M) : BorelSpace (FrameBundle g) := ⟨rfl⟩

def frameAt (g : SmoothMetric M) (c : M) : FrameBundle g :=
  ⟨c, canonicalFrame g c⟩

theorem frameBase_surjective (g : SmoothMetric M) :
    Function.Surjective (FrameBundle.base : FrameBundle g → M) :=
  fun c => ⟨frameAt g c, rfl⟩

end

end PositiveEinsteinFour.Geometry

end OAI
