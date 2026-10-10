import OAI.NumberTheory.DukePrimeDegree.Geometry.RootPrefixCompatibility
import OAI.NumberTheory.DukePrimeDegree.Geometry.QuotientLiftMeasure

namespace OAI

/-! # Root-prefix box measures agree with the actual covering lift -/

noncomputable section
open MeasureTheory Set
open scoped Topology
namespace DukePrimeDegree
open PrimeDegreePackets
namespace RootPrefixCoordinates

variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {T : Type*} [TopologicalSpace T]

def timeGroupParam (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries=allPositiveRoots n) (g : G n)
    (z : (UpperRootTransverse n × T) × c.Time) : G n :=
  g*C.groupParam (z.1.1,(z.1.2,c.remainingWordHomeomorph hP hf z.2))

theorem timeGroupParam_isOpenEmbedding
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries=allPositiveRoots n) (g : G n) :
    Topology.IsOpenEmbedding (C.timeGroupParam c hP hf g) := by
  let E := (Homeomorph.prodAssoc (UpperRootTransverse n) T c.Time).trans
    ((Homeomorph.refl (UpperRootTransverse n)).prodCongr
      ((Homeomorph.refl T).prodCongr (c.remainingWordHomeomorph hP hf)))
  exact (Homeomorph.mulLeft g).isOpenEmbedding.comp
    (C.groupParam_isOpenEmbedding.comp E.isOpenEmbedding)

lemma quotient_timeGroupParam
    (C : RootPrefixCoordinates n P T) (c : EliminationChain P D)
    (hP : InitialRootPattern P) (hf : c.finalEntries=allPositiveRoots n) (g : G n)
    (z : (UpperRootTransverse n × T) × c.Time) :
    Quotient.mk (QuotientGroup.rightRel (integralGroup n))
      (C.timeGroupParam c hP hf g z)=C.timeParam c hP hf g z := rfl

end RootPrefixCoordinates

namespace RootPrefixBox
variable {n : ℕ} {P : Finset (Fin n × Fin n)} {D : Finset (Fin n)}
  {T : Type*} [TopologicalSpace T] [MeasurableSpace T] [BorelSpace T]
  {C : RootPrefixCoordinates n P T} {c : EliminationChain P D}
  {hP : InitialRootPattern P} {hf : c.finalEntries=allPositiveRoots n} {g : G n}

theorem coordinateMeasure_eq_lift_restrict
    (B : RootPrefixBox C c hP hf g) (μ : Measure (X n))
    (s : X n → G n) (hsm : Measurable s)
    (hs : ∀ x, Quotient.mk (QuotientGroup.rightRel (integralGroup n)) (s x)=x) :
    B.coordinateMeasure μ=
      ((quotientLiftMeasure n μ s).comap (C.timeGroupParam c hP hf g)).restrict B.domain := by
  let F := C.timeGroupParam c hP hf g
  have hF : MeasurableEmbedding F := (C.timeGroupParam_isOpenEmbedding c hP hf g).measurableEmbedding
  ext A hA
  rw [B.coordinateMeasure_apply μ hA,Measure.restrict_apply hA,
    hF.comap_apply]
  have hinj : Set.InjOn
      (Quotient.mk (QuotientGroup.rightRel (integralGroup n))) (F '' (A ∩ B.domain)) := by
    rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ hxy
    have he : B.param ⟨x,hx.2⟩=B.param ⟨y,hy.2⟩ := hxy
    have hz := congrArg Subtype.val (B.embedding.injective he)
    exact congrArg F hz
  rw [quotientLiftMeasure_injective_chart n μ s hsm hs _
    (hF.measurableSet_image.mpr (hA.inter (B.transverse_open.prod B.time_open).measurableSet)) hinj]
  rw [Set.image_image]
  rfl

end RootPrefixBox
end DukePrimeDegree

end

end OAI
