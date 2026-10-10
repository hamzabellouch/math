import OAI.NumberTheory.PiExponent.Ampleness.NumericalAmpleness
import OAI.NumberTheory.PiExponent.Approximation.LinePullback
import OAI.NumberTheory.PiExponent.Cohomology.CohomologyIso

namespace OAI

namespace PiExponent.NumericalAmpleness
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open PiExponentSeshadri.Geometry

def curveDegree {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (C : IntegralCurve X) : ℤ :=
  eulerCharacteristic (C.embedding ≫ p) 1
    ((Scheme.Modules.pullback C.embedding).obj L.sheaf) -
  eulerCharacteristic (C.embedding ≫ p) 1 (structureSheaf C.scheme)

def IntegralCurve.mapClosed {X Y : Scheme.{0}} (C : IntegralCurve Y)
    (i : Y ⟶ X) [IsClosedImmersion i] : IntegralCurve X where
  scheme := C.scheme
  embedding := C.embedding ≫ i
  closedImmersion := inferInstance
  integral := C.integral
  dimension := C.dimension

theorem curveDegree_mapClosed {X Y : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of ℂ))
    (L : LineBundle X) (i : Y ⟶ X) [IsClosedImmersion i] (C : IntegralCurve Y) :
    curveDegree p L (C.mapClosed i) = curveDegree (i ≫ p) (L.pullback i) C := by
  unfold curveDegree IntegralCurve.mapClosed LineBundle.pullback
  simp only [Category.assoc]
  congr 1
  exact eulerCharacteristic_iso (C.embedding ≫ i ≫ p)
    ((Scheme.Modules.pullbackComp C.embedding i).app L.sheaf).symm 1

theorem uniform_curve_margin_restrict {X Y : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of ℂ)) (L H : LineBundle X) (ε : ℝ)
    (hmargin : ∀ C : IntegralCurve X,
      ε * (curveDegree p H C : ℝ) ≤ (curveDegree p L C : ℝ))
    (i : Y ⟶ X) [IsClosedImmersion i] :
    ∀ C : IntegralCurve Y,
      ε * (curveDegree (i ≫ p) (H.pullback i) C : ℝ) ≤
        (curveDegree (i ≫ p) (L.pullback i) C : ℝ) := by
  intro C
  simpa only [curveDegree_mapClosed] using hmargin (C.mapClosed i)

theorem proper_closed_dimension_succ_le {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [IrreducibleSpace X] [Nonempty Y]
    (f : Y → X) (hf : Topology.IsClosedEmbedding f)
    (hproper : Set.range f ≠ Set.univ) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim X := by
  let T : IrreducibleCloseds X := ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  let g := IrreducibleCloseds.map f hf.continuous
  have hg : StrictMono g := IrreducibleCloseds.map_strictMono_of_isInducing hf.isEmbedding.isInducing
  have hlt (Z : IrreducibleCloseds Y) : g Z < T := by
    apply lt_of_le_of_ne
    · intro x hx; trivial
    · intro he
      apply hproper
      apply Set.eq_univ_of_forall
      intro x
      have hx : x ∈ (g Z : Set X) := by rw [he]; trivial
      exact closure_minimal (Set.image_subset_range f _) hf.isClosed_range hx
  let k : WithTop (IrreducibleCloseds Y) → IrreducibleCloseds X := WithTop.recTopCoe T g
  have hk : StrictMono k := WithTop.strictMono_iff.mpr ⟨hg, hlt⟩
  have : Nonempty (IrreducibleCloseds Y) := by
    obtain ⟨y⟩ := ‹Nonempty Y›
    exact ⟨⟨closure {y}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  have hh := Order.krullDim_le_of_strictMono k hk
  simpa only [Order.krullDim_WithTop, topologicalKrullDim] using hh

theorem proper_closed_subscheme_dimension_succ_le {X Y : Scheme.{0}}
    [IsIntegral X] [Nonempty Y] (i : Y ⟶ X) [IsClosedImmersion i]
    (hproper : ¬ Function.Surjective i) :
    topologicalKrullDim Y + 1 ≤ topologicalKrullDim X :=
  proper_closed_dimension_succ_le i i.isClosedEmbedding
    (fun h => hproper (Set.range_eq_univ.mp h))

end
end PiExponent.NumericalAmpleness

end OAI
