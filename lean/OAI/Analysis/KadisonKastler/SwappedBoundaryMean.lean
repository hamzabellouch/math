import OAI.Analysis.KadisonKastler.ScalarProductSwap
import OAI.Analysis.KadisonKastler.ParameterizedBoundaryMean

namespace OAI

/-! # Transporting the scalar mean to the second coordinate -/

namespace KadisonKastler

noncomputable section

open MeasureTheory
open scoped BoundedContinuousFunction

variable {G D : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace D] {μ : Measure D} [IsProbabilityMeasure μ]

def scalarSwapFamilyL : (G →ᵇ ScalarLInfinity (μ.prod μ)) →L[ℂ]
    (G →ᵇ ScalarLInfinity (μ.prod μ)) := scalarProductSwapL.compLeftContinuousBounded G

omit [Group G] [DiscreteTopology G] in
theorem scalarSwapFamilyL_norm_le (F : G →ᵇ ScalarLInfinity (μ.prod μ)) :
    ‖scalarSwapFamilyL F‖ ≤ ‖F‖ := by
  apply (BoundedContinuousFunction.norm_le (norm_nonneg F)).mpr
  intro g
  change ‖scalarProductSwapL (F g)‖ ≤ ‖F‖
  rw [scalarProductSwapL_norm]
  exact F.norm_coe_le_norm g

omit [Group G] [DiscreteTopology G] in
theorem scalarSwapFamilyL_const (b : ScalarLInfinity (μ.prod μ)) :
    scalarSwapFamilyL (BoundedContinuousFunction.const G b) =
      BoundedContinuousFunction.const G (scalarProductSwapL b) := by ext; rfl

omit [Group G] in
theorem scalarSwapFamilyL_module (b : ScalarLInfinity (μ.prod μ))
    (F : G →ᵇ ScalarLInfinity (μ.prod μ)) :
    scalarSwapFamilyL (scalarBoundaryModule b F) =
      scalarBoundaryModule (scalarProductSwapL b) (scalarSwapFamilyL F) := by
  apply BoundedContinuousFunction.ext
  intro g
  exact scalarProductSwapL_mul b (F g)

theorem scalarSwapFamilyL_translate
    (α β : NonsingularAction G (D × D) (μ.prod μ))
    (hc : ∀ g z, β.toPerm g z.swap = (α.toPerm g z).swap)
    (g : G) (F : G →ᵇ ScalarLInfinity (μ.prod μ)) :
    scalarSwapFamilyL (scalarBoundaryTranslate β g F) =
      scalarBoundaryTranslate α g (scalarSwapFamilyL F) := by
  apply BoundedContinuousFunction.ext
  intro t
  exact scalarProductSwapL_intertwine (β.toPerm g⁻¹) (α.toPerm g⁻¹)
    (β.quasi g⁻¹) (α.quasi g⁻¹) (hc g⁻¹) (F (g⁻¹ * t))

def swappedScalarBoundaryMean
    {α : NonsingularAction G (D × D) (μ.prod μ)} (m : ScalarBoundaryMean α)
    (β : NonsingularAction G (D × D) (μ.prod μ))
    (hc : ∀ g z, β.toPerm g z.swap = (α.toPerm g z).swap) : ScalarBoundaryMean β where
  toCLM := scalarProductSwapL.comp (m.toCLM.comp scalarSwapFamilyL)
  map_one := by
    change scalarProductSwapL (m.toCLM (scalarSwapFamilyL (BoundedContinuousFunction.const G _))) = _
    rw [scalarSwapFamilyL_const, scalarProductSwapL_const, m.map_one, scalarProductSwapL_const]
  norm_le F := by
    change ‖scalarProductSwapL (m.toCLM (scalarSwapFamilyL F))‖ ≤ ‖F‖
    rw [scalarProductSwapL_norm]
    exact (m.norm_le _).trans (scalarSwapFamilyL_norm_le F)
  positive F hF := by
    apply scalarProductSwapL_positive
    apply m.positive
    intro g
    exact scalarProductSwapL_positive (F g) (hF g)
  module_map b F := by
    change scalarProductSwapL (m.toCLM (scalarSwapFamilyL (scalarBoundaryModule b F))) = _
    rw [scalarSwapFamilyL_module, m.module_map, scalarProductSwapL_mul, scalarProductSwapL_involution]
    rfl
  equivariant g F := by
    change scalarProductSwapL (m.toCLM (scalarSwapFamilyL (scalarBoundaryTranslate β g F))) = _
    rw [scalarSwapFamilyL_translate α β hc, m.equivariant]
    apply scalarProductSwapL_intertwine (α.toPerm g⁻¹) (β.toPerm g⁻¹)
      (α.quasi g⁻¹) (β.quasi g⁻¹)
    intro z
    have h := congrArg Prod.swap (hc g⁻¹ z.swap)
    simpa using h.symm

namespace NonsingularAction

variable (α : NonsingularAction G D μ)

def rightOnProduct : NonsingularAction G (D × D) (μ.prod μ) where
  toPerm :=
    { toFun := fun g => Equiv.prodCongr (Equiv.refl D) (α.toPerm g)
      map_one' := by ext z <;> simp
      map_mul' g h := by ext z <;> simp }
  quasi g := MeasureTheory.QuasiMeasurePreserving.prodMap
    (Measure.QuasiMeasurePreserving.id μ) (α.quasi g)

end NonsingularAction

variable (G) [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]

def randomWalkSecondScalarMean :
    ScalarBoundaryMean ((randomWalkBoundaryAction G).rightOnProduct) :=
  swappedScalarBoundaryMean
    (randomWalkParameterizedScalarMean G (randomWalkBoundaryMeasure G))
    ((randomWalkBoundaryAction G).rightOnProduct) (fun _ _ => rfl)

theorem randomWalkSecondScalarMean_natural (g : G)
    (F : G →ᵇ ScalarLInfinity ((randomWalkBoundaryMeasure G).prod (randomWalkBoundaryMeasure G))) :
    (randomWalkSecondScalarMean G).toCLM
      ((scalarInfinityPullbackL
        (((randomWalkBoundaryAction G).leftOnProduct (ν := randomWalkBoundaryMeasure G)).toPerm g)
        (((randomWalkBoundaryAction G).leftOnProduct (ν := randomWalkBoundaryMeasure G)).quasi g)).compLeftContinuousBounded G F) =
      scalarInfinityPullback
        (((randomWalkBoundaryAction G).leftOnProduct (ν := randomWalkBoundaryMeasure G)).toPerm g)
        (((randomWalkBoundaryAction G).leftOnProduct (ν := randomWalkBoundaryMeasure G)).quasi g)
        ((randomWalkSecondScalarMean G).toCLM F) := by
  let a := randomWalkBoundaryAction G
  let L := a.leftOnProduct (ν := randomWalkBoundaryMeasure G)
  let R := a.rightOnProduct
  let m := randomWalkParameterizedScalarMean G (randomWalkBoundaryMeasure G)
  have hF : scalarSwapFamilyL ((scalarInfinityPullbackL (L.toPerm g) (L.quasi g)).compLeftContinuousBounded G F) =
      (scalarInfinityPullbackL (R.toPerm g) (R.quasi g)).compLeftContinuousBounded G (scalarSwapFamilyL F) := by
    apply BoundedContinuousFunction.ext
    intro t
    exact scalarProductSwapL_intertwine (L.toPerm g) (R.toPerm g) (L.quasi g) (R.quasi g)
      (fun _ => rfl) (F t)
  change scalarProductSwapL (m.toCLM (scalarSwapFamilyL
    ((scalarInfinityPullbackL (L.toPerm g) (L.quasi g)).compLeftContinuousBounded G F))) =
    scalarInfinityPullback (L.toPerm g) (L.quasi g)
      (scalarProductSwapL (m.toCLM (scalarSwapFamilyL F)))
  rw [hF]
  have hm := randomWalkParameterizedScalarMean_natural G (randomWalkBoundaryMeasure G)
    (a.toPerm g) (a.quasi g) (scalarSwapFamilyL F)
  change m.toCLM ((scalarInfinityPullbackL (R.toPerm g) (R.quasi g)).compLeftContinuousBounded G
    (scalarSwapFamilyL F)) = scalarInfinityPullback (R.toPerm g) (R.quasi g)
      (m.toCLM (scalarSwapFamilyL F)) at hm
  rw [hm]
  exact scalarProductSwapL_intertwine (R.toPerm g) (L.toPerm g) (R.quasi g) (L.quasi g)
    (fun _ => rfl) _

end

end KadisonKastler

end OAI
