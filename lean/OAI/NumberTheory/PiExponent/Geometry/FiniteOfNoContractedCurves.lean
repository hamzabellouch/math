import OAI.NumberTheory.PiExponent.Geometry.IntegralCurveExistence
import OAI.NumberTheory.PiExponent.LocalAlgebra.FiniteFromClosedFibers

namespace OAI

noncomputable section
namespace PiExponent.NumericalAmpleness
open CategoryTheory AlgebraicGeometry TopologicalSpace Set

private theorem positive_dimension_eq_nat {D : WithBot ℕ∞} (d : ℕ)
    (hD : D ≤ d) (hpos : 0 < D) : ∃ n : ℕ, D = n ∧ 0 < n := by
  have hbot : D ≠ ⊥ := by
    intro h
    rw [h] at hpos
    exact not_lt_bot hpos
  obtain ⟨e, rfl⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have he : e ≤ (d : ℕ∞) := by exact_mod_cast hD
  have hetop : e ≠ ⊤ := ne_of_lt (he.trans_lt (by simp))
  obtain ⟨n, rfl⟩ := ENat.ne_top_iff_exists.mp hetop
  exact ⟨n, rfl, by exact_mod_cast hpos⟩

def integralCurveFromClosedFiber {X Y : Scheme.{0}} (f : X ⟶ Y) (y : Y)
    (hy : IsClosed ({y} : Set Y)) (C : IntegralCurve (f.fiber y)) : IntegralCurve X := by
  let : IsClosedImmersion (Y.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  let : IsClosedImmersion (f.fiberι y) := by
    unfold Scheme.Hom.fiberι
    let : MorphismProperty.IsStableUnderBaseChange (@IsClosedImmersion.{0}) :=
      IsClosedImmersion.isStableUnderBaseChange
    exact MorphismProperty.of_isPullback (P := @IsClosedImmersion.{0})
      (IsPullback.of_hasPullback f (Y.fromSpecResidueField y)).flip
      (show IsClosedImmersion (Y.fromSpecResidueField y) from inferInstance)
  exact {
    scheme := C.scheme
    embedding := C.embedding ≫ f.fiberι y
    closedImmersion := inferInstance
    integral := C.integral
    dimension := C.dimension }

theorem finite_closed_fiber_of_no_integralCurve {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsProper f] (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (y : Y) (hno : IsEmpty (IntegralCurve (f.fiber y))) : (f ⁻¹' {y}).Finite := by
  have hbound : topologicalKrullDim (f.fiber y) ≤ d :=
    (f.fiberι y).isEmbedding.topologicalKrullDim_le.trans hdim
  have hzero : topologicalKrullDim (f.fiber y) ≤ 0 := by
    by_contra h
    obtain ⟨n, hn, hpos⟩ := positive_dimension_eq_nat d hbound (lt_of_not_ge h)
    obtain ⟨C⟩ := nonempty_integralCurve_of_dimension_pos (f.fiber y) n hn hpos
    exact hno.false C
  let : IsLocallyNoetherian (f.fiber y) := by
    unfold Scheme.Hom.fiber
    infer_instance
  let : IsLocallyArtinian (f.fiber y) := IsLocallyArtinian.of_topologicalKrullDim_le_zero hzero
  let : Finite (f.fiber y) := finite_of_compact_of_discrete
  exact (f.fiberHomeo y).finite_iff.mp inferInstance

theorem isFinite_of_no_contracted_integralCurves {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsProper f] [JacobsonSpace Y]
    (d : ℕ) (hdim : topologicalKrullDim X ≤ d)
    (hno : ∀ (C : IntegralCurve X) (y : Y) (_hy : IsClosed ({y} : Set Y))
      (j : C.scheme ⟶ f.fiber y), j ≫ f.fiberι y = C.embedding → False) : IsFinite f := by
  apply isFinite_of_proper_finite_closed_fibers f
  intro y hy
  apply finite_closed_fiber_of_no_integralCurve f d hdim y
  refine ⟨fun C => ?_⟩
  exact hno (integralCurveFromClosedFiber f y hy C) y hy C.embedding rfl

end PiExponent.NumericalAmpleness

end

end OAI
