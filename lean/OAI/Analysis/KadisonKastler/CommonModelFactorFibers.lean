import OAI.Analysis.KadisonKastler.CommonFiberCenterPredicate
import OAI.Analysis.KadisonKastler.CommonRankCoordinates

namespace OAI

/-! # Scalar centers of the actual common-model range fibers -/

namespace KadisonKastler

open MeasureTheory KadisonSimilarity

noncomputable section

universe u

variable {Z H : Type u} [CommCStarAlgebra Z] [TopologicalSpace.SeparableSpace Z]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [TopologicalSpace.SeparableSpace H]
  {π : Z →⋆ₐ[ℂ] (H →L[ℂ] H)} {D : CyclicDecompositionData π.range}
  (S : StarSubalgebra ℂ (H →L[ℂ] H)) [IsClosed (S : Set (H →L[ℂ] H))]
  [TopologicalSpace.SeparableSpace S] (M : BorelCommonModel π D S.subtype)

attribute [local instance] commonCyclicMeasurable commonCyclicBorel commonCyclicCountable

omit [TopologicalSpace.SeparableSpace Z] [TopologicalSpace.SeparableSpace S] in
theorem commonModel_factor_fibers
    (A C : StarSubalgebra ℂ (H →L[ℂ] H))
    [IsClosed (A : Set (H →L[ℂ] H))] [IsClosed (C : Set (H →L[ℂ] H))]
    (hAS : A ≤ S) (hCS : C ≤ S)
    (hcomm : ∀ a : A, ∀ c : C, a.val * c.val = c.val * a.val)
    (hgen : representationVonNeumannAlgebra (jointCStarSource A C).subtype =
      starSubalgebraCommutant π.range) :
    ∀ᵐ x ∂cyclicCommonBaseMeasure π D,
      NonunitalFiberScalarCenter ((M.field x).comp
        (StarSubalgebra.inclusion hAS).toNonUnitalStarAlgHom) := by
  let hJS := jointCStarSource_minimal A C S hAS hCS inferInstance
  let φ := StarSubalgebra.inclusion hJS
  let ρ := fun x => (M.field x).comp φ.toNonUnitalStarAlgHom
  let ρu := fun x : (Set.univ : Set (WeakDual.characterSpace ℂ Z)) => Unitization.starLift (ρ x.val)
  have hρ (a : jointCStarSource A C) (f : CommonCyclicHilbert π D) :
      ∀ᵐ x : (Set.univ : Set (WeakDual.characterSpace ℂ Z))
        ∂Measure.comap Subtype.val (cyclicCommonBaseMeasure π D),
        isometricExtension (cyclicCommonEmbedding π D) a.val f x =
          ρu x (Unitization.inr a) (f x) := by
    have ha := (ae_restrict_iff_subtype MeasurableSet.univ).mp
      (ae_restrict_of_ae (M.action (φ a) f))
    filter_upwards [ha] with x hx
    have he : ρu x (Unitization.inr a) = M.field x.val (φ a) :=
      DFunLike.congr_fun (Unitization.starLift.left_inv (ρ x.val)) a
    rw [he]
    exact hx
  have hf := ae_common_nonunital_fiber_center π D A C hcomm hgen Set.univ
    MeasurableSet.univ (by simp) ρu hρ
  have hi : φ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left A C)) =
      StarSubalgebra.inclusion hAS := by
    apply StarAlgHom.ext
    intro a
    rfl
  apply hf.mono
  intro x hx
  have h := nonunitalFiberScalarCenter_restrict_starLift ρ
    (StarSubalgebra.inclusion (le_jointCStarSource_left A C)) x hx
  change NonunitalFiberScalarCenter ((M.field x).comp
    (φ.comp (StarSubalgebra.inclusion (le_jointCStarSource_left A C))).toNonUnitalStarAlgHom) at h
  rwa [hi] at h

end

end KadisonKastler

end OAI
