import OAI.Analysis.KadisonKastler.SimpleIrreducibleRepresentation
import OAI.Analysis.TracialSplitting.StateExtension

namespace OAI

/-! # Pure-state extensions along unital star embeddings

The set of state extensions is weak-star compact. If the original state
is pure, an extreme point of this set is pure on the larger algebra.
This supplies state extensions used in the derivation construction.
-/

namespace KadisonKastler

noncomputable section

open NaimarkZFC
open scoped ComplexOrder

variable {A B : Type*} [CStarAlgebra A] [CStarAlgebra B]

theorem exists_state_extension_of_embedding (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) (f : A →L[ℂ] ℂ) (hf : IsState f) :
    ∃ g : B →L[ℂ] ℂ, IsState g ∧ restrictState φ g = f := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let fP := positiveOfSquares f hf.2
  have hf1 : fP 1 = 1 := ((isState_iff f).mp hf).1
  obtain ⟨gP, hg1, hagree⟩ := CurrentMain.state_extension φ hφ fP hf1
  let g : B →L[ℂ] ℂ := gP.toLinearMap.mkContinuous 1 (fun b => by
    change ‖gP b‖ ≤ 1 * ‖b‖
    simpa only [hg1, Complex.one_re, one_mul] using positive_norm_apply_le gP b)
  have hg : IsState g := by
    apply (isState_iff g).mpr
    refine ⟨?_, fun b => ?_⟩
    · change gP 1 = 1
      exact hg1
    change (gP (star b * b)).im = 0 ∧ 0 ≤ (gP (star b * b)).re
    have h := gP.map_nonneg (star_mul_self_nonneg b)
    exact ⟨h.2.symm, h.1⟩
  refine ⟨g, hg, ?_⟩
  ext a
  change gP (φ a) = f a
  simpa only [fP, positiveOfSquares_apply] using hagree a

theorem exists_pure_state_extension (φ : A →⋆ₐ[ℂ] B)
    (hφ : Function.Injective φ) (f : A →L[ℂ] ℂ) (hf : IsPureState f) :
    ∃ g : B →L[ℂ] ℂ, IsPureState g ∧ restrictState φ g = f := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : IsScalarTower ℝ ℂ (WeakDual ℂ B) :=
    inferInstanceAs (IsScalarTower ℝ ℂ (B →L[ℂ] ℂ))
  let : LocallyConvexSpace ℝ (WeakDual ℂ B) :=
    (WeakDual.withSeminorms ℂ B).toLocallyConvexSpace
  have hfp := (mem_extremePoints.mp hf).1
  let S : Set (WeakDual ℂ B) :=
    {g | IsState g.toStrongDual ∧ ∀ a, g (φ a) = f a}
  have hclosed : IsClosed S := by
    have heq (a : A) : IsClosed {g : WeakDual ℂ B | g (φ a) = f a} :=
      isClosed_eq (WeakDual.eval_continuous (φ a)) continuous_const
    have h := isClosed_weakStates.inter (isClosed_iInter heq)
    simpa only [S, weakStates, Set.ofPred_and, Set.ofPred_forall] using h
  have hcompact : IsCompact S :=
    isCompact_weakStates.of_isClosed_subset hclosed (fun _ h => h.1)
  obtain ⟨g0, hg0, hrest0⟩ := exists_state_extension_of_embedding φ hφ f hfp
  have hne : S.Nonempty := by
    refine ⟨StrongDual.toWeakDual g0, hg0, fun a => ?_⟩
    exact congrArg (fun F : A →L[ℂ] ℂ => F a) hrest0
  obtain ⟨g, hg⟩ := hcompact.extremePoints_nonempty hne
  have hrest : restrictState φ g.toStrongDual = f := by
    ext a
    exact hg.1.2 a
  refine ⟨g.toStrongDual, ?_, hrest⟩
  rw [IsPureState, mem_extremePoints]
  refine ⟨hg.1.1, ?_⟩
  intro G hG H hH hseg
  have hfseg : f ∈ openSegment ℝ (restrictState φ G) (restrictState φ H) := by
    obtain ⟨a, b, ha, hb, hab, heq⟩ := hseg
    refine ⟨a, b, ha, hb, hab, ?_⟩
    rw [← restrictState_convex, heq, hrest]
  obtain ⟨hGf, hHf⟩ := (mem_extremePoints.mp hf).2 _ (isState_restrict φ G hG)
    _ (isState_restrict φ H hH) hfseg
  have hGS : StrongDual.toWeakDual G ∈ S :=
    ⟨hG, fun a => congrArg (fun F : A →L[ℂ] ℂ => F a) hGf⟩
  have hHS : StrongDual.toWeakDual H ∈ S :=
    ⟨hH, fun a => congrArg (fun F : A →L[ℂ] ℂ => F a) hHf⟩
  exact (mem_extremePoints.mp hg).2 _ hGS _ hHS hseg

end

end KadisonKastler

end OAI
