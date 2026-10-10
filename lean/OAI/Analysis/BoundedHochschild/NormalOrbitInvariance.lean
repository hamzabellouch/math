import OAI.Analysis.BoundedHochschild.UnitaryPredualAction
import OAI.Analysis.BoundedHochschild.IsometricFixedPoint

namespace OAI

/-! Convexity and invariance of the compact normal-state orbit. -/

noncomputable section

open Topology

namespace BoundedHochschild
namespace KadisonRingrose

open HochschildNormalPart

universe u

variable {M X : Type u} [CStarAlgebra M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

/-- Unitary pullback is weak-star continuous. -/
def weakUnitaryPullback (u : unitary M) : WeakDual ℂ M →L[ℂ] WeakDual ℂ M where
  toFun F := StrongDual.toWeakDual (unitaryPullback (WeakDual.toStrongDual F) u)
  map_add' F G := by apply WeakDual.toStrongDual.injective; ext a; rfl
  map_smul' c F := by apply WeakDual.toStrongDual.injective; ext a; rfl
  cont := WeakDual.continuous_of_continuous_eval (fun a =>
    WeakDual.eval_continuous ((u : M) * a * star (u : M)))

lemma unitaryOrbitHull_invariant (F : StrongDual ℂ M) (u : unitary M)
    {H : StrongDual ℂ M} (hH : H ∈ unitaryOrbitHull F) :
    unitaryPullback H u ∈ unitaryOrbitHull F := by
  have hconv : Convex ℝ (unitaryOrbitHull F) := (convex_convexHull ℝ _).closure
  have hclosed : IsClosed (unitaryOrbitHull F) := isClosed_closure
  apply closure_minimal (t := (unitaryDualEquiv u) ⁻¹' unitaryOrbitHull F) _
    (hclosed.preimage (unitaryDualEquiv u).continuous) hH
  apply convexHull_min _
    (hconv.linear_preimage ((unitaryDualEquiv u).toLinearEquiv.restrictScalars ℝ).toLinearMap)
  rintro _ ⟨v, rfl⟩
  change unitaryPullback (unitaryPullback F v) u ∈ unitaryOrbitHull F
  rw [unitaryPullback_mul]
  exact subset_closure (subset_convexHull ℝ _ (Set.mem_range_self (v * u)))

lemma weakOrbitClosure_invariant (F : StrongDual ℂ M) (u : unitary M)
    {H : WeakDual ℂ M} (hH : H ∈ weakFunctionalClosure (unitaryOrbitHull F)) :
    weakUnitaryPullback u H ∈ weakFunctionalClosure (unitaryOrbitHull F) := by
  apply closure_minimal (t := (weakUnitaryPullback u) ⁻¹'
    weakFunctionalClosure (unitaryOrbitHull F)) _
    (isClosed_closure.preimage (weakUnitaryPullback u).continuous) hH
  rintro _ ⟨G, hG, rfl⟩
  exact subset_closure ⟨unitaryPullback G u, unitaryOrbitHull_invariant F u hG, rfl⟩

lemma weakOrbitClosure_convex (F : StrongDual ℂ M) :
    Convex ℝ (weakFunctionalClosure (unitaryOrbitHull F)) := by
  have hsmul : ContinuousConstSMul ℝ (WeakDual ℂ M) :=
    ⟨fun r => WeakDual.continuous_of_continuous_eval (fun a =>
      (WeakDual.eval_continuous a).const_smul r)⟩
  have hHull : Convex ℝ (unitaryOrbitHull F) :=
    (convex_convexHull ℝ (Set.range (unitaryPullback F))).closure
  let L : StrongDual ℂ M →ₗ[ℝ] WeakDual ℂ M :=
    { toFun := StrongDual.toWeakDual
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hImage : Convex ℝ (L '' unitaryOrbitHull F) := hHull.linear_image L
  have hClosed : Convex ℝ (closure (L '' unitaryOrbitHull F)) :=
    @Convex.closure ℝ (WeakDual ℂ M) _ _ _ _ _ _ hsmul _ hImage
  exact hClosed

/-- The weak predual embedding is real-linear. -/
def weakPredualRealMap (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) :
    WeakSpace ℂ X →ₗ[ℝ] WeakDual ℂ M where
  toFun := weakPredualMap e
  map_add' x y := by
    apply WeakDual.toStrongDual.injective
    ext a
    change star (e.symm a ((toWeakSpace ℂ X).symm (x + y))) = _
    simp only [map_add, star_add]
    rfl
  map_smul' r x := by
    apply WeakDual.toStrongDual.injective
    ext a
    change star (e.symm a ((r : ℂ) • (toWeakSpace ℂ X).symm x)) =
      (r : ℂ) • star (e.symm a ((toWeakSpace ℂ X).symm x))
    rw [map_smul, star_smul]
    simp only [Complex.star_def, Complex.conj_ofReal]

variable [PartialOrder M] [StarOrderedRing M]

omit [CompleteSpace X] [PartialOrder M] [StarOrderedRing M] in
lemma weakPredualOrbit_convex (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (F : StrongDual ℂ M) :
    Convex ℝ ((weakPredualMap e) ⁻¹' weakFunctionalClosure (unitaryOrbitHull F)) := by
  intro x hx y hy a b ha hb hab
  have heq : weakPredualMap e (a • x + b • y) =
      a • weakPredualMap e x + b • weakPredualMap e y := by
    exact (weakPredualRealMap e).map_add (a • x) (b • y) |>.trans
      (congrArg₂ (· + ·) ((weakPredualRealMap e).map_smul a x)
        ((weakPredualRealMap e).map_smul b y))
  change weakPredualMap e (a • x + b • y) ∈ weakFunctionalClosure (unitaryOrbitHull F)
  rw [heq]
  exact (weakOrbitClosure_convex F) hx hy ha hb hab

lemma weakPredualOrbit_invariant (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (F : StrongDual ℂ M)
    (u : unitary M) :
    Set.MapsTo (weakIsometry (unitaryPredualAction e u))
      ((weakPredualMap e) ⁻¹' weakFunctionalClosure (unitaryOrbitHull F))
      ((weakPredualMap e) ⁻¹' weakFunctionalClosure (unitaryOrbitHull F)) := by
  intro x hx
  have heq : weakPredualMap e (weakIsometry (unitaryPredualAction e u) x) =
      weakUnitaryPullback (star u) (weakPredualMap e x) := by
    apply WeakDual.toStrongDual.injective
    exact predualEmbedding_unitaryAction e u ((toWeakSpace ℂ X).symm x)
  change weakPredualMap e (weakIsometry (unitaryPredualAction e u) x) ∈
    weakFunctionalClosure (unitaryOrbitHull F)
  rw [heq]
  exact weakOrbitClosure_invariant F (star u) hx

omit [PartialOrder M] [StarOrderedRing M] in
lemma weakFunctionalClosure_eval_eq (K : Set (StrongDual ℂ M)) (a : M) (c : ℂ)
    (h : ∀ G ∈ K, G a = c) {F : WeakDual ℂ M} (hF : F ∈ weakFunctionalClosure K) :
    F a = c := by
  apply closure_minimal (t := {G : WeakDual ℂ M | G a = c}) _
    (isClosed_eq (WeakDual.eval_continuous a) continuous_const) hF
  rintro _ ⟨G, hG, rfl⟩
  exact h G hG

end KadisonRingrose
end BoundedHochschild

end

end OAI
