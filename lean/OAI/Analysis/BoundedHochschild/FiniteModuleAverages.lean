import OAI.Analysis.BoundedHochschild.EncodedMapFamilies
import OAI.Analysis.BoundedHochschild.RightModuleAveragingExistence

namespace OAI

/-! A finite family of completely bounded maps admits a simultaneous
right-module average, with each original complete bound retained. -/

noncomputable section

open Topology

namespace BoundedHochschild.KadisonRingrose

open HochschildComparison

universe u
variable {M X : Type u} [CStarAlgebra M] [PartialOrder M] [StarOrderedRing M]
  [NormedAddCommGroup X] [NormedSpace ℂ X] [CompleteSpace X]

def finiteFamilyAverageOrbit {I : Type*} (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) : Set (I → M → WeakDual ℂ X) :=
  {F | ∃ (k : ℕ) (m : Fin k → M), (∑ j, m j * star (m j) = 1) ∧
    F = fun i => weakOperatorImage e (finiteRightAverage m (T i))}

def weakFamilyAverageOrbit {I : Type*} (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M)
    (T : I → M →L[ℂ] M) : Set (I → M → WeakDual ℂ X) :=
  closure (finiteFamilyAverageOrbit e T)

theorem exists_finite_right_module_average [Nontrivial M]
    (e : StrongDual ℂ X ≃ₗᵢ⋆[ℂ] M) (hno : NoFiniteCentralSummand M)
    {n : ℕ} (T : Fin (n+1) → M →L[ℂ] M) (C : Fin (n+1) → ℝ)
    (hT : ∀ i, CompletelyBoundedEstimate (T i) (C i)) :
    ∃ S : Fin (n+1) → M →L[ℂ] M,
      (∀ i, ‖S i‖ ≤ C i ∧ ∀ a b, S i (a*b) = S i a * b) ∧
      (fun i => weakOperatorImage e (S i)) ∈ weakFamilyAverageOrbit e T := by
  obtain ⟨c, hi, ho, _⟩ := exists_properlyInfinite_matrix_columns e hno (n+1)
  let B := encodeMapFamily c T
  let D := ∑ i, ‖(c i : M)‖ * C i * ‖star (c i : M)‖
  have hB : CompletelyBoundedEstimate B D := encodeMapFamily_completelyBounded c T C hT
  have hB' : CompletelyBoundedEstimate B (D+1) :=
    ⟨by linarith [hB.1], fun k A => (hB.2 k A).trans
      (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg A))⟩
  obtain ⟨R, _, hRorb, hR⟩ := exists_right_module_average e hno B
    (by linarith [hB.1] : 0 < D+1) hB'
  let S (i : Fin (n+1)) := leftSandwichMap (star (c i : M)) (c i : M) R
  have he (i : Fin (n+1)) :
      leftSandwichMap (star (c i : M)) (c i : M) B = T i :=
    extract_encodeMapFamily c hi ho T i
  have horb (i : Fin (n+1)) : weakOperatorImage e (S i) ∈ weakRightAverageOrbit e (T i) := by
    have h := weakLeftSandwich_mapsTo_orbit e (star (c i : M)) (c i : M) B hRorb
    rwa [weakLeftSandwich_image, he] at h
  refine ⟨S, fun i => ⟨?_, ?_⟩, ?_⟩
  · obtain ⟨U, hU, hUS⟩ := weakOperatorBall_realize e (hT i).1
      (weakRightAverageOrbit_subset_ball e hno (T i) (hT i) (horb i))
    have heq := weakOperatorImage_injective e hUS
    exact heq ▸ hU
  · intro a b
    change star (c i : M) * R ((c i : M) * (a*b)) =
      (star (c i : M) * R ((c i : M) * a)) * b
    rw [← mul_assoc (c i : M) a b, hR, mul_assoc]
  · let E (F : M → WeakDual ℂ X) : Fin (n+1) → M → WeakDual ℂ X :=
      fun i => weakLeftSandwich e (star (c i : M)) (c i : M) F
    have hEc : Continuous E := continuous_pi (fun i => weakLeftSandwich_continuous e _ _)
    have hmap : Set.MapsTo E (weakOperatorImage e '' rightAverageOrbit B)
        (finiteFamilyAverageOrbit e T) := by
      rintro F ⟨U, ⟨k, m, hm, rfl⟩, rfl⟩
      refine ⟨k, m, hm, ?_⟩
      funext i
      dsimp [E]
      rw [weakLeftSandwich_image, leftSandwichMap_rightAverage, he]
    have hh := hmap.closure hEc hRorb
    simpa only [E, weakLeftSandwich_image, S, weakFamilyAverageOrbit] using hh

end BoundedHochschild.KadisonRingrose

end

end OAI
