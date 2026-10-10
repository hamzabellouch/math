import OAI.GroupTheory.PolycyclicRecognition.Analysis.ConvexOrbit
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Convex

namespace OAI

/-! # Selecting a label in a finite linear group

Embedding a vector in the Euclidean product of all its group translates
provides an invariant strictly convex norm without changing the topology or
norm instances on the original height space.
-/

noncomputable section

namespace PolycyclicRecognition

open Set

variable {W E : Type*} [AddCommGroup W] [Module ℝ W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (Γ : Subgroup (W ≃ₗ[ℝ] W)) [Fintype Γ] (e : W →ₗ[ℝ] E)

/-- All group translates, recorded in a finite Euclidean product. -/
def finiteOrbitEmbedding : W →ₗ[ℝ] PiLp 2 (fun _ : Γ => E) :=
  (WithLp.linearEquiv 2 ℝ (Γ → E)).symm.toLinearMap.comp
    (LinearMap.pi (fun g : Γ => e.comp g.val.toLinearMap))

omit [Fintype Γ] in
@[simp] theorem finiteOrbitEmbedding_apply (w : W) (g : Γ) :
    finiteOrbitEmbedding Γ e w g = e (g.val w) := rfl

omit [Fintype Γ] in
theorem finiteOrbitEmbedding_injective (he : Function.Injective e) :
    Function.Injective (finiteOrbitEmbedding Γ e) := by
  intro w u h
  apply he
  have hh := congrArg (fun f : PiLp 2 (fun _ : Γ => E) => f 1) h
  simpa using hh

theorem finiteOrbitEmbedding_norm (g : Γ) (w : W) :
    ‖finiteOrbitEmbedding Γ e (g.val w)‖ = ‖finiteOrbitEmbedding Γ e w‖ := by
  rw [PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
  congr 1
  change (∑ k : Γ, ‖e ((k * g).val w)‖ ^ 2) = ∑ k : Γ, ‖e (k.val w)‖ ^ 2
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun _ => rfl)

/-- A member of a finite linear group lying pointwise in the convex orbit
of a finite family is one of the members of that family. -/
theorem exists_eq_label_of_finite_group_convex_orbit
    {J : Type*} [Finite J] (he : Function.Injective e)
    (B : Γ) (A : J → Γ)
    (hconv : ∀ w, B.val w ∈ convexHull ℝ (range fun j => (A j).val w)) :
    ∃ j, B = A j := by
  let L := finiteOrbitEmbedding Γ e
  have hinj : Function.Injective L := finiteOrbitEmbedding_injective Γ e he
  have hpoint (w : W) : ∃ j, B.val w = (A j).val w := by
    have hL : L (B.val w) ∈ convexHull ℝ (range fun j => L ((A j).val w)) := by
      have hh := mem_image_of_mem L (hconv w)
      rw [L.image_convexHull, ← range_comp] at hh
      exact hh
    have hm := mem_of_mem_convexHull_of_norm_eq
      (s := range fun j => L ((A j).val w))
      (r := ‖L w‖)
      (by rintro _ ⟨j, rfl⟩; exact (finiteOrbitEmbedding_norm Γ e (A j) w).le)
      hL (finiteOrbitEmbedding_norm Γ e B w)
    obtain ⟨j, hj⟩ := hm
    exact ⟨j, hinj hj.symm⟩
  obtain ⟨j, hj⟩ := exists_eq_of_pointwise_linear_selection B.val.toLinearMap
    (fun j => (A j).val.toLinearMap) hpoint
  refine ⟨j, Subtype.ext ?_⟩
  ext w
  exact LinearMap.congr_fun hj w

end PolycyclicRecognition

end

end OAI
