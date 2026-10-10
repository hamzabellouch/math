import Mathlib.LinearAlgebra.Multilinear.Basic

namespace OAI

/-! # The bilinear map obtained by varying two distinct coordinates -/

noncomputable section
namespace PolycyclicRecognition
variable {K I W V : Type} [CommRing K] [DecidableEq I]
  [AddCommGroup W] [Module K W] [AddCommGroup V] [Module K V]

def multilinearCoordinatePair (F : MultilinearMap K (fun _ : I => W) V)
    (v : I → W) (i j : I) (hij : i ≠ j) : W →ₗ[K] W →ₗ[K] V where
  toFun x := F.toLinearMap (Function.update v i x) j
  map_add' x y := by
    ext z
    change F (Function.update (Function.update v i (x + y)) j z) =
      F (Function.update (Function.update v i x) j z) +
        F (Function.update (Function.update v i y) j z)
    rw [Function.update_comm hij (x + y) z v, F.map_update_add,
      Function.update_comm hij x z v, Function.update_comm hij y z v]
  map_smul' r x := by
    ext z
    change F (Function.update (Function.update v i (r • x)) j z) =
      r • F (Function.update (Function.update v i x) j z)
    rw [Function.update_comm hij (r • x) z v, F.map_update_smul,
      Function.update_comm hij x z v]

@[simp] theorem multilinearCoordinatePair_apply
    (F : MultilinearMap K (fun _ : I => W) V) (v : I → W)
    (i j : I) (hij : i ≠ j) (x y : W) :
    multilinearCoordinatePair F v i j hij x y =
      F (Function.update (Function.update v i x) j y) := rfl

omit [AddCommGroup W] in
theorem update_pair_comp_swap (v : I → W) (i j : I) (hij : i ≠ j) (x y : W) :
    Function.update (Function.update v i x) j y ∘ Equiv.swap i j =
      Function.update (Function.update v i y) j x := by
  funext k
  by_cases hki : k = i
  · subst k; simp [hij]
  · by_cases hkj : k = j
    · subst k; simp [hij]
    · simp [Function.comp_apply, Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]

end PolycyclicRecognition

end

end OAI
