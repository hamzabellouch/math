import Mathlib
import OAI.Analysis.Commutator.HilbertTensors2

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct

namespace Kadison.PreHilbert

open Function

lemma pure_update_add (E : PreHilbert) (n : ℕ) (v : Fin n → E) (i : Fin n) (x y : E) :
    pure E n (update v i (x + y)) =
      pure E n (update v i x) + pure E n (update v i y) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp [pure_succ, Fin.tail_update_zero, TensorProduct.add_tmul]
    | succ i =>
      simp only [pure_succ, Fin.tail_update_succ, update_of_ne (Fin.succ_ne_zero i).symm]
      rw [ih, TensorProduct.tmul_add]

lemma pure_update_smul (E : PreHilbert) (n : ℕ) (v : Fin n → E) (i : Fin n) (c : ℂ) (x : E) :
    pure E n (update v i (c • x)) = c • pure E n (update v i x) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    cases i using Fin.cases with
    | zero => simp [pure_succ, Fin.tail_update_zero, TensorProduct.smul_tmul']
    | succ i =>
      simp only [pure_succ, Fin.tail_update_succ, update_of_ne (Fin.succ_ne_zero i).symm]
      rw [ih, TensorProduct.tmul_smul]

def pureMultilinear (E : PreHilbert) (n : ℕ) :
    MultilinearMap ℂ (fun _ : Fin n => E) (power E n) where
  toFun := pure E n
  map_update_add' := by
    intro inst v i x y
    have hi : inst = instDecidableEqFin n := Subsingleton.elim _ _
    subst inst
    exact pure_update_add E n v i x y
  map_update_smul' := by
    intro inst v i c x
    have hi : inst = instDecidableEqFin n := Subsingleton.elim _ _
    subst inst
    exact pure_update_smul E n v i c x

def hilbertPureMultilinear (E : PreHilbert) (n : ℕ) :
    MultilinearMap ℂ (fun _ : Fin n => E) (hilbertPower E n) :=
  (UniformSpace.Completion.toComplL : power E n →L[ℂ] hilbertPower E n).toLinearMap.compMultilinearMap
    (pureMultilinear E n)

end Kadison.PreHilbert
end

end OAI
