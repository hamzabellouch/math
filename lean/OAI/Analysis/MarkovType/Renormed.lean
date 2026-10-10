import OAI.Analysis.MarkovType.RenormingBasic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Topology.UniformSpace.Equiv
import Mathlib.Tactic.Ring

namespace OAI

noncomputable section

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

def Renormed (_N : EquivalentNorm X) : Type u := X

namespace Renormed

variable (N : EquivalentNorm X)

instance : AddCommGroup (Renormed N) := inferInstanceAs (AddCommGroup X)
instance : Module ℝ (Renormed N) := inferInstanceAs (Module ℝ X)

def ofOriginal (x : X) : Renormed N := x
def toOriginal (x : Renormed N) : X := x

@[simp] theorem toOriginal_ofOriginal (x : X) :
    toOriginal N (ofOriginal N x) = x := rfl

@[simp] theorem ofOriginal_toOriginal (x : Renormed N) :
    ofOriginal N (toOriginal N x) = x := rfl

instance : Norm (Renormed N) := ⟨fun x => N.p (toOriginal N x)⟩

private theorem normCore : NormedSpace.Core ℝ (Renormed N) where
  norm_nonneg x := apply_nonneg N.p (toOriginal N x)
  norm_smul c x := map_smul_eq_mul N.p c (toOriginal N x)
  norm_triangle x y := map_add_le_add N.p (toOriginal N x) (toOriginal N y)
  norm_eq_zero_iff x := N.eq_zero_iff (toOriginal N x)

instance : NormedAddCommGroup (Renormed N) := NormedAddCommGroup.ofCore (normCore N)
instance : NormedSpace ℝ (Renormed N) := NormedSpace.ofCore (normCore N)

@[simp] theorem norm_ofOriginal (x : X) : ‖ofOriginal N x‖ = N.p x := rfl

@[simp] theorem norm_eq (x : Renormed N) : ‖x‖ = N.p (toOriginal N x) := rfl

def linearEquiv : X ≃ₗ[ℝ] Renormed N where
  toFun := ofOriginal N
  invFun := toOriginal N
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def ofOriginalL : X →L[ℝ] Renormed N :=
  (linearEquiv N).toLinearMap.mkContinuous N.upper (fun x => N.upper_bound x)

def toOriginalL : Renormed N →L[ℝ] X :=
  (linearEquiv N).symm.toLinearMap.mkContinuous (1 / N.lower) (by
    intro x
    change ‖toOriginal N x‖ ≤ (1 / N.lower) * N.p (toOriginal N x)
    calc
      ‖toOriginal N x‖ ≤ N.p (toOriginal N x) / N.lower :=
        (le_div_iff₀ N.lower_pos).2 (by simpa only [mul_comm] using N.lower_bound (toOriginal N x))
      _ = (1 / N.lower) * N.p (toOriginal N x) := by ring)

@[simp] theorem ofOriginalL_apply (x : X) : ofOriginalL N x = ofOriginal N x := rfl

@[simp] theorem toOriginalL_apply (x : Renormed N) : toOriginalL N x = toOriginal N x := rfl

def continuousLinearEquiv : X ≃L[ℝ] Renormed N where
  toLinearEquiv := linearEquiv N
  continuous_toFun := (ofOriginalL N).continuous
  continuous_invFun := (toOriginalL N).continuous

def uniformEquiv : X ≃ᵤ Renormed N where
  toEquiv := (linearEquiv N).toEquiv
  uniformContinuous_toFun := (ofOriginalL N).uniformContinuous
  uniformContinuous_invFun := (toOriginalL N).uniformContinuous

instance [CompleteSpace X] : CompleteSpace (Renormed N) :=
  (uniformEquiv N).completeSpace_iff.mp inferInstance

end Renormed

end MarkovSuperreflexivity

end

end OAI
