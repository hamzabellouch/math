import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Algebra.Module.Basic

namespace OAI

/-! # The complete space of continuous differences

A continuous function modulo additive constants is represented by its
pairwise differences. The inherited supremum norm is exactly the
oscillation norm needed for positive kernel contraction.
-/

open Set
noncomputable section
namespace RegularPointCoordinates
variable (X : Type*) [TopologicalSpace X]

def continuousDifferenceSubmodule : Submodule ℝ C(X × X, ℝ) where
  carrier := {d | ∀ x y z, d (x,z) = d (x,y) + d (y,z)}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg x y z
    change f (x,z) + g (x,z) = f (x,y) + g (x,y) + (f (y,z) + g (y,z))
    rw [hf x y z,hg x y z]
    ring
  smul_mem' := by
    intro a f hf x y z
    change a * f (x,z) = a * f (x,y) + a * f (y,z)
    rw [hf x y z,mul_add]

instance continuousDifferenceSubmodule_closed : IsClosed (continuousDifferenceSubmodule X : Set C(X × X, ℝ)) := by
  change IsClosed {d : C(X × X, ℝ) | ∀ x y z, d (x,z) = d (x,y) + d (y,z)}
  simp_rw [ofPred_forall]
  exact isClosed_iInter fun x => isClosed_iInter fun y => isClosed_iInter fun z =>
    isClosed_eq (continuous_eval_const (x,z))
      ((continuous_eval_const (x,y)).add (continuous_eval_const (y,z)))

abbrev ContinuousDifference := continuousDifferenceSubmodule X

def continuousDifference (f : C(X, ℝ)) : ContinuousDifference X :=
  ⟨⟨fun p => f p.1 - f p.2,
    (f.continuous.comp continuous_fst).sub (f.continuous.comp continuous_snd)⟩,
    fun _ _ _ => by dsimp; ring⟩

def differenceValue (d : ContinuousDifference X) (x₀ : X) : C(X, ℝ) :=
  ⟨fun x => d.val (x,x₀), d.val.continuous.comp (continuous_id.prodMk continuous_const)⟩

@[simp] theorem differenceValue_apply (d : ContinuousDifference X) (x₀ x : X) :
    differenceValue X d x₀ x = d.val (x,x₀) := rfl

theorem continuousDifference_diagonal (d : ContinuousDifference X) (x : X) : d.val (x,x)=0 := by
  have h := d.property x x x
  linarith

theorem differenceValue_sub (d : ContinuousDifference X) (x₀ x y : X) :
    differenceValue X d x₀ x - differenceValue X d x₀ y = d.val (x,y) := by
  have h := d.property x y x₀
  change d.val (x,x₀) - d.val (y,x₀) = _
  linarith

@[simp] theorem continuousDifference_value (d : ContinuousDifference X) (x₀ : X) :
    continuousDifference X (differenceValue X d x₀) = d := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro p
  exact differenceValue_sub X d x₀ p.1 p.2

theorem ContinuousDifference.norm_le [CompactSpace X] {d : ContinuousDifference X} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x y, |d.val (x,y)| ≤ C) : ‖d‖ ≤ C :=
  (ContinuousMap.norm_le d.val hC).mpr fun p => h p.1 p.2

end RegularPointCoordinates

end

end OAI
