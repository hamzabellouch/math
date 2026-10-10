import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Abel

namespace OAI

/-! # Inverting a map whose error raises a finite filtration

The fixed-point correction terminates after the filtration length. This
gives a concrete inverse for triangular polynomial translations.
-/

noncomputable section
namespace PolycyclicRecognition

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

def filteredNewton (f : V → V) (y : V) : ℕ → V
  | 0 => 0
  | n + 1 => filteredNewton f y n + (y - f (filteredNewton f y n))

theorem filteredNewton_error_mem (F : ℕ → Submodule ℝ V) (hF0 : F 0 = ⊤)
    (f : V → V)
    (hraise : ∀ k x y, x - y ∈ F k → (f x - f y) - (x - y) ∈ F (k + 1))
    (y : V) (n : ℕ) : y - f (filteredNewton f y n) ∈ F n := by
  induction n with
  | zero => rw [hF0]; exact Submodule.mem_top
  | succ n ih =>
    have hstep : filteredNewton f y (n + 1) - filteredNewton f y n ∈ F n := by
      simpa only [filteredNewton, add_sub_cancel_left] using ih
    have hh := hraise n (filteredNewton f y (n + 1)) (filteredNewton f y n) hstep
    have heq : y - f (filteredNewton f y (n + 1)) =
        -((f (filteredNewton f y (n + 1)) - f (filteredNewton f y n)) -
          (filteredNewton f y (n + 1) - filteredNewton f y n)) := by
      rw [filteredNewton]
      abel
    rw [heq]
    exact (F (n + 1)).neg_mem hh

theorem filteredNewton_right_inverse (F : ℕ → Submodule ℝ V) (hF0 : F 0 = ⊤)
    {c : ℕ} (hFc : F c = ⊥) (f : V → V)
    (hraise : ∀ k x y, x - y ∈ F k → (f x - f y) - (x - y) ∈ F (k + 1))
    (y : V) : f (filteredNewton f y c) = y := by
  have hh := filteredNewton_error_mem F hF0 f hraise y c
  rw [hFc, Submodule.mem_bot] at hh
  exact (sub_eq_zero.mp hh).symm

theorem injective_of_raises_difference_filtration
    (F : ℕ → Submodule ℝ V) (hF0 : F 0 = ⊤) {c : ℕ} (hFc : F c = ⊥)
    (f : V → V)
    (hraise : ∀ k x y, x - y ∈ F k → (f x - f y) - (x - y) ∈ F (k + 1)) :
    Function.Injective f := by
  intro x y hxy
  have hm : ∀ k, x - y ∈ F k := by
    intro k
    induction k with
    | zero => rw [hF0]; exact Submodule.mem_top
    | succ k ih =>
      have hh := hraise k x y ih
      rw [hxy, sub_self, zero_sub] at hh
      exact (F (k + 1)).neg_mem_iff.mp hh
  have hh := hm c
  rw [hFc, Submodule.mem_bot] at hh
  exact sub_eq_zero.mp hh

theorem bijective_of_raises_difference_filtration
    (F : ℕ → Submodule ℝ V) (hF0 : F 0 = ⊤) {c : ℕ} (hFc : F c = ⊥)
    (f : V → V)
    (hraise : ∀ k x y, x - y ∈ F k → (f x - f y) - (x - y) ∈ F (k + 1)) :
    Function.Bijective f :=
  ⟨injective_of_raises_difference_filtration F hF0 hFc f hraise,
    fun y => ⟨filteredNewton f y c, filteredNewton_right_inverse F hF0 hFc f hraise y⟩⟩

variable [TopologicalSpace V] [IsTopologicalAddGroup V]

omit [Module ℝ V] in
theorem continuous_filteredNewton (f : V → V) (hf : Continuous f) (n : ℕ) :
    Continuous (fun y => filteredNewton f y n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact ih.add (continuous_id.sub (hf.comp ih))

omit [Module ℝ V] in
theorem continuous_parametric_filteredNewton (f : V → V → V)
    (hf : Continuous (fun p : V × V => f p.1 p.2)) (n : ℕ) :
    Continuous (fun p : V × V => filteredNewton (f p.1) p.2 n) := by
  induction n with
  | zero => exact continuous_const
  | succ n ih => exact ih.add (continuous_snd.sub (hf.comp (continuous_fst.prodMk ih)))

def homeomorphOfRaisesDifferenceFiltration
    (F : ℕ → Submodule ℝ V) (hF0 : F 0 = ⊤) {c : ℕ} (hFc : F c = ⊥)
    (f : V → V) (hf : Continuous f)
    (hraise : ∀ k x y, x - y ∈ F k → (f x - f y) - (x - y) ∈ F (k + 1)) : V ≃ₜ V where
  toFun := f
  invFun y := filteredNewton f y c
  left_inv x := (injective_of_raises_difference_filtration F hF0 hFc f hraise)
    (filteredNewton_right_inverse F hF0 hFc f hraise (f x))
  right_inv := filteredNewton_right_inverse F hF0 hFc f hraise
  continuous_toFun := hf
  continuous_invFun := continuous_filteredNewton f hf c

end PolycyclicRecognition

end

end OAI
