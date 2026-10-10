import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dual.Defs
import OAI.Computability.PerfectCompleteness.Algebra.OutputCharacters
import OAI.Computability.PerfectCompleteness.Foundations.QuarterBalanceLemmas

namespace OAI

section

namespace PerfectCompleteness.BinaryDualCoordinates

open scoped BigOperators
open QuarterBalance (F2)
open SmallBiasSlice

noncomputable section

def toBool (a : F2) : Bool := decide (a ≠ 0)

def ofBool (b : Bool) : F2 := if b then 1 else 0

@[simp] theorem toBool_ofBool (b : Bool) : toBool (ofBool b) = b := by
  cases b <;> simp [toBool, ofBool]

@[simp] theorem ofBool_toBool (a : F2) : ofBool (toBool a) = a := by
  rcases QuarterBalance.scalar_cases a with rfl | rfl <;> simp [toBool, ofBool]

theorem toBool_injective : Function.Injective toBool := by
  intro a b h
  simpa using congrArg ofBool h

theorem ofBool_injective : Function.Injective ofBool := by
  intro a b h
  simpa using congrArg toBool h

@[simp] theorem bitSign_toBool (a : F2) : bitSign (toBool a) =
    QuarterBalance.sign a := by
  rcases QuarterBalance.scalar_cases a with rfl | rfl <;>
    simp [bitSign, toBool]

variable {I V : Type*} [Fintype I] [AddCommGroup V] [Module F2 V]

def coordinates (b : Module.Basis I F2 V) (x : V) : I → Bool :=
  fun i => toBool (b.coord i x)

theorem coordinates_injective (b : Module.Basis I F2 V) :
    Function.Injective (coordinates b) := by
  intro x y h
  apply b.equivFun.injective
  funext i
  have hi := toBool_injective (congrFun h i)
  simpa only [Module.Basis.equivFun_apply, Module.Basis.coord_apply] using hi

def frequency (b : Module.Basis I F2 V) (s : I → Bool) : Module.Dual F2 V :=
  rowCombination (fun i => b.coord i) s

theorem frequency_apply (b : Module.Basis I F2 V) (s : I → Bool) (x : V) :
    frequency b s x = ∑ i, if s i then b.coord i x else 0 := by
  classical
  simp only [frequency, rowCombination, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases s i <;> simp

@[simp] theorem frequency_apply_basis (b : Module.Basis I F2 V)
    (s : I → Bool) (j : I) : frequency b s (b j) = ofBool (s j) := by
  classical
  rw [frequency_apply, Finset.sum_eq_single j]
  · simp [Module.Basis.coord_apply, ofBool]
  · intro i _ hij
    simp [Module.Basis.coord_apply, Ne.symm hij]
  · simp

theorem frequency_injective (b : Module.Basis I F2 V) :
    Function.Injective (frequency b) := by
  intro s t h
  funext i
  apply ofBool_injective
  simpa using congrArg (fun f : Module.Dual F2 V => f (b i)) h

theorem frequency_surjective (b : Module.Basis I F2 V) :
    Function.Surjective (frequency b) := by
  intro f
  refine ⟨fun i => toBool (f (b i)), ?_⟩
  apply b.ext
  intro i
  simp

def frequencyEquiv (b : Module.Basis I F2 V) :
    (I → Bool) ≃ Module.Dual F2 V where
  toFun := frequency b
  invFun f i := toBool (f (b i))
  left_inv s := by funext i; simp
  right_inv f := by apply b.ext; intro i; simp

def character (f : Module.Dual F2 V) (x : V) : ℝ :=
  QuarterBalance.sign (f x)

@[simp] theorem character_zero (x : V) : character 0 x = 1 := by
  simp [character]

theorem character_add (f g : Module.Dual F2 V) (x : V) :
    character (f + g) x = character f x * character g x := by
  simp only [character, LinearMap.add_apply, QuarterBalance.sign_add]

@[simp] theorem abs_character (f : Module.Dual F2 V) (x : V) :
    |character f x| = 1 := QuarterBalance.abs_sign _

theorem character_frequency (b : Module.Basis I F2 V)
    (s : I → Bool) (x : V) :
    character (frequency b s) x = maskChar s (coordinates b x) := by
  classical
  apply character_rowCombination character character_zero character_add
    (fun i => b.coord i) (coordinates b)
  intro i y
  exact (bitSign_toBool (b.coord i y)).symm

variable {U : Type*} [AddCommGroup U] [Module F2 U]

def equationRows (b : Module.Basis I F2 V) (R : U →ₗ[F2] V) :
    I → Module.Dual F2 U := fun i => (b.coord i).comp R

def equations (b : Module.Basis I F2 V) (R : U →ₗ[F2] V) (x : U) : I → Bool :=
  coordinates b (R x)

theorem equations_eq_iff (b : Module.Basis I F2 V) (R : U →ₗ[F2] V)
    (x : U) (target : V) :
    equations b R x = coordinates b target ↔ R x = target :=
  ⟨fun h => coordinates_injective b h, fun h => congrArg (coordinates b) h⟩

omit [Fintype I] in
theorem character_equationRows (b : Module.Basis I F2 V)
    (R : U →ₗ[F2] V) (i : I) (x : U) :
    character (equationRows b R i) x = bitSign (equations b R x i) :=
  (bitSign_toBool _).symm

theorem rowCombination_equationRows (b : Module.Basis I F2 V)
    (R : U →ₗ[F2] V) (s : I → Bool) :
    rowCombination (equationRows b R) s = (frequency b s).comp R := by
  classical
  ext x
  simp only [equationRows, frequency, rowCombination, LinearMap.comp_apply,
    LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  cases s i <;> simp

theorem equationRows_independent (b : Module.Basis I F2 V)
    (R : U →ₗ[F2] V) (hR : Function.Surjective R) :
    Function.Injective (rowCombination (equationRows b R)) := by
  intro s t h
  apply frequency_injective b
  ext v
  obtain ⟨x, rfl⟩ := hR v
  rw [rowCombination_equationRows, rowCombination_equationRows] at h
  exact congrArg (fun f : Module.Dual F2 U => f x) h

theorem rowCombination_mem_dualRange (b : Module.Basis I F2 V)
    (R : U →ₗ[F2] V) (s : I → Bool) :
    rowCombination (equationRows b R) s ∈ LinearMap.range R.dualMap := by
  refine ⟨frequency b s, ?_⟩
  exact (rowCombination_equationRows b R s).symm

theorem character_affine_target (b : Module.Basis I F2 V)
    (T : U →ₗ[F2] V) (offset : V) (s : I → Bool) (x : U) :
    maskChar s (coordinates b (offset + T x)) =
      character (frequency b s) offset * character ((frequency b s).comp T) x := by
  rw [← character_frequency]
  simp only [character, map_add, LinearMap.comp_apply, QuarterBalance.sign_add]

end
end PerfectCompleteness.BinaryDualCoordinates

end

end OAI
