import OAI.GroupTheory.PolycyclicRecognition.Geometry.LieWordDifference
import OAI.GroupTheory.PolycyclicRecognition.Algebra.CollinearDynkin
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FilteredBijection

namespace OAI

/-! # Global inverses for nilpotent BCH translations

Axis normalization fixes the linear term. Every other term raises the
lower central series, so the finite correction construction applies.
-/

noncomputable section
namespace PolycyclicRecognition

open LieModule

variable {L : Type*} [LieRing L] [LieAlgebra ℝ L]

theorem finiteDynkinPolynomial_collinear_eq_linear {c n : ℕ}
    (coeff : DynkinCoefficients c n) (a : Fin n → ℝ) (v : L) :
    finiteDynkinPolynomial coeff (fun i => a i • v) =
      finiteDynkinLinearPart coeff (fun i => a i • v) := by
  have hw (k : ℕ) (w : Fin (k + 1) → Fin n) :
      evalBracketWord (fun i => a i • v) (rightNestedWord k w) =
        wordLinearPart (rightNestedWord k w) (fun i => a i • v) := by
    cases k with
    | zero => rfl
    | succ k => rw [eval_rightNestedWord_succ_collinear]; rfl
  simp only [finiteDynkinPolynomial, finiteDynkinLinearPart, LinearMap.sum_apply,
    LinearMap.smul_apply, hw]

theorem finiteDynkinPolynomial_single_eq_linear {c n : ℕ}
    (coeff : DynkinCoefficients c n) (i : Fin n) (v : L) :
    finiteDynkinPolynomial coeff (Pi.single i v) =
      finiteDynkinLinearPart coeff (Pi.single i v) := by
  classical
  have heq : (Pi.single i v : Fin n → L) =
      fun j => ((Pi.single i (1 : ℝ) : Fin n → ℝ) j) • v := by
    funext j
    by_cases h : j = i <;> simp [h]
  rw [heq]
  exact finiteDynkinPolynomial_collinear_eq_linear coeff _ v

theorem binaryDynkinLinearPart {c : ℕ} (coeff : DynkinCoefficients c 2)
    (haxis : ∀ (i : Fin 2) (v : L), finiteDynkinPolynomial coeff (Pi.single i v) = v)
    (x y : L) : finiteDynkinLinearPart coeff ![x, y] = x + y := by
  have hsplit : ![x, y] = (Pi.single 0 x : Fin 2 → L) + Pi.single 1 y := by
    funext i
    fin_cases i <;> simp
  rw [hsplit, map_add, ← finiteDynkinPolynomial_single_eq_linear,
    ← finiteDynkinPolynomial_single_eq_linear, haxis, haxis]

theorem binaryDynkin_raises_difference {c : ℕ} (coeff : DynkinCoefficients c 2)
    (haxis : ∀ (i : Fin 2) (v : L), finiteDynkinPolynomial coeff (Pi.single i v) = v)
    (a : L) (k : ℕ) (x y : L) (hxy : x - y ∈ lowerCentralSeries ℝ L L k) :
    (finiteDynkinPolynomial coeff ![a, x] - finiteDynkinPolynomial coeff ![a, y]) -
        (x - y) ∈ lowerCentralSeries ℝ L L (k + 1) := by
  have hh := finiteDynkinPolynomial_sub_linear_mem_succ coeff ![a, x] ![a, y] k (by
    intro i
    fin_cases i
    · simp
    · exact hxy)
  have hdiff : ![a, x] - ![a, y] = ![0, x - y] := by
    funext i
    fin_cases i <;> simp
  rw [hdiff, binaryDynkinLinearPart coeff haxis, zero_add] at hh
  exact hh

theorem bijective_binaryDynkin_translation {c : ℕ} (coeff : DynkinCoefficients c 2)
    (haxis : ∀ (i : Fin 2) (v : L), finiteDynkinPolynomial coeff (Pi.single i v) = v)
    {d : ℕ} (hd : lowerCentralSeries ℝ L L d = ⊥) (a : L) :
    Function.Bijective (fun x => finiteDynkinPolynomial coeff ![a, x]) := by
  apply bijective_of_raises_difference_filtration
    (fun k => (lowerCentralSeries ℝ L L k).toSubmodule) (by simp)
    (congrArg LieSubmodule.toSubmodule hd)
  exact binaryDynkin_raises_difference coeff haxis a

theorem binaryDynkin_raises_left_difference {c : ℕ} (coeff : DynkinCoefficients c 2)
    (haxis : ∀ (i : Fin 2) (v : L), finiteDynkinPolynomial coeff (Pi.single i v) = v)
    (a : L) (k : ℕ) (x y : L) (hxy : x - y ∈ lowerCentralSeries ℝ L L k) :
    (finiteDynkinPolynomial coeff ![x, a] - finiteDynkinPolynomial coeff ![y, a]) -
        (x - y) ∈ lowerCentralSeries ℝ L L (k + 1) := by
  have hh := finiteDynkinPolynomial_sub_linear_mem_succ coeff ![x, a] ![y, a] k (by
    intro i
    fin_cases i
    · exact hxy
    · simp)
  have hdiff : ![x, a] - ![y, a] = ![x - y, 0] := by
    funext i
    fin_cases i <;> simp
  rw [hdiff, binaryDynkinLinearPart coeff haxis, add_zero] at hh
  exact hh

end PolycyclicRecognition

end

end OAI
