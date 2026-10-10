import OAI.Analysis.PlanarPacking.ResidualBase

namespace OAI

/-!
# Error bounds for cardinal interpolation

Norm bounds for the inverse interpolation operator control the distance from the finite coefficient families to the exact solution.
-/

namespace SharpPlanar
open Numerical
noncomputable def exactList (a : Bool) : X := if a then exactList₂ else exactList₁
noncomputable def coefficientError (a : Bool) : X := tableList a-exactList a
lemma coefficientError_equation (a : Bool) :
    coefficientError a-S (coefficientError (!a))=tableResidual a := by
  cases a
  · simp only [coefficientError,exactList,Bool.false_eq_true,ite_false,Bool.not_false,ite_true,map_sub,tableResidual]
    rw [← exactLists_equations.1]; abel
  · simp only [coefficientError,exactList,ite_true,Bool.not_true,map_sub,tableResidual]
    rw [← exactLists_equations.2]; abel
lemma pair_error_plus :
    coefficientError false+coefficientError true-signedS false (coefficientError false+coefficientError true)=
      tableResidual false+tableResidual true := by
  change _-S (_+_)=_
  rw [map_add,← coefficientError_equation false,← coefficientError_equation true]
  simp only [Bool.not_false,Bool.not_true]
  abel
lemma pair_error_minus :
    coefficientError false-coefficientError true-signedS true (coefficientError false-coefficientError true)=
      tableResidual false-tableResidual true := by
  change _- -S (_-_)=_
  rw [map_sub,← coefficientError_equation false,← coefficientError_equation true]
  simp only [Bool.not_false,Bool.not_true]
  abel
lemma discard_add_bound (x y : X) :
    ‖x+y-IF (RF (x+y))‖ ≤ ‖x-IF (RF x)‖+‖y-IF (RF y)‖ := by
  rw [map_add,map_add]
  convert norm_add_le (x-IF (RF x)) (y-IF (RF y)) using 1
  congr 1
  abel
lemma discard_sub_bound (x y : X) :
    ‖x-y-IF (RF (x-y))‖ ≤ ‖x-IF (RF x)‖+‖y-IF (RF y)‖ := by
  rw [map_sub,map_sub]
  convert norm_sub_le (x-IF (RF x)) (y-IF (RF y)) using 1
  congr 1
  abel
lemma pair_error_estimate {r t : ℝ}
    (hr : ∀ a, ‖RF (tableResidual a)‖ ≤ r)
    (ht : ∀ a, ‖tableResidual a-IF (RF (tableResidual a))‖ ≤ t) :
    ∀ a, ‖coefficientError a‖ ≤ 182*r+5080*t := by
  have hpr : ‖RF (tableResidual false+tableResidual true)‖ ≤ 2*r := by
    rw [map_add]; exact (norm_add_le _ _).trans (by linarith [hr false,hr true])
  have hmr : ‖RF (tableResidual false-tableResidual true)‖ ≤ 2*r := by
    rw [map_sub]; exact (norm_sub_le _ _).trans (by linarith [hr false,hr true])
  have hpt := (discard_add_bound (tableResidual false) (tableResidual true)).trans (add_le_add (ht false) (ht true))
  have hmt := (discard_sub_bound (tableResidual false) (tableResidual true)).trans (add_le_add (ht false) (ht true))
  have hp := interpolation_norm_bound false pair_error_plus
  have hm := interpolation_norm_bound true pair_error_minus
  have h1 : 2*‖coefficientError false‖ ≤ ‖coefficientError false+coefficientError true‖+‖coefficientError false-coefficientError true‖ := by
    have hh:=norm_add_le (coefficientError false+coefficientError true) (coefficientError false-coefficientError true)
    have he : coefficientError false+coefficientError true+(coefficientError false-coefficientError true)=(2:ℝ) • coefficientError false := by module
    rw [he,norm_smul,Real.norm_eq_abs,show |(2:ℝ)|=2 by norm_num] at hh
    exact hh
  have h2 : 2*‖coefficientError true‖ ≤ ‖coefficientError false+coefficientError true‖+‖coefficientError false-coefficientError true‖ := by
    have hh:=norm_sub_le (coefficientError false+coefficientError true) (coefficientError false-coefficientError true)
    have he : coefficientError false+coefficientError true-(coefficientError false-coefficientError true)=(2:ℝ) • coefficientError true := by module
    rw [he,norm_smul,Real.norm_eq_abs,show |(2:ℝ)|=2 by norm_num] at hh
    exact hh
  intro a
  cases a <;> linarith
end SharpPlanar

end OAI
