import OAI.NumberTheory.Ostmann.Characters.DiagonalEstimateComplex
import OAI.NumberTheory.Ostmann.Construction.RowDiagonal

namespace OAI

open Erdos970

noncomputable section
open scoped BigOperators ComplexConjugate
namespace Ostmann.Characters.DiagonalEstimate
open Ostmann.Construction
attribute [local instance] Classical.propDecidable

theorem finite_root_pairing {H K : Type*} [Fintype H] [Fintype K] [DecidableEq K]
    (root : H→K) (f g : H→ℂ) :
    (∑s,(∑h,if root h=s then f h else 0)*conj (∑h,if root h=s then g h else 0)) =
      ∑h,∑h',if root h'=root h then f h*conj (g h') else 0 := by
  simp only [map_sum,Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h' hh'
  simp only [apply_ite,map_zero,ite_mul,zero_mul,mul_zero]
  by_cases he : root h = root h'
  · simp [he]
  · simp [he,Ne.symm he]

theorem refinedRowDiagonal_eq_root_pairs
    {A H K P : Type*} [Fintype A] [Fintype H] [Fintype K] [DecidableEq K] [DecidableEq P]
    (μ : FinitePrior A) (root : H→K) (prod : A→P) (tag : A→H→ℚ) (F : A→H→ℂ)
    (hrel : ∀x y h h',μ.mass x≠0 → μ.mass y≠0 → F x h≠0 → F y h'≠0 →
      (tag y h'=tag x h ↔ prod y=prod x ∧ root h'=root h)) :
    refinedRowDiagonal (fun a:A×H=>μ.mass a.1) (fun a=>tag a.1 a.2) (fun a=>F a.1 a.2) =
      ∑x,∑y,((μ.mass x*μ.mass y:ℝ):ℂ)*
        (if prod y=prod x then
          ∑s,(∑h,if root h=s then F x h else 0)*conj (∑h,if root h=s then F y h else 0)
        else 0) := by
  simp only [refinedRowDiagonal,diagonalComplex,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  rw [finite_root_pairing]
  by_cases hx0 : μ.mass x=0
  · simp [hx0]
  by_cases hy0 : μ.mass y=0
  · simp [hy0]
  by_cases hp : prod y=prod x
  · simp only [hp,ite_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h hh
    apply Finset.sum_congr rfl
    intro h' hh'
    by_cases hf : F x h=0
    · simp [hf]
    by_cases hg : F y h'=0
    · simp [hg]
    have hr := hrel x y h h' hx0 hy0 hf hg
    simp only [hp,true_and] at hr
    simp only [hr]
    split_ifs <;> simp only [map_mul,Complex.conj_ofReal,Complex.ofReal_mul,mul_zero]
    ring
  · simp only [hp,ite_false,mul_zero]
    apply Finset.sum_eq_zero
    intro h hh
    apply Finset.sum_eq_zero
    intro h' hh'
    by_cases hf : F x h=0
    · simp [hf]
    by_cases hg : F y h'=0
    · simp [hg]
    have ht : tag y h'≠tag x h := fun he=>hp ((hrel x y h h' hx0 hy0 hf hg).mp he).1
    exact ite_eq_right ht

end Ostmann.Characters.DiagonalEstimate

end

end OAI
