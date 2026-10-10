import Mathlib
import OAI.Combinatorics.KMedian.Compression.AffineElimination
import OAI.Combinatorics.KMedian.Compression.RationalScaling

namespace OAI

namespace MetricKMedian.IntegerLaw
open Finset
variable {α β : Type} [Fintype α] [Fintype β]

def reindex (μ : IntegerLaw α) (e : α ≃ β) : IntegerLaw β where
  denominator := μ.denominator
  denominator_pos := μ.denominator_pos
  numerator := fun b => μ.numerator (e.symm b)
  numerator_nonneg _b := μ.numerator_nonneg _
  total := (e.symm.sum_comp _).trans μ.total

theorem reindex_moment (μ : IntegerLaw α) (e : α ≃ β) (f : α → ℚ) :
    (∑ b, (μ.reindex e).rational.weight b*f (e.symm b))=
      ∑ a, μ.rational.weight a*f a := by
  exact e.symm.sum_comp (fun a => μ.rational.weight a*f a)

end MetricKMedian.IntegerLaw
namespace MetricKMedian.IntegerBranching
open Finset
variable {n : ℕ}

def branchNumerator (p : Fin n → ℚ) (i : Fin n) (b : Fin 2) : ℤ :=
  if b=0 then RationalScaling.numerator p i
    else RationalScaling.denominator p-RationalScaling.numerator p i

theorem branchNumerator_nonneg (p : Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (i : Fin n) (b : Fin 2) :
    0 ≤ branchNumerator p i b := by
  have hD : (0:ℚ) < RationalScaling.denominator p := by
    exact_mod_cast RationalScaling.denominator_pos p
  have hA0 : (0:ℤ) ≤ RationalScaling.numerator p i := by
    have hh := mul_nonneg (hp i).1 hD.le
    rw [← RationalScaling.numerator_cast] at hh
    exact_mod_cast hh
  have hA1 : RationalScaling.numerator p i ≤ RationalScaling.denominator p := by
    have hh := mul_le_mul_of_nonneg_right (hp i).2 hD.le
    rw [one_mul,← RationalScaling.numerator_cast] at hh
    exact_mod_cast hh
  dsimp only [branchNumerator]
  split_ifs
  · exact hA0
  · exact sub_nonneg.mpr hA1

def branch (μ : IntegerLaw (Fin n)) (p : Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) : IntegerLaw (Fin n × Fin 2) where
  denominator := μ.denominator*RationalScaling.denominator p
  denominator_pos := mul_pos μ.denominator_pos (RationalScaling.denominator_pos p)
  numerator := let v := Vector.ofFn (fun i => Vector.ofFn (fun b =>
    μ.numerator i*branchNumerator p i b))
    fun a => v[a.1.val][a.2.val]
  numerator_nonneg a := by
    simp only [Vector.getElem_ofFn]
    exact mul_nonneg (μ.numerator_nonneg _) (branchNumerator_nonneg p hp _ _)
  total := by
    simp only [Vector.getElem_ofFn,Fin.eta]
    rw [Fintype.sum_prod_type]
    simp only [Fin.sum_univ_two,branchNumerator]
    norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
    simp only [mul_sub,add_sub_cancel,← sum_mul,μ.total]

theorem branch_moment (μ : IntegerLaw (Fin n)) (p : Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (f : Fin n → Fin 2 → ℚ) :
    (∑ a, (branch μ p hp).rational.weight a*f a.1 a.2)=
      ∑ i, μ.rational.weight i*(p i*f i 0+(1-p i)*f i 1) := by
  have hD : (RationalScaling.denominator p:ℚ) ≠ 0 := by
    exact_mod_cast (RationalScaling.denominator_pos p).ne'
  have hM : (μ.denominator:ℚ) ≠ 0 := by exact_mod_cast μ.denominator_pos.ne'
  simp only [IntegerLaw.rational,branch,Vector.getElem_ofFn,Fin.eta]
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two,branchNumerator]
  norm_num only [show (1:Fin 2) ≠ 0 by decide,ite_true,ite_false]
  simp only [Int.cast_mul,Int.cast_sub,RationalScaling.numerator_cast]
  apply sum_congr rfl
  intro i _
  field_simp

theorem branch_denominator (μ : IntegerLaw (Fin n)) (p : Fin n → ℚ)
    (hp : ∀ i, 0 ≤ p i ∧ p i ≤ 1) (L : ℕ)
    (hden : ∀ i, ((p i).den:ℤ) ≤ (2:ℤ)^L) :
    (branch μ p hp).denominator ≤ μ.denominator*(2:ℤ)^(L*n) := by
  apply mul_le_mul_of_nonneg_left _ μ.denominator_pos.le
  simpa only [Fintype.card_fin] using RationalScaling.denominator_bound p L hden

end MetricKMedian.IntegerBranching

end OAI
