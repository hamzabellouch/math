import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import OAI.Geometry.NodalSets.Elliptic.RealLocalWeakDifferenceQuadratic

namespace OAI

namespace Yau
open MeasureTheory Set
noncomputable section

theorem real_L2_add_square_bound {α : Type*} [MeasurableSpace α] (mu : Measure α)
    (u v : α → ℝ) (hu : MemLp u 2 mu) (hv : MemLp v 2 mu) :
    (∫ x, (u x+v x)^2 ∂mu) ≤ 2*(∫ x, (u x)^2 ∂mu)+2*(∫ x, (v x)^2 ∂mu) := by
  rw [← integral_const_mul,← integral_const_mul,
    ← integral_add (hu.integrable_sq.const_mul 2) (hv.integrable_sq.const_mul 2)]
  apply integral_mono (hu.add hv).integrable_sq
    ((hu.integrable_sq.const_mul 2).add (hv.integrable_sq.const_mul 2))
  intro x
  change (u x+v x)^2 ≤ 2*(u x)^2+2*(v x)^2
  nlinarith [sq_nonneg (u x-v x)]

theorem real_compact_finite_coefficient_L2_bound {n m : ℕ} {K : Set (Coord n)}
    (hK : IsCompact K) (A : Coord n → Fin m → ℝ) (hA : ∀ j, Continuous (fun x ↦ A x j)) :
    ∃ C > 0, ∀ U : Fin m → Coord n → ℝ, (∀ j, MemLp (U j) 2 (volume.restrict K)) →
      MemLp (fun x ↦ ∑ j, A x j*U j x) 2 (volume.restrict K) ∧
      (∫ x in K, (∑ j, A x j*U j x)^2) ≤ C*(∑ j, ∫ x in K, (U j x)^2) := by
  obtain ⟨B,hB,hb⟩ := (hK.image (continuous_pi hA)).isBounded.exists_pos_norm_le
  refine ⟨((m:ℝ)+1)*B^2,by positivity,fun U hU ↦ ?_⟩
  have hprod (j : Fin m) : MemLp (fun x ↦ A x j*U j x) 2 (volume.restrict K) := by
    obtain ⟨_,_,hbound⟩ := real_compact_multiplier_bound hK (fun x ↦ A x j) (hA j)
    exact (hbound (U j) (hU j)).1
  have hsum : MemLp (fun x ↦ ∑ j, A x j*U j x) 2 (volume.restrict K) :=
    memLp_finsetSum Finset.univ (fun j _ ↦ hprod j)
  refine ⟨hsum,?_⟩
  have hisum := integrable_finsetSum Finset.univ (fun j _ ↦ (hU j).integrable_sq)
  rw [← integral_finsetSum Finset.univ (fun j _ ↦ (hU j).integrable_sq),← integral_const_mul]
  apply setIntegral_mono_on hsum.integrable_sq (hisum.const_mul _) hK.measurableSet
  intro x hx
  have hcoef (j : Fin m) : (A x j)^2 ≤ B^2 := by
    have ht := (norm_le_pi_norm (A x) j).trans (hb _ ⟨x,hx,rfl⟩)
    rw [Real.norm_eq_abs] at ht
    nlinarith [sq_abs (A x j),abs_nonneg (A x j)]
  have hcoefsum := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcoef j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hcoefsum
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j ↦ A x j) (fun j ↦ U j x)
  have hn : 0 ≤ ∑ j, (U j x)^2 := Finset.sum_nonneg (fun _ _ ↦ sq_nonneg _)
  have hmul := mul_le_mul_of_nonneg_right hcoefsum hn
  have hextra := mul_nonneg (sq_nonneg B) hn
  nlinarith only [hCS,hmul,hextra]

end
end Yau

end OAI
