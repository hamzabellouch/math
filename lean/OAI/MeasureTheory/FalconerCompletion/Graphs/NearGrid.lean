import Mathlib
import OAI.MeasureTheory.FalconerCompletion.Measures.AmbientGridCell4

namespace OAI

/-! Graph energies and pair estimates. -/

section
section
open Set MeasureTheory
open scoped ComplexConjugate RealInnerProductSpace
namespace GraphLiteralSupport
namespace Attempt4Near
open Set MeasureTheory Metric

def nearGridND {d : ℕ} (h : ℕ) (P Q : Fin d → ℤ) : Prop :=
  dist (ambientGridCenter h P) (ambientGridCenter h Q) ≤ 10*(d+1:ℝ)/(2:ℝ)^h

noncomputable instance nearGridND_decidable {d : ℕ} (h : ℕ) :
    DecidableRel (@nearGridND d h) := fun _ _ => Classical.propDecidable _

lemma nearGridND_symm {d h : ℕ} {P Q : Fin d → ℤ} :
    nearGridND h P Q ↔ nearGridND h Q P := by
  simp only [nearGridND,dist_comm]

theorem nearGridND_partner_card {d : ℕ} (h : ℕ) (P : Fin d → ℤ)
    (A : Finset (Fin d → ℤ)) :
    ((A.filter (nearGridND h P)).card:ℝ) ≤ (20*(d+1:ℝ)+5)^d := by
  have hh := ambientGridCenter_ball_card h (A.filter (nearGridND h P))
    (ambientGridCenter h P) (r := 10*(d+1:ℝ)/(2:ℝ)^h) (by positivity) (by
      intro Q hQ
      rw [dist_comm]
      exact (Finset.mem_filter.mp hQ).2)
  convert hh using 1
  congr 1
  field_simp
  ring

def nearGridPairND {d : ℕ} (h : ℕ)
    (a b : (Fin d → ℤ) × (Fin d → ℤ)) : Prop :=
  nearGridND h a.1 b.1 ∧ nearGridND h a.2 b.2

noncomputable instance nearGridPairND_decidable {d : ℕ} (h : ℕ) :
    DecidableRel (@nearGridPairND d h) := fun _ _ => Classical.propDecidable _

lemma nearGridPairND_symm {d h : ℕ} {a b : (Fin d → ℤ) × (Fin d → ℤ)} :
    nearGridPairND h a b ↔ nearGridPairND h b a := by
  simp only [nearGridPairND,nearGridND_symm]

theorem nearGridPairND_row_card {d : ℕ} (h : ℕ)
    (A B : Finset (Fin d → ℤ)) (a : (Fin d → ℤ) × (Fin d → ℤ)) :
    (((A.product B).filter (nearGridPairND h a)).card:ℝ) ≤
      (20*(d+1:ℝ)+5)^(2*d) := by
  have he : (A.product B).filter (nearGridPairND h a) =
      (A.filter (nearGridND h a.1)).product (B.filter (nearGridND h a.2)) := by
    ext b
    simp only [Finset.product_eq_sprod,Finset.mem_filter,Finset.mem_product,nearGridPairND]
    tauto
  rw [he,Finset.product_eq_sprod,Finset.card_product,Nat.cast_mul]
  calc
    _ ≤ (20*(d+1:ℝ)+5)^d*(20*(d+1:ℝ)+5)^d := mul_le_mul
      (nearGridND_partner_card h a.1 A) (nearGridND_partner_card h a.2 B)
      (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← pow_add,← two_mul]

theorem nearGridPairND_col_card {d : ℕ} (h : ℕ)
    (A B : Finset (Fin d → ℤ)) (b : (Fin d → ℤ) × (Fin d → ℤ)) :
    (((A.product B).filter (fun a => nearGridPairND h a b)).card:ℝ) ≤
      (20*(d+1:ℝ)+5)^(2*d) := by
  have he : (A.product B).filter (fun a => nearGridPairND h a b) =
      (A.product B).filter (nearGridPairND h b) := by
    ext a
    simp only [Finset.mem_filter,nearGridPairND_symm]
  rw [he]
  exact nearGridPairND_row_card h A B b

end Attempt4Near
end GraphLiteralSupport
end
end

end OAI
