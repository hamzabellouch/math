import OAI.NumberTheory.Ostmann.Tree.ConstrainedCharacterSum
import OAI.NumberTheory.Ostmann.Tree.QuartetFiberIndependence

namespace OAI

namespace Ostmann.Tree
noncomputable section
open scoped BigOperators
open Density

theorem average_pi_product_real {I : Type*} [Fintype I] [DecidableEq I]
    {A : I → Type*} [∀ i,Fintype (A i)] (f : ∀ i,A i → ℝ) :
    average (fun x : ∀ i,A i => ∏ i,f i (x i)) = ∏ i,average (f i) := by
  classical
  simp only [average,Fintype.card_pi,Nat.cast_prod,Finset.prod_inv_distrib,
    Finset.prod_mul_distrib,← Fintype.prod_sum]

variable {I C : Type*} [Fintype I] [DecidableEq I] [CommGroup C] [Fintype C] [DecidableEq C]
variable {A : I → Type*} [∀ i,Fintype (A i)]

def constrainedMajorant (e : I → C ≃ C) (B : ∀ i,C → A i → ℝ) (x : ∀ i,A i) : ℝ :=
  ∑ ρ : I → C,if (∏ i,e i (ρ i))=1 then ∏ i,B i (ρ i) (x i) else 0

omit [∀ i,Fintype (A i)] in
theorem constrainedMajorant_nonneg (e : I → C ≃ C) (B : ∀ i,C → A i → ℝ)
    (hB : ∀ i χ x,0≤B i χ x) (x : ∀ i,A i) : 0≤constrainedMajorant e B x := by
  apply Finset.sum_nonneg
  intro ρ _
  split_ifs
  · exact Finset.prod_nonneg (fun i _ => hB i (ρ i) (x i))
  · exact le_rfl

theorem constrainedMajorant_average (e : I → C ≃ C) (B : ∀ i,C → A i → ℝ) :
    average (constrainedMajorant e B) =
      ∑ ρ : I → C,if (∏ i,e i (ρ i))=1 then ∏ i,average (B i (ρ i)) else 0 := by
  conv_lhs => unfold average constrainedMajorant
  rw [Finset.sum_comm,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ρ _
  split_ifs with h
  · simpa only [average,h,ite_true] using average_pi_product_real (fun i => B i (ρ i))
  · simp

theorem constrainedMajorant_average_bound (e : I → C ≃ C) (B : ∀ i,C → A i → ℝ)
    (hB : ∀ i χ x,0≤B i χ x) (j : I) (δ : ℝ)
    (hδ : ∀ χ,average (B j χ)≤δ) :
    average (constrainedMajorant e B) ≤
      δ*∏ i : {i : I // i≠j},∑ χ : C,average (B i χ) := by
  rw [constrainedMajorant_average]
  apply Ostmann.FiniteField.constrained_character_sum_bound j e
    (fun i χ => average (B i χ)) _ δ hδ
  intro i χ
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun x _ => hB i χ x))

end
end Ostmann.Tree

end OAI
