import OAI.MeasureTheory.Falconer.Estimates.ScalarWeakRefinement

namespace OAI

/-! Dense-graph refinement without equal cardinalities for the coordinate
sets. The explicit cost is the square of their cardinality ratio. -/
namespace Falconer
open scoped Pointwise
attribute [local instance] Classical.propDecidable

 theorem scalar_unbalanced_projection_bound {S N P Q D V : ℝ}
    (hS : 0 < S) (hN : 0 < N) (hP : 0 < P) (hD : 0 ≤ D)
    (hcard : D ≤ S*N) (hNP : N ≤ Q*P)
    (hbound : V*((S⁻¹)^8*N^2*P^2) ≤ 67108864*D^5) :
    V ≤ 67108864*S^13*Q^2*N := by
  have hNP2 : N^2 ≤ Q^2*P^2 := by
    have hh := pow_le_pow_left₀ hN.le hNP 2
    nlinarith
  have hcore : V*(S⁻¹)^8 ≤ 67108864*S^5*N*Q^2 := by
    apply (mul_le_mul_iff_left₀ (mul_pos (sq_pos_of_pos hN) (sq_pos_of_pos hP))).1
    calc
      _ = V*((S⁻¹)^8*N^2*P^2) := by ring
      _ ≤ 67108864*D^5 := hbound
      _ ≤ 67108864*(S*N)^5 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD hcard 5) (by norm_num)
      _ = (67108864*S^5*N^3)*N^2 := by ring
      _ ≤ (67108864*S^5*N^3)*(Q^2*P^2) := mul_le_mul_of_nonneg_left hNP2 (by positivity)
      _ = _ := by ring
  calc
    _ ≤ (67108864*S^5*N*Q^2)/(S⁻¹)^8 :=
      (le_div_iff₀ (by positivity : 0 < (S⁻¹)^8)).2 hcore
    _ = _ := by field_simp

 theorem scalar_dilated_unbalanced_refinement {δ S c Q : ℝ}
    (hδ : 0 < δ) (hS : 1 ≤ S) (hc : c ≠ 0)
    (A B : Finset ℝ) (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : (A.card:ℝ) ≤ Q*(B.card:ℝ))
    (hAsep : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → δ ≤ |x-y|)
    (hBsep : ∀ x ∈ B.image (fun y => c*y), ∀ y ∈ B.image (fun y => c*y), x ≠ y → δ ≤ |x-y|)
    (e : ℝ → ℝ → Prop) (D : Finset ℤ)
    (hdense : S⁻¹*(A.card:ℝ)*(B.card:ℝ) ≤ ∑ a ∈ A, ((B.filter fun b => e a b).card:ℝ))
    (hlabels : ∀ a ∈ A, ∀ b ∈ B, e a b → ⌊(a+c*b)/δ⌋ ∈ D)
    (hcard : (D.card:ℝ) ≤ S*(A.card:ℝ)) :
    ∃ X ⊆ A, ∃ Y ⊆ B,
      ((S⁻¹)^2/64)*(A.card:ℝ) ≤ (X.card:ℝ) ∧
      ((S⁻¹)^2/64)*(B.card:ℝ) ≤ (Y.card:ℝ) ∧
      ((scalarCells δ (X+Y.image (fun y => c*y))).card:ℝ) ≤ 67108864*S^13*Q^2*(A.card:ℝ) ∧
      ∀ x ∈ X, ((S⁻¹)^2/64)*(Y.card:ℝ) ≤ ((Y.filter fun y => e x y).card:ℝ) := by
  have hSpos : 0 < S := zero_lt_one.trans_le hS
  obtain ⟨X,hXA,Y,hYB,hX,hY,hproj,hdegree⟩ := scalar_dilated_refinement
    hδ (inv_pos.mpr hSpos) hc A B hA hB hAsep hBsep e D hdense hlabels
  have hN : 0 < (A.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hA)
  have hP : 0 < (B.card:ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hB)
  have hproj' := scalar_unbalanced_projection_bound hSpos hN hP (Nat.cast_nonneg _)
    hcard hAB hproj
  have hρ1 : S⁻¹ ≤ 1 := (inv_le_one₀ hSpos).2 hS
  have hρ0 : 0 ≤ S⁻¹ := (inv_pos.mpr hSpos).le
  have hρ2 : (S⁻¹)^2 ≤ S⁻¹ := by nlinarith
  have hh := mul_le_mul_of_nonneg_right hρ2 (Nat.cast_nonneg (α := ℝ) B.card)
  refine ⟨X,hXA,Y,hYB,?_,?_,hproj',?_⟩
  · nlinarith
  · nlinarith
  · intro x hx
    have hd := hdegree x hx
    nlinarith

end Falconer

end OAI
