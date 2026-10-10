import OAI.NumberTheory.Ostmann.Conclusion.LowLevelBadPairs

namespace OAI

noncomputable section
open scoped BigOperators
namespace Ostmann.Conclusion

def orderedRelativePairEquiv {G : Type*} [Group G] (P : G → Prop) :
    {z : G × G // P (z.1⁻¹*z.2)} ≃ G × {b : G // P b} where
  toFun z := (z.val.1,⟨z.val.1⁻¹*z.val.2,z.property⟩)
  invFun z := ⟨(z.1,z.1*z.2.val),by simpa using z.2.property⟩
  left_inv z := by ext <;> simp
  right_inv z := by ext <;> simp

theorem ordered_relative_pair_card {G : Type*} [Group G] [Finite G] (P : G → Prop) :
    Nat.card {z : G × G // P (z.1⁻¹*z.2)} = Nat.card G*Nat.card {b : G // P b} := by
  rw [Nat.card_congr (orderedRelativePairEquiv P), Nat.card_prod]

theorem sum_bad_good_bound {J : Type*} [Fintype J] (P : J → Prop) [DecidablePred P]
    (F : J → ℝ) {B ε : ℝ} (hε : 0 ≤ ε)
    (hbad : ∀ j, P j → F j ≤ B) (hgood : ∀ j, ¬P j → F j ≤ ε) :
    ∑ j, F j ≤ (Fintype.card {j // P j} : ℝ)*B+(Fintype.card J : ℝ)*ε := by
  have h : ∀ j, F j ≤ (if P j then B else 0)+ε := by
    intro j
    split_ifs with hj
    · exact (hbad j hj).trans (by linarith)
    · simpa using hgood j hj
  calc
    _ ≤ ∑ j, ((if P j then B else 0)+ε) := Finset.sum_le_sum fun j _ => h j
    _ = _ := by simp [Finset.sum_add_distrib,Finset.sum_ite, Fintype.card_subtype]

theorem pair_average_bound {G : Type*} [Group G] [Fintype G]
    (P : G → Prop) [DecidablePred P] (K : G → G → ℝ) {B ε : ℝ} (hε : 0 ≤ ε)
    (hbad : ∀ a b, P (a⁻¹*b) → K a b ≤ B)
    (hgood : ∀ a b, ¬P (a⁻¹*b) → K a b ≤ ε) :
    (∑ a, ∑ b, K a b)/(Fintype.card G : ℝ)^2 ≤
      ((Fintype.card {b : G // P b} : ℝ)/(Fintype.card G : ℝ))*B+ε := by
  classical
  have h := sum_bad_good_bound (fun z : G × G => P (z.1⁻¹*z.2))
    (fun z => K z.1 z.2) hε (fun z => hbad z.1 z.2) (fun z => hgood z.1 z.2)
  have hcard : Fintype.card {z : G × G // P (z.1⁻¹*z.2)} =
      Fintype.card G*Fintype.card {b : G // P b} := by
    simpa only [Nat.card_eq_fintype_card] using ordered_relative_pair_card P
  rw [hcard,Fintype.card_prod] at h
  simp only [Fintype.sum_prod_type,Nat.cast_mul] at h
  have hn : (Fintype.card G : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ ((Fintype.card G : ℝ)*(Fintype.card {b : G // P b} : ℝ)*B+
        ((Fintype.card G : ℝ)*(Fintype.card G : ℝ))*ε)/(Fintype.card G : ℝ)^2 :=
      div_le_div_of_nonneg_right h (sq_nonneg _)
    _ = _ := by field_simp

end Ostmann.Conclusion

end

end OAI
