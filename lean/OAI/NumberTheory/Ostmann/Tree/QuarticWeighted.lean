import OAI.NumberTheory.Ostmann.Tree.QuarticCollision

namespace OAI

namespace Ostmann.FiniteField
noncomputable section
open scoped BigOperators
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

abbrev Quartet (F : Type*) := (F × F) × (F × F)
def quartetWeight (w : F → ℝ) (b : Quartet F) : ℝ :=
  w b.1.1*w b.1.2*w b.2.1*w b.2.2

abbrev quartetDiagonal (b : Quartet F) : Prop :=
  (b.1.1=b.2.1 ∧ b.1.2=b.2.2) ∨ (b.1.1=b.2.2 ∧ b.1.2=b.2.1)

abbrev quartetCollision (a : F) (b : Quartet F) : Prop :=
  (a-b.1.1)*(a-b.1.2)=(a-b.2.1)*(a-b.2.2)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem quartetWeight_nonneg (w : F → ℝ) (hw : ∀ x, 0 ≤ w x) (b : Quartet F) :
    0 ≤ quartetWeight w b := by
  exact mul_nonneg (mul_nonneg (mul_nonneg (hw _) (hw _)) (hw _)) (hw _)

omit [Field F] [DecidableEq F] in
theorem quartetWeight_sum (w : F → ℝ) :
    (∑ b : Quartet F, quartetWeight w b) = (∑ x, w x)^4 := by
  simp only [quartetWeight,Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, ← Finset.sum_mul]
  ring

omit [Field F] in
theorem quartetWeight_diagonal_sum (w : F → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ b : Quartet F, if quartetDiagonal b then quartetWeight w b else 0) ≤
      2*(∑ x, w x^2)^2 := by
  classical
  have hpoint (b : Quartet F) :
      (if quartetDiagonal b then quartetWeight w b else 0) ≤
        (if b.1=b.2 then quartetWeight w b else 0)+
        (if b.1=b.2.swap then quartetWeight w b else 0) := by
    have h1 : b.1=b.2 ↔ b.1.1=b.2.1 ∧ b.1.2=b.2.2 := Prod.ext_iff
    have h2 : b.1=b.2.swap ↔ b.1.1=b.2.2 ∧ b.1.2=b.2.1 := Prod.ext_iff
    have hW := quartetWeight_nonneg w hw b
    simp only [h1,h2,quartetDiagonal]
    split_ifs <;> simp_all
  have hfirst : (∑ b : Quartet F, if b.1=b.2 then quartetWeight w b else 0) =
      (∑ x, w x^2)^2 := by
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true, quartetWeight]
    rw [Fintype.sum_prod_type]
    have he (x y : F) : w x*w y*w x*w y = w x^2*w y^2 := by ring
    simp_rw [he]
    simp only [← Finset.mul_sum,← Finset.sum_mul,pow_two]
  have hsecond : (∑ b : Quartet F, if b.1=b.2.swap then quartetWeight w b else 0) =
      (∑ x, w x^2)^2 := by
    rw [Fintype.sum_prod_type,Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true, quartetWeight, Prod.fst_swap,Prod.snd_swap]
    rw [Fintype.sum_prod_type]
    have he (x y : F) : w y*w x*w x*w y = w x^2*w y^2 := by ring
    simp_rw [he]
    simp only [← Finset.mul_sum,← Finset.sum_mul,pow_two]
  calc
    _ ≤ ∑ b : Quartet F, ((if b.1=b.2 then quartetWeight w b else 0)+
        (if b.1=b.2.swap then quartetWeight w b else 0)) := Finset.sum_le_sum (fun b _ => hpoint b)
    _ = 2*(∑ x, w x^2)^2 := by rw [Finset.sum_add_distrib,hfirst,hsecond]; ring

theorem quartetCollision_weighted_bound (w : F → ℝ) (hw : ∀ x, 0 ≤ w x) :
    (∑ a : F, ∑ b : Quartet F, if quartetCollision a b then quartetWeight w b else 0) ≤
      2*(Fintype.card F:ℝ)*(∑ x, w x^2)^2+(∑ x, w x)^4 := by
  classical
  have hpoint (b : Quartet F) :
      (∑ a : F, if quartetCollision a b then quartetWeight w b else 0) ≤
        (Fintype.card F:ℝ)*(if quartetDiagonal b then quartetWeight w b else 0)+quartetWeight w b := by
    have hw0 := quartetWeight_nonneg w hw b
    rw [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul]
    by_cases hd : quartetDiagonal b
    · simp only [hd,ite_true]
      have hc : (Finset.univ.filter (fun a : F => quartetCollision a b)).card ≤ Fintype.card F :=
        (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_univ)
      have hcR : ((Finset.univ.filter (fun a : F => quartetCollision a b)).card:ℝ) ≤ Fintype.card F := by exact_mod_cast hc
      have hh := mul_le_mul_of_nonneg_right hcR hw0
      linarith
    · simp only [hd,ite_false,mul_zero,zero_add]
      have hc := quartet_collision_card_le_one b.1.1 b.1.2 b.2.1 b.2.2 hd
      have hcR : ((Finset.univ.filter (fun a : F => quartetCollision a b)).card:ℝ) ≤ 1 := by exact_mod_cast hc
      exact (mul_le_mul_of_nonneg_right hcR hw0).trans_eq (one_mul _)
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ b : Quartet F, ((Fintype.card F:ℝ)*(if quartetDiagonal b then quartetWeight w b else 0)+quartetWeight w b) :=
      Finset.sum_le_sum (fun b _ => hpoint b)
    _ = (Fintype.card F:ℝ)*(∑ b : Quartet F, if quartetDiagonal b then quartetWeight w b else 0)+(∑ x,w x)^4 := by
      rw [Finset.sum_add_distrib,← Finset.mul_sum,quartetWeight_sum]
    _ ≤ (Fintype.card F:ℝ)*(2*(∑ x,w x^2)^2)+(∑ x,w x)^4 := by
      exact add_le_add (mul_le_mul_of_nonneg_left (quartetWeight_diagonal_sum w hw) (by positivity)) le_rfl
    _ = 2*(Fintype.card F:ℝ)*(∑ x, w x^2)^2+(∑ x, w x)^4 := by ring

end
end Ostmann.FiniteField

end OAI
