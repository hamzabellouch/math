import Mathlib
import OAI.Probability.SKBarriers.SpinGlass.Basic

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped InnerProductSpace

theorem unit_conflict_packing {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {d : ℕ} (hd : 0 < d) (u : Fin d → E) (w : E) {a b : ℝ}
    (hb : 0 < b) (ha : 0 ≤ a) (hab : a < b^2/2)
    (hu : ∀ i, ‖u i‖ = 1) (hw : ‖w‖ = 1)
    (hoff : ∀ i j, i ≠ j → ⟪u i,u j⟫_ℝ ≤ a)
    (hconf : ∀ i, b < ⟪u i,w⟫_ℝ) : (d:ℝ) < 2/b^2 := by
  classical
  let U := ∑ i, u i
  have hdR : 0 < (d:ℝ) := by exact_mod_cast hd
  have hsum : (d:ℝ)*b < ⟪U,w⟫_ℝ := by
    dsimp only [U]
    rw [sum_inner]
    have H := Finset.sum_lt_sum_of_nonempty (s := (Finset.univ : Finset (Fin d)))
      (Finset.univ_nonempty_iff.mpr ⟨⟨0,hd⟩⟩) (fun i _ => hconf i)
    simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using H
  have hCS : ⟪U,w⟫_ℝ ≤ ‖U‖ := by simpa only [hw,mul_one] using real_inner_le_norm U w
  have hdiag (i : Fin d) : (∑ j : Fin d, ⟪u i,u j⟫_ℝ) ≤ 1+((d:ℝ)-1)*a := by
    have H := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d)))
      (g := fun j => if i=j then (1:ℝ) else a) (fun j _ => show ⟪u i,u j⟫_ℝ ≤ (if i=j then 1 else a) from by
        by_cases hij : i=j
        · subst j; simp only [ite_true,real_inner_self_eq_norm_sq,hu,one_pow,le_refl]
        · simp only [ite_eq_right hij]; exact hoff i j hij)
    have he : (∑ j : Fin d, if i=j then (1:ℝ) else a) = 1+((d:ℝ)-1)*a := by
      have hh (j : Fin d) : (if i=j then (1:ℝ) else a) = a+(if i=j then 1-a else 0) := by split_ifs <;> ring
      simp_rw [hh]
      simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        Finset.sum_ite_eq,Finset.mem_univ,ite_true]
      ring
    rwa [he] at H
  have hnorm : ‖U‖^2 ≤ (d:ℝ)+(d:ℝ)*((d:ℝ)-1)*a := by
    rw [← real_inner_self_eq_norm_sq]
    dsimp only [U]
    rw [sum_inner]
    simp_rw [inner_sum]
    have H := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) => hdiag i)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at H
    nlinarith [H]
  have hqlt : ((d:ℝ)*b)^2 < ‖U‖^2 := sq_lt_sq₀ (by positivity) (norm_nonneg _) |>.mpr (hsum.trans_le hCS)
  have hdb : (d:ℝ)*b^2 < 1+((d:ℝ)-1)*a := by
    have H : (d:ℝ)*((d:ℝ)*b^2) < (d:ℝ)*(1+((d:ℝ)-1)*a) := by nlinarith [hqlt,hnorm]
    exact (mul_lt_mul_iff_right₀ hdR).mp H
  have hdiff : b^2-a > b^2/2 := by linarith
  have H : (d:ℝ)*(b^2-a) < 1-a := by nlinarith [hdb]
  have H' : (d:ℝ)*(b^2/2) < 1 := by nlinarith [mul_lt_mul_of_pos_left hdiff hdR,H]
  apply (lt_div_iff₀ (sq_pos_of_pos hb)).mpr
  nlinarith

def configVector {n : ℕ} (x : Config n) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => spin (x i)/Real.sqrt (n:ℝ))

theorem configVector_inner {n : ℕ} (hn : 0 < n) (x y : Config n) :
    ⟪configVector x,configVector y⟫_ℝ = overlap x y := by
  rw [configVector,configVector,EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct,Pi.star_apply,star_trivial]
  have hn0 : 0 ≤ (n:ℝ) := by positivity
  have he (i : Fin n) : spin (y i)/Real.sqrt (n:ℝ)*(spin (x i)/Real.sqrt (n:ℝ)) =
      (spin (x i)*spin (y i))/(n:ℝ) := by
    rw [div_mul_div_comm,Real.mul_self_sqrt hn0,mul_comm (spin (y i))]
  simp_rw [he]
  rw [← Finset.sum_div]
  rfl

theorem configVector_norm {n : ℕ} (hn : 0 < n) (x : Config n) : ‖configVector x‖ = 1 := by
  have H := configVector_inner hn x x
  rw [real_inner_self_eq_norm_sq,overlap_self hn] at H
  nlinarith [norm_nonneg (configVector x)]

theorem config_conflict_packing {n d : ℕ} (hn : 0 < n) (hd : 0 < d)
    (x : Fin d → Config n) (w : Config n) {a b : ℝ}
    (hb : 0 < b) (ha : 0 ≤ a) (hab : a < b^2/2)
    (hoff : ∀ i j, i ≠ j → |overlap (x i) (x j)| ≤ a)
    (hconf : ∀ i, b < |overlap (x i) w|) : (d:ℝ) < 2/b^2 := by
  let u : Fin d → EuclideanSpace ℝ (Fin n) := fun i =>
    if 0 ≤ overlap (x i) w then configVector (x i) else -configVector (x i)
  apply unit_conflict_packing hd u (configVector w) hb ha hab
  · intro i
    dsimp only [u]
    split_ifs <;> simp only [norm_neg,configVector_norm hn]
  · exact configVector_norm hn w
  · intro i j hij
    have H := hoff i j hij
    have HP := (le_abs_self (overlap (x i) (x j))).trans H
    have HN := (neg_le_abs (overlap (x i) (x j))).trans H
    dsimp only [u]
    split_ifs <;> simp only [inner_neg_left,inner_neg_right,configVector_inner hn,neg_neg] <;> assumption
  · intro i
    dsimp only [u]
    split_ifs with hs
    · simpa only [configVector_inner hn,abs_of_nonneg hs] using hconf i
    · simpa only [inner_neg_left,configVector_inner hn,abs_of_neg (lt_of_not_ge hs)] using hconf i

end SK.Analytic

end
end

end

end OAI
