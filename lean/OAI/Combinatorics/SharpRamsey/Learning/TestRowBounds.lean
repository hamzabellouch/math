import Mathlib
import OAI.Combinatorics.SharpRamsey.Geometry.TestRowPencils

namespace OAI

section
namespace SharpLogRamsey.PreparedRow
open Finset MeasureTheory
open scoped BigOperators Classical NNReal
noncomputable section
variable {A H : Type*} [Fintype A] [Fintype H]

omit [Fintype A] [Fintype H] in
lemma degree_eq_card (inc : H→A→Prop) (Z : Finset H) (x : A) :
    PencilContrast.degree (fun x H => inc H x) Z x=(Z.filter (fun H => inc H x)).card := by
  simp only [PencilContrast.degree,card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

omit [Fintype A] [Fintype H] in
lemma support_empty_large (S : Finset A) (Z : Finset H) (inc : H→A→Prop)
    (q a : ℝ) (hq : 0<q) (hS : S.Nonempty) (hZ : Z.Nonempty)
    (hb : (∑ H∈Z,(q/(S.card:ℝ))*((S.filter (inc H)).card:ℝ))≤a*(Z.card:ℝ)) :
    ((S.filter (fun x => (Z.card:ℝ)/(10*q)<((Z.filter (fun H => inc H x)).card:ℝ))).card:ℝ)≤
      (10*a)*(S.card:ℝ) := by
  have hSc : (0:ℝ)<S.card := by exact_mod_cast card_pos.mpr hS
  have hZc : (0:ℝ)<Z.card := by exact_mod_cast card_pos.mpr hZ
  have hh := PencilContrast.support_large_degree (fun x H => inc H x) S Z q S.card Z.card a
    (1/10) hq hSc hZc (by norm_num) (by
      convert hb using 1
      simp only [card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero])
  have hs : S.filter (fun x => (Z.card:ℝ)/(10*q)<((Z.filter (fun H => inc H x)).card:ℝ))⊆
      S.filter (fun x => (1/10:ℝ)*(Z.card:ℝ)/q≤PencilContrast.degree (fun x H => inc H x) Z x) := by
    intro x hx
    refine mem_filter.mpr ⟨(mem_filter.mp hx).1,?_⟩
    rw [degree_eq_card]
    convert (mem_filter.mp hx).2.le using 1
    first | with_unfolding_all rfl | ring
  have hc : ((S.filter (fun x => (Z.card:ℝ)/(10*q)<((Z.filter (fun H => inc H x)).card:ℝ))).card:ℝ)≤
      (S.filter (fun x => (1/10:ℝ)*(Z.card:ℝ)/q≤PencilContrast.degree (fun x H => inc H x) Z x)).card := by
    exact_mod_cast card_le_card hs
  convert hc.trans hh using 1
  first | with_unfolding_all rfl | ring

lemma alpha_bounds (L f : ℝ) (R : ℕ) (hL : 0≤L) (hf : f≤1/25)
    (hR : (R:ℝ)*Real.exp (-(24/25:ℝ)*L)≤1/10) :
    0≤Real.exp (-L*(1-f)) ∧ Real.exp (-L*(1-f))≤1 ∧
      9/10≤(1-Real.exp (-L*(1-f)))^R ∧ (1-Real.exp (-L*(1-f)))^R≤1 := by
  let b := Real.exp (-L*(1-f))
  have hb : 0≤b := (Real.exp_pos _).le
  have hb1 : b≤1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hbe : b≤Real.exp (-(24/25:ℝ)*L) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hbR : (R:ℝ)*b≤1/10 :=
    (mul_le_mul_of_nonneg_left hbe (Nat.cast_nonneg R)).trans hR
  have hber : 1-(R:ℝ)*b≤(1-b)^R := by
    have hh := one_add_mul_sub_le_pow (show (-1:ℝ)≤1-b by linarith) R
    convert hh using 1
    first | with_unfolding_all rfl | ring
  exact ⟨hb,hb1,by linarith,pow_le_one₀ (by linarith) (by linarith)⟩

end
end SharpLogRamsey.PreparedRow

end

end OAI
