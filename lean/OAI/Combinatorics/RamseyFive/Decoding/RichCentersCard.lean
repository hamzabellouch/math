import Mathlib
import OAI.Combinatorics.RamseyFive.Decoding.RichCenters
import OAI.Combinatorics.RamseyFive.Geometry.CardIndexed

namespace OAI

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
open scoped BigOperators
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal
noncomputable section
namespace SharpRamseyFive.GlobalRadial
open Module ProjectiveTraining GreedyTraining ProjectiveIncidence
open scoped BigOperators LinearAlgebra.Projectivization Classical
variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Finite K]

lemma richCenters_card_le (X : Finset (ℙ K V)) (O : ℙ K V → Finset (ℙ K V))
    (δ a : ℝ) (A : Submodule K V) (hA : finrank K A = 2) :
    (richCenters X O δ a A).card ≤ Nat.card K+1 := by
  let : Finite V := Module.finite_of_finite K
  let C := richCenters X O δ a A
  let f (x : C) : {y : ℙ K V // y.submodule ≤ A} :=
    ⟨x.val,(mem_flatPoints A x.val).mp (Finset.mem_filter.mp x.property).1⟩
  have hi : Function.Injective f := fun _ _ he => Subtype.ext (show _ = _ from congrArg (fun z : {y : ℙ K V // y.submodule ≤ A} => z.val) he)
  have hc := Nat.card_le_card_of_injective f hi
  rw [Nat.card_eq_fintype_card,Fintype.card_coe,card_subspacePoints,hA] at hc
  simpa only [Finset.sum_range_succ,Finset.range_zero,Finset.sum_empty,pow_zero,pow_one,
    zero_add,add_comm] using hc

lemma centers_empty_of_not_rich (X : Finset (ℙ K V))
    (O : ℙ K V → Finset (ℙ K V)) {δ a : ℝ} (hδ : 0 ≤ δ)
    (A : Submodule K V) (ha : ¬a ≤ δ*(X.filter fun y => y.submodule ≤ A).card) :
    richCenters X O δ a A = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro x hx
  apply ha
  apply (Finset.mem_filter.mp hx).2.trans
  apply mul_le_mul_of_nonneg_left _ hδ
  exact_mod_cast Finset.card_le_card (Finset.filter_subset_filter _ Finset.sdiff_subset)

theorem residual_rich_centers {I : Type*} [Fintype I] {q : ℕ} [CharP K q]
    (hq : 2 < q) (hcard : Nat.card K = q)
    (hI : Fintype.card I = 4 ∨ Fintype.card I = 5)
    (σ g n' a : ℝ) (hσq : Real.exp σ = q)
    (hσ : 1000 ≤ σ) (hg : 100000000 ≤ g) (hghi : g ≤ 2*σ)
    (hn' : Real.exp (3*σ/2+g)/4 ≤ n') (ha : Real.exp (-g/20) ≤ a) (ha2 : a ≤ 2)
    (X : Finset (ℙ K (I → K))) (hX : (X.card:ℝ) ≤ Real.exp (3*σ/2+g))
    (L : Finset (Submodule K (I → K))) (hL : ∀ A ∈ L, finrank K A = 2)
    (O : ℙ K (I → K) → Finset (ℙ K (I → K)))
    (hcap : ∀ U : Submodule K (I → K), finrank K U = 3 →
      ((X.filter fun y => y.submodule ≤ U).card:ℝ) ≤
        (Real.exp (3*σ/2+g)) ^ (4/3:ℝ) / Real.exp σ * Real.exp (-g/5)) :
    (∑ A ∈ L, ((richCenters X O ((q:ℝ)/n') a A).card:ℝ))*a^2 ≤ 333024*(q:ℝ)^2 := by
  have hq0 : (0:ℝ)<q := by exact_mod_cast lt_trans (by decide : 0<2) hq
  have hn0 : 0<n' := (by positivity : 0<Real.exp (3*σ/2+g)/4).trans_le hn'
  have ha0 : 0<a := (Real.exp_pos _).trans_le ha
  let F := L.filter fun A => n'*a/(q:ℝ) ≤ (X.filter fun y => y.submodule ≤ A).card
  have hr := ProjectiveRichLines.source_rich_lines hq hI σ g n' a hσq hσ hg hghi
    hn' ha X hX F (fun A hA => hL A (Finset.mem_filter.mp hA).1)
    (fun A hA => by simpa only [hσq] using (Finset.mem_filter.mp hA).2) hcap
  rw [hσq] at hr
  have hsum : (∑ A ∈ L, ((richCenters X O ((q:ℝ)/n') a A).card:ℝ)) ≤
      (F.card:ℝ)*((q:ℝ)+1) := by
    have he : (∑ A ∈ L, ((richCenters X O ((q:ℝ)/n') a A).card:ℝ)) =
        ∑ A ∈ F, ((richCenters X O ((q:ℝ)/n') a A).card:ℝ) := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro A hA hn
      have hnrich : ¬n'*a/(q:ℝ) ≤ (X.filter fun y => y.submodule ≤ A).card := by
        intro hh
        exact hn (Finset.mem_filter.mpr ⟨hA,hh⟩)
      rw [centers_empty_of_not_rich X O (by positivity) A ?_,Finset.card_empty,Nat.cast_zero]
      intro hh
      apply hnrich
      apply (div_le_iff₀ hq0).mpr
      have hh' := (le_div_iff₀ hn0).mp (show a ≤
          (q:ℝ)*(X.filter fun y => y.submodule ≤ A).card/n' by simpa only [div_mul_eq_mul_div] using hh)
      nlinarith
    rw [he]
    calc
      _ ≤ ∑ _A ∈ F, ((q:ℝ)+1) := by
        apply Finset.sum_le_sum
        intro A hA
        have hh := richCenters_card_le X O ((q:ℝ)/n') a A (hL A (Finset.mem_filter.mp hA).1)
        rw [hcard] at hh
        exact_mod_cast hh
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have hr' : (F.card:ℝ)*n'*a ≤ 20814*Real.exp (3*σ/2+g)*(q:ℝ) := by
    have hh := (div_le_iff₀ hq0).mp (show (F.card:ℝ)*n'*a/(q:ℝ) ≤ _ by
      simpa only [mul_div_assoc,mul_assoc] using hr)
    simpa only [mul_div_assoc] using hh
  have hn : Real.exp (3*σ/2+g) ≤ 4*n' := by linarith
  have hr'' : (F.card:ℝ)*a ≤ 83256*(q:ℝ) := by
    have hh := hr'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn (by norm_num)) hq0.le)
    nlinarith
  have hq1 : (q:ℝ)+1 ≤ 2*(q:ℝ) := by exact_mod_cast (by omega : q+1≤2*q)
  calc
    _ ≤ ((F.card:ℝ)*((q:ℝ)+1))*a^2 := mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
    _ = ((F.card:ℝ)*a)*(((q:ℝ)+1)*a) := by ring
    _ ≤ (83256*(q:ℝ))*((2*(q:ℝ))*2) := mul_le_mul hr''
      (mul_le_mul hq1 ha2 ha0.le (by positivity)) (by positivity) (by positivity)
    _ = _ := by ring

end SharpRamseyFive.GlobalRadial

end

end OAI
