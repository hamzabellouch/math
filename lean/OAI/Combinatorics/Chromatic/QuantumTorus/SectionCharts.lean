import Mathlib
import OAI.Combinatorics.Chromatic.Walls.ChartRefinement
import OAI.Combinatorics.Chromatic.Walls.TranslatedCompletion
import OAI.Combinatorics.Chromatic.QuantumTorus.SectionTrace

namespace OAI

section
namespace ElementaryPositivity.QuantumTorus
open PowerSeries PowerSeriesSplit PowerSeriesAdjoint
noncomputable section
variable {M I : Type*} [AddCommGroup M] [Fintype I]
variable (v : (LaurentSeries ℚ)ˣ) (Ω : M →+ M →+ ℤ) (C : (I → ℤ) →+ M)
lemma negative_sign_congr_through (h k : M →+ ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hs : ∀n,0<n → n≤N → ∀m,HasRootDegree C n m →
      (0<h m → 0<k m) ∧ (h m=0 → k m=0) ∧ (h m<0 → k m<0)) :
    ∀n≤N,coeff n (chartNegative v Ω C h F).val=coeff n (chartNegative v Ω C k F).val := by
  have H:=chart_three_support v Ω C h F
  have HU:=chart_three_truncated_unique v Ω C k F
    (chartPositive v Ω C h F).val (chartZero v Ω C h F).val (chartNegative v Ω C h F).val N
    (chartPositive v Ω C h F).property.1 (chartZero v Ω C h F).property.1
    (chartNegative v Ω C h F).property.1 (chart_three_factorization v Ω C h F)
    (fun n hn m hm=>(hs (n+1) (by omega) hn m (chart_root_of_ne v Ω C _ _ _ hm)).1 (H.1 n m hm))
    (fun n hn m hm=>(hs (n+1) (by omega) hn m (chart_root_of_ne v Ω C _ _ _ hm)).2.1 (H.2.1 n m hm))
    (fun n hn m hm=>(hs (n+1) (by omega) hn m (chart_root_of_ne v Ω C _ _ _ hm)).2.2 (H.2.2 n m hm))
  exact fun n hn=>(HU n hn).2.2
lemma section_sign_congr_through (h k : M →+ ℝ) (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hs : ∀n,0<n → n≤N → ∀m,HasRootDegree C n m →
      (0<h m → 0<k m) ∧ (h m=0 → k m=0) ∧ (h m<0 → k m<0)) :
    ∀n≤N,coeff n (sectionValue v Ω C F h X)=coeff n (sectionValue v Ω C F k X) := by
  intro n hn
  exact adjoint_coeff_congr _ _ _ _ n
    (fun j hj=>negative_sign_congr_through v Ω C h k F N hs j (hj.trans hn)) (fun _ _=>rfl)
lemma section_refinement_through (h k H : M →+ ℝ) (F : CompletedPositive v Ω C)
    (X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hs : ∀n≤N,∀m,HasRootDegree C n m → LexSigns h k H m) :
    ∀n≤N,coeff n (sectionValue v Ω C F H X)=
      coeff n (adjoint (chartNegative v Ω C k (chartZero v Ω C h F)).val
        (sectionValue v Ω C F h X)) := by
  intro n hn
  unfold sectionValue
  rw [←adjoint_mul _ _ _ (chartNegative v Ω C k (chartZero v Ω C h F)).property.1
    (chartNegative v Ω C h F).property.1]
  exact adjoint_coeff_congr _ _ _ _ n
    (fun j hj=>chart_negative_refinement v Ω C h k H F N hs j (hj.trans hn)) (fun _ _=>rfl)
lemma section_incoming_perturbation (hΩ : ∀m,Ω m m=0) (r : M) (k H : M →+ ℝ)
    (F : CompletedPositive v Ω C) (X : PowerSeries (Torus v Ω)) (N : ℕ)
    (hs : ∀n≤N,∀m,HasRootDegree C n m → LexSigns (incomingCovector Ω r) k H m) :
    (coeff N (sectionValue v Ω C F H X)) r=
      (coeff N (sectionValue v Ω C F (incomingCovector Ω r) X)) r := by
  rw [section_refinement_through v Ω C _ _ _ F X N hs N le_rfl]
  apply adjoint_coefficient_trace v Ω hΩ r _ _ N
    (chartNegative v Ω C k (chartZero v Ω C (incomingCovector Ω r) F)).property.1
  have hker:=chartThree_supported v Ω C k (incomingCovector Ω r).ker.toAddSubmonoid
    (chartZero v Ω C (incomingCovector Ω r) F) (chartZero_supported_kernel v Ω C _ F)
  intro n hn m hm
  apply hker.2.2 n m
  intro hh
  apply hm
  change (Ω m r:ℝ)=0 at hh
  exact_mod_cast hh
lemma chartNegative_of_positive_through (h : M →+ ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hpos : ∀n,n+1≤N → ∀m,coeff (n+1) F.val m≠0 → 0<h m) :
    ∀n≤N,coeff n (chartNegative v Ω C h F).val=coeff n 1 := by
  have H:=chart_three_truncated_unique v Ω C h F F.val 1 1 N F.property.1 (by simp)
    (by simp) (by simp) hpos (by intro n hn m hm; simp at hm) (by intro n hn m hm; simp at hm)
  exact fun n hn=>(H n hn).2.2.symm
lemma chartNegative_of_negative_through (h : M →+ ℝ) (F : CompletedPositive v Ω C) (N : ℕ)
    (hneg : ∀n,n+1≤N → ∀m,coeff (n+1) F.val m≠0 → h m<0) :
    ∀n≤N,coeff n (chartNegative v Ω C h F).val=coeff n F.val := by
  have H:=chart_three_truncated_unique v Ω C h F 1 1 F.val N (by simp) (by simp)
    F.property.1 (by simp) (by intro n hn m hm; simp at hm) (by intro n hn m hm; simp at hm) hneg
  exact fun n hn=>(H n hn).2.2.symm
end
end ElementaryPositivity.QuantumTorus

end

end OAI
