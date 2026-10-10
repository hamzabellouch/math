import Mathlib
import OAI.Probability.SphericalField.Entropy.StationaryExistence

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace SphericalPerceptron

lemma Trial.ext_fun {m n : Trial} (h : ∀ t, m t=n t) : m=n := by
  cases m
  cases n
  congr 1
  exact funext h

lemma weightedStepTrial_coupling_fst {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w : I → ℝ) (q : I → Time)
    (hc : ∀ a, 0 ≤ c a) (hc1 : ∑ a, c a=1)
    (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (hrow : ∀ i, ∑ j, c (i,j)=w i) :
    weightedStepTrial c (fun a => q a.1) hc hc1=weightedStepTrial w q hw hw1 := by
  apply Trial.ext_fun
  intro t
  change (∑ a : I×J, if q a.1 ≤ t then c a else 0)=∑ i, if q i ≤ t then w i else 0
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : q i ≤ t <;> simp [hi,hrow]

lemma weightedStepTrial_coupling_snd {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (v : J → ℝ) (p : J → Time)
    (hc : ∀ a, 0 ≤ c a) (hc1 : ∑ a, c a=1)
    (hv : ∀ i, 0 ≤ v i) (hv1 : ∑ i, v i=1)
    (hcol : ∀ j, ∑ i, c (i,j)=v j) :
    weightedStepTrial c (fun a => p a.2) hc hc1=weightedStepTrial v p hv hv1 := by
  apply Trial.ext_fun
  intro t
  change (∑ a : I×J, if p a.2 ≤ t then c a else 0)=∑ j, if p j ≤ t then v j else 0
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : p j ≤ t <;> simp [hj,hcol]

lemma coupling_sum_fst {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w f : I → ℝ) (hrow : ∀ i, ∑ j, c (i,j)=w i) :
    (∑ a, c a*f a.1)=∑ i, w i*f i := by
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.sum_mul,hrow]

lemma coupling_sum_snd {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (v f : J → ℝ) (hcol : ∀ j, ∑ i, c (i,j)=v j) :
    (∑ a, c a*f a.2)=∑ j, v j*f j := by
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp_rw [← Finset.sum_mul,hcol]

lemma weightedStepTail_coupling_fst {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w q : I → ℝ) (hrow : ∀ i, ∑ j, c (i,j)=w i) :
    weightedStepTail c (fun a => q a.1)=weightedStepTail w q := by
  funext t
  exact coupling_sum_fst c w (fun i => 1-max (q i) t) hrow

lemma weightedStepA_coupling_fst {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w q : I → ℝ) (hrow : ∀ i, ∑ j, c (i,j)=w i) :
    weightedStepA c (fun a => q a.1)=weightedStepA w q := by
  unfold weightedStepA
  rw [weightedStepTail_coupling_fst c w q hrow]

lemma entropy_coupled_stationary_comparison {I J : Type*} [Fintype I] [Fintype J]
    (c : I×J → ℝ) (w h : I → ℝ) (v g : J → ℝ) (q : I → Time) (p : J → Time)
    (hc : ∀ a, 0 ≤ c a) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (hv : ∀ j, 0 ≤ v j) (hv1 : ∑ j, v j=1)
    (hrow : ∀ i, ∑ j, c (i,j)=w i) (hcol : ∀ j, ∑ i, c (i,j)=v j)
    (B : ℝ) (hB0 : 0 ≤ B) (hB1 : B < 1)
    (hq : ∀ i, (q i:ℝ) ≤ B) (hp : ∀ j, (p j:ℝ) ≤ B)
    (hstat : ∀ i, 2*h i=weightedStepA w (fun i => (q i:ℝ)) (q i)) :
    (entropy (weightedStepTrial w q hw hw1)).toReal-∑ i, w i*h i*(q i:ℝ) ≤
      (entropy (weightedStepTrial v p hv hv1)).toReal-∑ j, v j*g j*(p j:ℝ)+
        ∑ a, c a*|h a.1-g a.2| := by
  have hc1 : ∑ a, c a=1 := by rw [Fintype.sum_prod_type]; simp_rw [hrow]; exact hw1
  have hs := entropy_weightedStep_support c (fun a => p a.2) (fun a => q a.1)
    hc hc1 B hB0 hB1 (fun a => hp a.2) (fun a => hq a.1)
  rw [weightedStepTrial_coupling_fst c w q hc hc1 hw hw1 hrow,
    weightedStepTrial_coupling_snd c v p hc hc1 hv hv1 hcol,
    weightedStepA_coupling_fst c w (fun i => (q i:ℝ)) hrow] at hs
  have he : (∑ a, c a*((p a.2:ℝ)-(q a.1:ℝ))*weightedStepA w (fun i => (q i:ℝ)) (q a.1))/2 =
      (∑ a, c a*h a.1*(p a.2:ℝ))-(∑ i, w i*h i*(q i:ℝ)) := by
    simp only [mul_assoc]
    rw [← coupling_sum_fst c w (fun i => h i*(q i:ℝ)) hrow]
    simp only [← mul_assoc]
    rw [Finset.sum_div,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _
    rw [← hstat a.1]
    ring
  rw [he] at hs
  have hb : (∑ j, v j*g j*(p j:ℝ))-(∑ a, c a*h a.1*(p a.2:ℝ)) ≤
      ∑ a, c a*|h a.1-g a.2| := by
    simp only [mul_assoc]
    rw [← coupling_sum_snd c v (fun j => g j*(p j:ℝ)) hcol]
    simp only [← mul_assoc]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro a _
    have h₁ : (g a.2-h a.1)*(p a.2:ℝ) ≤ |h a.1-g a.2| := calc
      _ ≤ |g a.2-h a.1| *(p a.2:ℝ) := mul_le_mul_of_nonneg_right (le_abs_self _) (p a.2).2.1
      _ ≤ |g a.2-h a.1| *1 := mul_le_mul_of_nonneg_left (p a.2).2.2 (abs_nonneg _)
      _ = _ := by rw [mul_one,abs_sub_comm]
    have H := mul_le_mul_of_nonneg_left h₁ (hc a)
    nlinarith [H]
  linarith

lemma finiteSphericalDual_eq_stationary {k : ℕ} (w h : Fin (k+1) → ℝ)
    (q : Fin (k+1) → Time) (hw : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i=1)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ) < 1)
    (hs : ∀ i, 2*h i=weightedStepA w (fun j => (q j:ℝ)) (q i)) :
    sInf (finiteSphericalDualValues w h hw hw1)=finiteSphericalDualObjective w h hw hw1 q := by
  apply IsLeast.csInf_eq
  refine ⟨⟨q,⟨hq,hq1⟩,rfl⟩,?_⟩
  rintro a ⟨p,⟨hp,hp1⟩,rfl⟩
  exact stationary_finite_entropy_minimizes w h q p hw hw1 hq hp hq1 hp1 hs

theorem finiteSphericalDual_abs_sub_le {k : ℕ} (w h g : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1)
    (hh : Monotone h) (hh0 : 0 ≤ h 0) (hg : Monotone g) (hg0 : 0 ≤ g 0) :
    |sInf (finiteSphericalDualValues w h (fun i => (hw i).le) hw1)-
      sInf (finiteSphericalDualValues w g (fun i => (hw i).le) hw1)| ≤
        ∑ i, w i*|h i-g i| := by
  classical
  obtain ⟨q,hq,hq1,hsq⟩ := exists_finite_stationary_quantile w h hw hw1 hh hh0
  obtain ⟨p,hp,hp1,hsp⟩ := exists_finite_stationary_quantile w g hw hw1 hg hg0
  rw [finiteSphericalDual_eq_stationary w h q (fun i => (hw i).le) hw1 hq hq1 hsq,
    finiteSphericalDual_eq_stationary w g p (fun i => (hw i).le) hw1 hp hp1 hsp]
  let c : Fin (k+1)×Fin (k+1) → ℝ := fun a => if a.1=a.2 then w a.1 else 0
  have hc : ∀ a, 0 ≤ c a := by intro a; dsimp [c]; split_ifs; exact (hw a.1).le; rfl
  have hr : ∀ i, ∑ j, c (i,j)=w i := by intro i; simp [c]
  have he : ∀ j, ∑ i, c (i,j)=w j := by intro j; simp [c]
  let B := max (q (Fin.last k):ℝ) (p (Fin.last k):ℝ)
  have hB0 : 0 ≤ B := (q (Fin.last k)).2.1.trans (le_max_left _ _)
  have hB1 : B < 1 := max_lt hq1 hp1
  have hQ (i : Fin (k+1)) : (q i:ℝ) ≤ B :=
    (show (q i:ℝ) ≤ (q (Fin.last k):ℝ) from hq (Fin.le_last i)).trans (le_max_left _ _)
  have hP (i : Fin (k+1)) : (p i:ℝ) ≤ B :=
    (show (p i:ℝ) ≤ (p (Fin.last k):ℝ) from hp (Fin.le_last i)).trans (le_max_right _ _)
  have H := entropy_coupled_stationary_comparison c w h w g q p hc
    (fun i => (hw i).le) hw1 (fun i => (hw i).le) hw1 hr he B hB0 hB1 hQ hP hsq
  have H' := entropy_coupled_stationary_comparison c w g w h p q hc
    (fun i => (hw i).le) hw1 (fun i => (hw i).le) hw1 hr he B hB0 hB1 hP hQ hsp
  have hsum : (∑ a, c a*|h a.1-g a.2|)=∑ i, w i*|h i-g i| := by
    simp only [Fintype.sum_prod_type,c,ite_mul,zero_mul]
    simp
  have hsum' : (∑ a, c a*|g a.1-h a.2|)=∑ i, w i*|h i-g i| := by
    simp only [Fintype.sum_prod_type,c,ite_mul,zero_mul]
    simp [abs_sub_comm]
  rw [hsum] at H
  rw [hsum'] at H'
  unfold finiteSphericalDualObjective
  exact abs_le.mpr ⟨by linarith,by linarith⟩

end SphericalPerceptron
end
end

end OAI
