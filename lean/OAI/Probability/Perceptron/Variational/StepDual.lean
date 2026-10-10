import Mathlib
import OAI.Probability.Perceptron.Variational.StepEntropy

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma finite_weighted_increment_identity (k : ℕ) (a h : Fin (k+1) → ℝ) :
    h (Fin.last k)-∑ j, a j*h j = h 0*(1-∑ j, a j)+
      ∑ i : Fin k, (h i.succ-h i.castSucc)*(1-∑ j : Fin (k+1), if i.castSucc < j then a j else 0) := by
  classical
  induction k with
  | zero => simp [Fin.fin_one_eq_zero]; ring
  | succ k ih =>
    have ht := ih (fun j => a j.succ) (fun j => h j.succ)
    have hl0 : (∑ j : Fin (k+2), if (0:Fin (k+2)) < j then a j else 0) =
        ∑ j : Fin (k+1), a j.succ := by
      rw [Fin.sum_univ_succ]
      simp only [lt_self_iff_false,ite_false,Fin.succ_pos,ite_true,zero_add]
    have hlt (i : Fin k) : (∑ j : Fin (k+2), if i.castSucc.succ < j then a j else 0) =
        ∑ j : Fin (k+1), if i.castSucc < j then a j.succ else 0 := by
      rw [Fin.sum_univ_succ]
      simp only [Fin.not_lt_zero,ite_false,zero_add,Fin.succ_lt_succ_iff]
    rw [Fin.sum_univ_succ (fun j => a j*h j),Fin.sum_univ_succ a,
      Fin.sum_univ_succ (fun i : Fin (k+1) =>
        (h i.succ-h i.castSucc)*(1-∑ j : Fin (k+2), if i.castSucc < j then a j else 0))]
    simp only [Fin.castSucc_zero,Fin.succ_zero_eq_one,Fin.castSucc_succ]
    erw [hl0]
    simp only [hlt]
    simp only [Fin.succ_last,Fin.succ_zero_eq_one] at ht
    linear_combination ht

lemma weightedStepTail_root {k : ℕ} (w q : Fin (k+1) → ℝ)
    (hw1 : ∑ i, w i = 1) (hq : Monotone q) :
    weightedStepTail w q (q 0) = 1-∑ i, w i*q i := by
  unfold weightedStepTail
  simp only [max_eq_left (hq (Fin.zero_le _)),mul_sub,mul_one]
  rw [Finset.sum_sub_distrib,hw1]

lemma weightedStepTail_cut {k : ℕ} (w q : Fin (k+1) → ℝ)
    (hw1 : ∑ i, w i = 1) (hq : Monotone q) (i : Fin k) :
    weightedStepTail w q (q i.castSucc)+stepCumulative w i*q i.castSucc =
      1-∑ j : Fin (k+1), if i.castSucc < j then w j*q j else 0 := by
  unfold weightedStepTail stepCumulative
  rw [Finset.sum_mul,← Finset.sum_add_distrib,← hw1,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j ≤ i.castSucc
  · rw [ite_eq_left hj,ite_eq_right (not_lt.mpr hj),max_eq_right (hq hj)]
    rw [hw1]
    ring
  · rw [ite_eq_right hj,ite_eq_left (lt_of_not_ge hj),max_eq_left (hq (le_of_not_ge hj))]
    rw [hw1]
    ring

lemma finite_sum_successive_differences (k : ℕ) (v : Fin (k+1) → ℝ) :
    (∑ i : Fin k, (v i.succ-v i.castSucc)) = v (Fin.last k)-v 0 := by
  have h1 := Fin.sum_univ_succ v
  have h2 := Fin.sum_univ_castSucc v
  rw [Finset.sum_sub_distrib]
  linarith

lemma stationary_field_shift_identity {k : ℕ} (w q h : Fin (k+1) → ℝ)
    (hw1 : ∑ i, w i = 1) (hq : Monotone q)
    (hD : ∀ i, 0 < weightedStepTail w q (q i))
    (hroot : 2*h 0=q 0/(weightedStepTail w q (q 0))^2)
    (hinc : ∀ i : Fin k, 2*(h i.succ-h i.castSucc)=
      (q i.succ-q i.castSucc)/(weightedStepTail w q (q i.castSucc)*weightedStepTail w q (q i.succ))) :
    2*(h (Fin.last k)-∑ i, w i*h i*q i) = (weightedStepTail w q (q (Fin.last k)))⁻¹-1 := by
  let D := fun i => weightedStepTail w q (q i)
  have hgap (i : Fin k) : D i.castSucc-D i.succ = stepCumulative w i*(q i.succ-q i.castSucc) := by
    have he := weightedStepTail_affine w q hq i (t := q i.succ) ⟨hq (Fin.castSucc_le_succ i),le_rfl⟩
    change D i.succ = D i.castSucc-stepCumulative w i*(q i.succ-q i.castSucc) at he
    linarith
  have hroot' : 2*h 0*(1-∑ i, w i*q i) = q 0/D 0 := by
    rw [← weightedStepTail_root w q hw1 hq,hroot]
    change (q 0/(D 0)^2)*D 0=q 0/D 0
    field_simp [(hD 0).ne']
  have hinc' (i : Fin k) : 2*(h i.succ-h i.castSucc)*
      (1-∑ j : Fin (k+1), if i.castSucc < j then w j*q j else 0) =
        q i.succ/D i.succ-q i.castSucc/D i.castSucc := by
    rw [← weightedStepTail_cut w q hw1 hq i,hinc i]
    change ((q i.succ-q i.castSucc)/(D i.castSucc*D i.succ))*
      (D i.castSucc+stepCumulative w i*q i.castSucc)=_
    have hg := hgap i
    have h1 : D i.castSucc ≠ 0 := (hD i.castSucc).ne'
    have h2 : D i.succ ≠ 0 := (hD i.succ).ne'
    field_simp [h1,h2]
    linear_combination -q i.castSucc * hg
  have he := finite_weighted_increment_identity k (fun i => w i*q i) h
  have hend : D (Fin.last k) = 1-q (Fin.last k) :=
    weightedStepTail_of_le w q hw1 (fun i => hq (Fin.le_last i))
  calc
    _ = 2*h 0*(1-∑ i, w i*q i)+∑ i : Fin k,
        2*(h i.succ-h i.castSucc)*(1-∑ j : Fin (k+1), if i.castSucc < j then w j*q j else 0) := by
      simp only [mul_right_comm (w _) (h _) (q _)]
      rw [he,mul_add,Finset.mul_sum]
      ring_nf
    _ = q 0/D 0+∑ i : Fin k, (q i.succ/D i.succ-q i.castSucc/D i.castSucc) := by
      rw [hroot']
      congr 1
      exact Finset.sum_congr rfl (fun i _ => hinc' i)
    _ = q (Fin.last k)/D (Fin.last k) := by
      rw [finite_sum_successive_differences k (fun i => q i/D i)]
      ring
    _ = _ := by
      change q (Fin.last k)/D (Fin.last k)=(D (Fin.last k))⁻¹-1
      have hn : D (Fin.last k) ≠ 0 := (hD (Fin.last k)).ne'
      field_simp [hn]
      linarith

def stepFieldIncrement (k : ℕ) (h : Fin (k+1) → ℝ) (j : ℕ) : ℝ :=
  if hj : j < k then
    Real.sqrt (2*(h (Fin.rev ⟨j,hj⟩).succ-h (Fin.rev ⟨j,hj⟩).castSucc)) else 0

lemma stepFieldIncrement_sq (k : ℕ) (h : Fin (k+1) → ℝ) (hh : Monotone h) (i : Fin k) :
    (stepFieldIncrement k h (k-1-i.val))^2 = 2*(h i.succ-h i.castSucc) := by
  have hi : k-1-i.val < k := by omega
  have he : Fin.rev (⟨k-1-i.val,hi⟩ : Fin k) = i := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [stepFieldIncrement,dite_eq_left hi,he,Real.sq_sqrt]
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr (hh (Fin.castSucc_le_succ i)))

def finiteSphericalFieldValue (n k : ℕ) (w h : Fin (k+1) → ℝ) : ℝ :=
  expectedCoordinateSphereLog n k (stepFieldIncrement k h) (stepCumulative w)
    (Real.toNNReal (2*h 0))-h (Fin.last k)

theorem finiteSphericalFieldValue_stationary {k : ℕ} (w h : Fin (k+1) → ℝ)
    (q : Fin (k+1) → Time) (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i = 1)
    (hq : Monotone q) (hq1 : (q (Fin.last k):ℝ) < 1)
    (hstat : ∀ i, 2*h i = weightedStepA w (fun j => (q j:ℝ)) (q i)) :
    Tendsto (fun n : ℕ => finiteSphericalFieldValue n k w h) atTop
      (𝓝 ((entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal-
        ∑ i, w i*h i*(q i:ℝ))) := by
  let Q : Fin (k+1) → ℝ := fun i => q i
  let D : Fin (k+1) → ℝ := fun i => weightedStepTail w Q (Q i)
  have hm : Monotone Q := fun i j hij => hq hij
  have h0 : 0 ≤ Q 0 := (q 0).2.1
  have hmax (i : Fin (k+1)) : Q i ≤ Q (Fin.last k) := hm (Fin.le_last i)
  have hD (i : Fin (k+1)) : 0 < D i :=
    weightedStepTail_pos w Q (fun i => (hw i).le) hw1 hq1 hmax (hmax i)
  have hz := stepCumulative_strictMono w hw
  have hz0 := stepCumulative_pos w hw
  have hz1 := stepCumulative_lt_one w hw hw1
  have hroot : 2*h 0=Q 0/(D 0)^2 :=
    (hstat 0).trans (weightedStepA_root w Q hm h0)
  have hinc (i : Fin k) : 2*(h i.succ-h i.castSucc)=
      (Q i.succ-Q i.castSucc)/(D i.castSucc*D i.succ) := by
    calc
      _ = weightedStepA w Q (Q i.succ)-weightedStepA w Q (Q i.castSucc) := by
        linarith [hstat i.succ,hstat i.castSucc]
      _ = _ := weightedStepA_increment w Q (fun i => (hw i).le) hw1 hm h0 hq1 i (hz0 i)
  have hh : Monotone h := by
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    have hp := div_nonneg (sub_nonneg.mpr (hm (Fin.castSucc_le_succ i)))
      (mul_pos (hD i.castSucc) (hD i.succ)).le
    rw [← hinc i] at hp
    linarith
  have hr0 : 0 ≤ 2*h 0 := by rw [hroot]; positivity
  have hr : (Real.toNNReal (2*h 0):ℝ)=Q 0/(D 0)^2 := by rw [Real.coe_toNNReal _ hr0,hroot]
  have hend : D (Fin.last k) = 1-Q (Fin.last k) := weightedStepTail_of_le w Q hw1 hmax
  have hgap (i : Fin k) : D i.castSucc-D i.succ=stepCumulative w i*(Q i.succ-Q i.castSucc) := by
    have he := weightedStepTail_affine w Q hm i (t := Q i.succ) ⟨hm (Fin.castSucc_le_succ i),le_rfl⟩
    change D i.succ=D i.castSucc-stepCumulative w i*(Q i.succ-Q i.castSucc) at he
    linarith
  have hσ (i : Fin k) : (stepFieldIncrement k h (k-1-i.val))^2=
      (Q i.succ-Q i.castSucc)/(D i.castSucc*D i.succ) :=
    (stepFieldIncrement_sq k h hh i).trans (hinc i)
  have ht := (expectedCoordinateSphereLog_stationary_data k (stepFieldIncrement k h)
    Q D (stepCumulative w) hz hz0 hz1 hD hend hgap hσ _ hr).sub_const (h (Fin.last k))
  have he := entropy_weightedStepTrial_toReal_finite_formula w q (fun i => (hw i).le) hw1 hq hq1 hz0
  simp only [tailIntegral_weightedStepTrial] at he
  change (entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal =
    Real.log (D (Fin.last k))/2+stepLogRatios k D (stepCumulative w)+Q 0/(2*D 0) at he
  have hs := stationary_field_shift_identity w Q h hw1 hm hD hroot hinc
  have hv : Real.log (D (Fin.last k))/2+stepLogRatios k D (stepCumulative w)+Q 0/(2*D 0)+
      ((D (Fin.last k))⁻¹-1)/2-h (Fin.last k) =
      (entropy (weightedStepTrial w q (fun i => (hw i).le) hw1)).toReal-∑ i, w i*h i*Q i := by
    rw [he]
    change 2*(h (Fin.last k)-∑ i, w i*h i*Q i)=(D (Fin.last k))⁻¹-1 at hs
    linarith
  rw [hv] at ht
  exact ht

end SphericalPerceptronFreeEnergy
end

end OAI
