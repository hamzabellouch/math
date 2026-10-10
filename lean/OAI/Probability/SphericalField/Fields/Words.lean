import Mathlib
import OAI.Probability.SphericalField.Cascade.HeatWord
import OAI.Probability.SphericalField.Heat.Grid
import OAI.Probability.SphericalField.Sphere.FiniteUniform

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators

namespace SphericalPerceptron

lemma cascadeHeatWord_eq_ofFn (σ : ℕ → ℝ) (k : ℕ) (z : Fin k → ℝ) :
    cascadeHeatWord σ k z=List.ofFn (fun i => (z i,σ (k-1-i.val))) := by
  induction k with
  | zero => simp [cascadeHeatWord]
  | succ k ih =>
    rw [cascadeHeatWord,List.ofFn_succ,ih]
    simp only [Fin.val_zero,Nat.add_sub_cancel,Nat.sub_zero]
    congr 1
    congr 1
    funext i
    have he : k-1-i.val=k+1-1-i.succ.val := by simp only [Fin.val_succ]; omega
    simp only [he,Nat.add_sub_cancel]

def fieldVariances (k : ℕ) (h : Fin (k+1) → ℝ) : Fin (k+1) → ℝ :=
  Fin.cases (2*h 0) (fun i => 2*(h i.succ-h i.castSucc))

def fieldExponents {k : ℕ} (w : Fin (k+1) → ℝ) : Fin (k+1) → ℝ :=
  Fin.cases 0 (stepCumulative w)

lemma fieldVariances_nonneg (k : ℕ) (h : Fin (k+1) → ℝ)
    (hh : Monotone h) (hh0 : 0 ≤ h 0) (i : Fin (k+1)) : 0 ≤ fieldVariances k h i := by
  refine Fin.cases ?_ (fun i => ?_) i
  · exact mul_nonneg (by norm_num) hh0
  · exact mul_nonneg (by norm_num) (sub_nonneg.mpr (hh (Fin.castSucc_le_succ i)))

lemma fieldVariances_sum (k : ℕ) (h : Fin (k+1) → ℝ) :
    (∑ i, fieldVariances k h i)=2*h (Fin.last k) := by
  rw [Fin.sum_univ_succ]
  simp only [fieldVariances,Fin.cases_zero,Fin.cases_succ]
  rw [← Finset.mul_sum,finite_sum_successive_differences]
  ring

lemma fieldExponents_nonneg {k : ℕ} (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 < w i)
    (i : Fin (k+1)) : 0 ≤ fieldExponents w i := by
  refine Fin.cases (by rfl) (fun j => (stepCumulative_pos w hw j).le) i

lemma fieldExponents_lt_one {k : ℕ} (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 < w i)
    (hw1 : ∑ i, w i=1) (i : Fin (k+1)) : fieldExponents w i < 1 := by
  refine Fin.cases (by norm_num [fieldExponents]) (fun j => stepCumulative_lt_one w hw hw1 j) i

lemma fieldExponents_strictMono {k : ℕ} (w : Fin (k+1) → ℝ) (hw : ∀ i, 0 < w i) :
    StrictMono (fieldExponents w) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases (by simp) (fun j _ => stepCumulative_pos w hw j) j
  · intro j
    refine Fin.cases (by simp) (fun j hij => stepCumulative_strictMono w hw (Fin.succ_lt_succ_iff.mp hij)) j

lemma stepFieldIncrement_reverse (k : ℕ) (h : Fin (k+1) → ℝ) (i : Fin k) :
    stepFieldIncrement k h (k-1-i.val)=Real.sqrt (2*(h i.succ-h i.castSucc)) := by
  have hi : k-1-i.val < k := by omega
  have he : Fin.rev (⟨k-1-i.val,hi⟩ : Fin k)=i := by
    apply Fin.ext
    simp only [Fin.val_rev]
    omega
  rw [stepFieldIncrement,dite_eq_left hi,he]

lemma fieldWord_eq (k : ℕ) (w h : Fin (k+1) → ℝ) :
    List.ofFn (fun i => (fieldExponents w i,Real.sqrt (fieldVariances k h i)))=
      (0,Real.sqrt (2*h 0))::cascadeHeatWord (stepFieldIncrement k h) k (stepCumulative w) := by
  rw [List.ofFn_succ,cascadeHeatWord_eq_ofFn]
  simp only [fieldExponents,fieldVariances,Fin.cases_zero,Fin.cases_succ,stepFieldIncrement_reverse]

def sphericalHeatValue (n : ℕ) (l : List (ℝ×ℝ)) : ℝ :=
  gaussianBackward (stdGaussian (Spin (n+1))) l
    (logSphericalExp n (Real.sqrt (n+1:ℕ))) 0/(n+1:ℕ)-(l.map fun c => c.2^2).sum/2

lemma finiteSphericalFieldValue_eq_heat {k : ℕ} (w h : Fin (k+1) → ℝ)
    (hw : ∀ i, 0 < w i) (hw1 : ∑ i, w i=1) (hh : Monotone h) (hh0 : 0 ≤ h 0) (n : ℕ) :
    finiteSphericalFieldValue n k w h=sphericalHeatValue n
      (List.ofFn fun i => (fieldExponents w i,Real.sqrt (fieldVariances k h i))) := by
  have hs : ((List.ofFn fun i => (fieldExponents w i,Real.sqrt (fieldVariances k h i))).map
      fun c => c.2^2).sum=2*h (Fin.last k) := by
    rw [List.map_ofFn,List.sum_ofFn]
    change (∑ i, (Real.sqrt (fieldVariances k h i))^2)=_
    simp only [Real.sq_sqrt (fieldVariances_nonneg k h hh hh0 _)]
    exact fieldVariances_sum k h
  have ha := finiteAmplitudeSphereValue_fieldAmplitudes n k w h hh0
  unfold finiteAmplitudeSphereValue at ha
  rw [fieldAmplitudes_increment,fieldAmplitudes_last,
    amplitudeSphereValue_eq_backward n k (stepFieldIncrement k h) (stepCumulative w)
      (stepCumulative_strictMono w hw) (stepCumulative_pos w hw)
      (stepCumulative_lt_one w hw hw1)] at ha
  rw [sphericalHeatValue,hs,fieldWord_eq]
  linarith

def varianceLevels {k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin (k+1)) : ℝ :=
  (∑ j, if j ≤ i then v j else 0)/2

lemma varianceLevels_zero {k : ℕ} (v : Fin (k+1) → ℝ) : varianceLevels v 0=v 0/2 := by
  simp [varianceLevels]

lemma varianceLevels_last {k : ℕ} (v : Fin (k+1) → ℝ) :
    varianceLevels v (Fin.last k)=(∑ j, v j)/2 := by
  simp [varianceLevels,Fin.le_last]

lemma varianceLevels_increment {k : ℕ} (v : Fin (k+1) → ℝ) (i : Fin k) :
    varianceLevels v i.succ-varianceLevels v i.castSucc=v i.succ/2 := by
  unfold varianceLevels
  rw [← sub_div,← Finset.sum_sub_distrib]
  congr 1
  have he : (fun j : Fin (k+1) => (if j ≤ i.succ then v j else 0)-
      (if j ≤ i.castSucc then v j else 0))=fun j => if j=i.succ then v j else 0 := by
    funext j
    by_cases h₁ : j ≤ i.castSucc
    · have h₂ : j ≤ i.succ := h₁.trans (Fin.castSucc_le_succ i)
      have h₃ : j ≠ i.succ := by intro e; subst j; simp [Fin.le_def,Fin.val_succ] at h₁
      simp [h₁,h₂,h₃]
    · by_cases h₂ : j ≤ i.succ
      · have hj : j=i.succ := by apply Fin.ext; simp only [Fin.le_def,Fin.val_castSucc,Fin.val_succ] at *; omega
        simp [hj]
      · have h₃ : j ≠ i.succ := by intro e; subst j; exact h₂ le_rfl
        simp [h₁,h₂,h₃]
  rw [he]
  simp

lemma fieldVariances_varianceLevels {k : ℕ} (v : Fin (k+1) → ℝ) :
    fieldVariances k (varianceLevels v)=v := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [fieldVariances,varianceLevels_zero]; ring
  · simp [fieldVariances,varianceLevels_increment]; ring

lemma varianceLevels_monotone {k : ℕ} (v : Fin (k+1) → ℝ) (hv : ∀ i, 0 ≤ v i) :
    Monotone (varianceLevels v) := by
  apply Fin.monotone_iff_le_succ.mpr
  intro i
  have h := varianceLevels_increment v i
  linarith [hv i.succ]

lemma varianceLevels_nonneg {k : ℕ} (v : Fin (k+1) → ℝ) (hv : ∀ i, 0 ≤ v i)
    (i : Fin (k+1)) : 0 ≤ varianceLevels v i := by
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro j _
  split_ifs <;> first | exact hv j | rfl

lemma gaussianGrid_spherical_last (n k : ℕ) (p v : Fin (k+2) → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hv : 0 ≤ v (Fin.last (k+1))) (hpl : p (Fin.last (k+1))=1) :
    gaussianGrid (k+2) p v (logSphericalExp n (Real.sqrt (n+1:ℕ)))=
      fun x => gaussianGrid (k+1) (fun i => p i.castSucc) (fun i => v i.castSucc)
        (logSphericalExp n (Real.sqrt (n+1:ℕ))) x+(n+1:ℕ)*v (Fin.last (k+1))/2 := by
  unfold gaussianGrid
  rw [List.ofFn_succ_last,gaussianBackward_append]
  simp only [gaussianBackward]
  have he : gaussianEntropic (stdGaussian (Spin (n+1))) (p (Fin.last (k+1)))
      (Real.sqrt (v (Fin.last (k+1)))) (logSphericalExp n (Real.sqrt (n+1:ℕ)))=
        fun x => logSphericalExp n (Real.sqrt (n+1:ℕ)) x+(n+1:ℕ)*v (Fin.last (k+1))/2 := by
    funext x
    rw [hpl,gaussianEntropic_logSphericalExp_one,Real.sq_sqrt (by positivity),Real.sq_sqrt hv]
  rw [he]
  apply gaussianBackward_add_const _ (logSphericalExp_lipschitz n (Real.sqrt (n+1:ℕ)))
  intro c hc
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
  exact hp i.castSucc

end SphericalPerceptron
end
end

end OAI
