import Mathlib
import OAI.Probability.Perceptron.Variational.PureLabel
import OAI.Probability.Perceptron.Variational.DensityDerivative
import OAI.Probability.Perceptron.Variational.StepDual

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

lemma diagonalCascadeWord_response_sum {I : Type} [Fintype I]
    (A : ℕ→I→ℝ) (i : I) (k : ℕ) (z : Fin k→ℝ) :
    ((diagonalCascadeWord A k z).map (fun a => a.1*(a.2 i)^2)).sum=
      ∑ l : Fin k, z l*(A (k-1-l.val) i)^2 := by
  induction k with
  | zero => simp [diagonalCascadeWord]
  | succ k ih =>
    simp only [diagonalCascadeWord,List.map_cons,List.sum_cons,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Nat.add_sub_cancel,Nat.sub_zero,Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro l _
    have he : k-1-l.val=k-(l.val+1) := by omega
    rw [he]

lemma pureLabelResponse_sum {N k : ℕ} (p d : Fin N→ℕ) (j : Fin N) (hp : p j=0)
    (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) :
    pureLabelResponse p d j hp k h z=
      ∑ i : Fin k, z i*((((i.val+1:ℕ):ℝ)/(k+1:ℕ))^(d j)-
        ((i.val:ℝ)/(k+1:ℕ))^(d j)) := by
  rw [pureLabelResponse,diagonalCascadeWord_response_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hlt : k-1-i.val<k := by omega
  have he1 : k-(k-1-i.val)=i.val+1 := by omega
  have he0 : k-(k-1-i.val)-1=i.val := by omega
  simp only [enrichedIncrementFactors,dite_eq_left hlt,enrichedCoordinateLevel,pureLabelIndex,he1,Nat.add_sub_cancel]
  rw [Real.sq_sqrt]
  apply sub_nonneg.mpr
  apply pow_le_pow_left₀ (by positivity)
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast Nat.le_add_right i.val 1

lemma pureLabelResponse_weights {N k : ℕ} (p d : Fin N→ℕ) (j : Fin N) (hp : p j=0)
    (h w : Fin (k+1)→ℝ) (hw1 : ∑ i, w i=1) :
    pureLabelResponse p d j hp k h (stepCumulative w)=
      ((k:ℝ)/(k+1:ℕ))^(d j)-∑ i, w i*((i.val:ℝ)/(k+1:ℕ))^(d j) := by
  rw [pureLabelResponse_sum]
  have he := finite_weighted_increment_identity k w (fun i => ((i.val:ℝ)/(k+1:ℕ))^(d j))
  simp only [Fin.val_last,Fin.val_zero,hw1,sub_self,mul_zero,zero_add,Fin.val_succ,Fin.val_castSucc] at he
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  have hc : stepCumulative w i=1-∑ l : Fin (k+1), if i.castSucc<l then w l else 0 := by
    rw [← hw1,← Finset.sum_sub_distrib]
    unfold stepCumulative
    apply Finset.sum_congr rfl
    intro l _
    by_cases hl : l ≤ i.castSucc
    · simp [hl,not_lt.mpr hl]
    · simp [hl,lt_of_not_ge hl]
  rw [hc]
  push_cast
  ring

lemma sourceCountExpectedLog_pure_response (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (j : Fin (n+1)) (hp : p j=0)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (M : ℕ) :
    sourceCountExpectedLog n k f p d h z u M=
      sourceCountExpectedLog n k f p d h z (Function.update u j 0) M+
        (perturbationAmplitude (n+1) u j)^2/2*pureLabelResponse p d j hp k h z := by
  have hi (v : Fin (n+1)→ℝ) := (enrichedPoissonLog_section_variance n M k f p d v h z hz hz0 hz1).1.integrable (by norm_num)
  have he (v : Fin (n+1)→ℝ) : sourceCountExpectedLog n k f p d h z v M=
      ∫ g, enrichedExpectedLog n M k f p d v h z (patternPrefix (n+1) M g)
        ∂infinitePatternRowsLaw (n+1) := integral_prod _ (hi v)
  rw [he,he]
  simp_rw [enrichedExpectedLog_pure_response n M k f _ p d u j hp h z hz hz0 hz1]
  have hi' : Integrable (fun g => enrichedExpectedLog n M k f p d (Function.update u j 0) h z
      (patternPrefix (n+1) M g)) (infinitePatternRowsLaw (n+1)) :=
    (hi (Function.update u j 0)).integral_prod_left
  rw [integral_add hi' (integrable_const _),integral_const,
    probReal_univ,one_smul]

lemma sourceExpectedPressure_pure_response (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (j : Fin (n+1)) (hp : p j=0)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    sourceExpectedPressure n k f p d h z t u=
      sourceExpectedPressure n k f p d h z t (Function.update u j 0)+
        (1/(n+1:ℕ))*(perturbationAmplitude (n+1) u j)^2/2*pureLabelResponse p d j hp k h z := by
  simp_rw [sourceExpectedPressure_poissonMean n k f p d h z _ hz hz0 hz1]
  have he (v : Fin (n+1)→ℝ) :
      poissonRealMean (sourceCountExpectedLog n k f p d h z v) ((n+1:ℕ)*(t:ℝ))=
        ∫ M, sourceCountExpectedLog n k f p d h z v M ∂poissonMeasure ((n+1:ℕ)*t) := by
    simpa only [NNReal.coe_mul,NNReal.coe_natCast] using poissonRealMean_eq_integral (norm_nonneg f)
      (sourceCountExpectedLog_increment n k f p d h z v hz hz0 hz1) ((n+1:ℕ)*t)
  rw [he,he]
  simp_rw [sourceCountExpectedLog_pure_response n k f p d h z u j hp hz hz0 hz1]
  have hi := (poisson_bounded_increment_memLp ((n+1:ℕ)*t) (norm_nonneg f)
    (sourceCountExpectedLog_increment n k f p d h z (Function.update u j 0) hz hz0 hz1)).integrable (by norm_num)
  rw [integral_add hi (integrable_const _),integral_const,probReal_univ,one_smul]
  ring

lemma sourceExpectedPressure_pure_derivative (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (h : Fin (k+1)→ℝ) (z : Fin k→ℝ) (u : Fin (n+1)→ℝ)
    (j : Fin (n+1)) (hp : p j=0)
    (hz : StrictMono z) (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0) :
    HasDerivAt (fun r => sourceExpectedPressure n k f p d h z t (u+Pi.single j r))
      ((1/(n+1:ℕ))*perturbationAmplitude (n+1) (fun _ => 1) j*
        perturbationAmplitude (n+1) u j*pureLabelResponse p d j hp k h z) 0 := by
  classical
  have he (r : ℝ) : Function.update (u+Pi.single j r) j 0=Function.update u j 0 := by
    funext l
    by_cases hl : l=j
    · subst l; simp
    · simp [Function.update_of_ne hl,Pi.single_eq_of_ne hl]
  have ha (r : ℝ) : perturbationAmplitude (n+1) (u+Pi.single j r) j=
      perturbationAmplitude (n+1) (fun _ => 1) j*(u j+r) := by
    simp only [perturbationAmplitude,Pi.add_apply,Pi.single_eq_same,mul_one]
  have hf : (fun r => sourceExpectedPressure n k f p d h z t (u+Pi.single j r))=
      (fun r => sourceExpectedPressure n k f p d h z t (Function.update u j 0)+
        (1/(n+1:ℕ))*(perturbationAmplitude (n+1) (fun _ => 1) j*(u j+r))^2/2*
          pureLabelResponse p d j hp k h z) := by
    funext r
    rw [sourceExpectedPressure_pure_response n k f p d h z _ j hp hz hz0 hz1 t,he,ha]
  rw [hf]
  convert (((((hasDerivAt_id (0:ℝ)).const_add (u j)).const_mul
      (perturbationAmplitude (n+1) (fun _ => 1) j)).pow 2).const_mul (1/((n+1:ℕ):ℝ)) |>.div_const (2:ℝ)
      |>.mul_const (pureLabelResponse p d j hp k h z) |>.const_add
        (sourceExpectedPressure n k f p d h z t (Function.update u j 0))) using 1
  all_goals first | rfl | (simp only [perturbationAmplitude,id_eq,add_zero,mul_one,Nat.reduceSub,Nat.cast_ofNat,pow_one]; ring)

lemma source_label_moment (n k : ℕ) (f : ℝ →ᵇ ℝ)
    (p d : Fin (n+1)→ℕ) (h w : Fin (k+1)→ℝ)
    (hh0 : ∀ l, 0≤h l) (hh : Monotone h) (hw : ∀ l, 0<w l) (hw1 : ∑ l, w l=1)
    (u : Fin (n+1)→ℝ) (j : Fin (n+1)) (hp : p j=0) (hu : u j≠0) (t : ℝ≥0) :
    ∫ a, gibbsReplicaMean (sourceSpinLeafKernel n k a.1)
        (sourceCouplingHamiltonian n k f p d h u a) 2
        (fun x => (((indexedCommonDepth k (x 0).2 (x 1).2).val:ℝ)/(k+1:ℕ))^(d j))
      ∂((sourceBaseDataLaw n k (stepCumulative w) t).prod countableGaussianLaw)=
      ∑ l, w l*((l.val:ℝ)/(k+1:ℕ))^(d j) := by
  have hz := stepCumulative_strictMono w hw
  have hz0 := stepCumulative_pos w hw
  have hz1 := stepCumulative_lt_one w hw hw1
  obtain ⟨D,hD,he⟩ := sourceExpectedPressure_coordinate_derivative n k f p d h hh0 hh u j
    (stepCumulative w) hz hz0 hz1 t
  have hd := sourceExpectedPressure_pure_derivative n k f p d h (stepCumulative w) u j hp hz hz0 hz1 t
  change HasDerivAt (fun r => sourceExpectedPressure n k f p d h (stepCumulative w) t (u+Pi.single j r)) D 0 at hD
  have hsame := hD.unique hd
  rw [he,pureLabelResponse_weights p d j hp h w hw1] at hsame
  simp only [sourceCouplingCovariance,sourceJointMonomial,hp,pow_zero,mul_one,
    replicaMean_const_mul,integral_const_mul] at hsame
  have hA : perturbationAmplitude (n+1) (fun _ => 1) j≠0 := by
    unfold perturbationAmplitude perturbationScale
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) (by positivity)) one_ne_zero
  have hB : perturbationAmplitude (n+1) u j≠0 := by
    unfold perturbationAmplitude perturbationScale
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by positivity) (by positivity)) (by positivity)) hu
  have hN : (1/((n+1:ℕ):ℝ))≠0 := by positivity
  apply (mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hN hA) hB))
  nlinarith [hsame]

end SphericalPerceptronFreeEnergy
end

end OAI
