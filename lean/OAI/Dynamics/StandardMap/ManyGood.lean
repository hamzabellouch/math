import OAI.Dynamics.StandardMap.MatchingCore

namespace OAI

open MeasureTheory Set
open scoped ENNReal BigOperators

open MeasureTheory Set Filter Metric
open scoped Topology ENNReal
namespace StandardMapEntropy
lemma pairMagnitude_wronskian (v : ℕ → ℝ) (b : ℝ) (N : ℕ) (hN : 1≤N) :
    1 ≤ 2*pairMagnitude (linearSolution v 1 b) N*pairMagnitude (tSolution v) N := by
  let u:=linearSolution v 1 b
  let t:=tSolution v
  have hw := solution_wronskian v 1 b (N-1)
  rw [Nat.sub_add_cancel hN] at hw
  have habs : |u (N-1)*t N-u N*t (N-1)|=1 := by rw [hw]; norm_num
  have h1 : |u (N-1)|≤pairMagnitude u N := le_max_right _ _
  have h2 : |u N|≤pairMagnitude u N := le_max_left _ _
  have h3 : |t N|≤pairMagnitude t N := le_max_left _ _
  have h4 : |t (N-1)|≤pairMagnitude t N := le_max_right _ _
  calc
    1 = |u (N-1)*t N-u N*t (N-1)| := habs.symm
    _ ≤ |u (N-1)| *|t N|+|u N| *|t (N-1)| := by simpa only [abs_mul] using abs_sub (u (N-1)*t N) (u N*t (N-1))
    _ ≤ pairMagnitude u N*pairMagnitude t N+pairMagnitude u N*pairMagnitude t N :=
      add_le_add (mul_le_mul h1 h3 (abs_nonneg _) (pairMagnitude_nonneg _ _))
        (mul_le_mul h2 h4 (abs_nonneg _) (pairMagnitude_nonneg _ _))
    _ = _ := by dsimp [u,t]; ring
lemma pairLog_t_one (v : ℕ → ℝ) (M : ℝ) : pairLog M (tSolution v) 1=0 := by
  simp [pairLog,pairMagnitude,tSolution]
lemma pairLog_normalized_one_nonneg (v : ℕ → ℝ) (b M : ℝ) (hM : 1<M) :
    0≤pairLog M (linearSolution v 1 b) 1 := by
  apply Real.logb_nonneg hM
  simp [pairMagnitude]
noncomputable def badIndices (M : ℝ) (v : ℕ → ℝ) (b : ℝ) (N : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (2:ℕ) (N-2)).filter fun j => ¬GoodIndex M v b j
lemma goodIndex_failure_bound (v : ℕ → ℝ) (b M : ℝ) (N : ℕ) (hN : 2≤N)
    (hM : 1<M) (hv : ∀ j, 1≤j → j<N → |v j|+1≤M) :
    ((badIndices M v b N).card : ℝ) ≤
      2*(((N:ℝ)-1-pairLog M (tSolution v) N)+
      ((N:ℝ)-1+pairLog M (linearSolution v 1 b) N-pairLog M (linearSolution v 1 b) 1))/(1-goodExponent) := by
  classical
  have ht (j : ℕ) (hj : 1≤j) (hjN : j<N) :=
    pairLog_step_abs M v 0 1 j hM hj (hv j hj hjN)
      (pairMagnitude_t_pos v j hj) (pairMagnitude_t_pos v (j+1) (by omega))
  have hu (j : ℕ) (hj : 1≤j) (hjN : j<N) :=
    pairLog_step_abs M v 1 b j hM hj (hv j hj hjN)
      (pairMagnitude_normalized_pos v b j hj) (pairMagnitude_normalized_pos v b (j+1) (by omega))
  have hh:=good_failures_count (pairLog M (tSolution v)) (fun j => -pairLog M (linearSolution v 1 b) j)
    goodExponent goodExponent_lt_one N hN
    (fun j hj hjN => (abs_le.mp (ht j hj hjN)).2)
    (fun j hj hjN => by have := (abs_le.mp (hu j hj hjN)).1; linarith)
  have he : (Finset.Icc (2:ℕ) (N-2)).filter (fun j => ¬GoodIndex M v b j) =
      (Finset.Icc (2:ℕ) (N-2)).filter (fun j => ¬
        ((∀ l : ℕ, 1≤l → l<j → goodExponent*((j:ℝ)-(l:ℝ))≤pairLog M (tSolution v) j-pairLog M (tSolution v) l) ∧
        goodExponent≤pairLog M (tSolution v) (j+1)-pairLog M (tSolution v) j ∧
        goodExponent≤ -pairLog M (linearSolution v 1 b) (j+1)-(-pairLog M (linearSolution v 1 b) j) ∧
        goodExponent≤ -pairLog M (linearSolution v 1 b) (j+2)-(-pairLog M (linearSolution v 1 b) (j+1)))) := by
    apply Finset.filter_congr
    intro j hj
    have hj2 := (Finset.mem_Icc.mp hj).1
    simp only [GoodIndex,hj2,true_and,neg_sub_neg]
  unfold badIndices
  rw [he]
  convert hh using 1
  rw [pairLog_t_one]
  ring
lemma small_endpoint_log_bounds (v : ℕ → ℝ) (b M E : ℝ) (N : ℕ)
    (hM : 1<M) (hN : 1≤N) (hE : 0<E)
    (hb : pairMagnitude (linearSolution v 1 b) N≤E) :
    -Real.logb M 2-Real.logb M E≤pairLog M (tSolution v) N ∧
    pairLog M (linearSolution v 1 b) N≤Real.logb M E := by
  have hu:=pairMagnitude_normalized_pos v b N hN
  have ht:=pairMagnitude_t_pos v N hN
  have hp : 1≤2*E*pairMagnitude (tSolution v) N := by
    have hh:=pairMagnitude_wronskian v b N hN
    exact hh.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hb (by norm_num)) ht.le)
  have hlog := (Real.logb_le_logb hM (by norm_num : (0:ℝ)<1) (by positivity : 0<2*E*pairMagnitude (tSolution v) N)).mpr hp
  rw [Real.logb_one,Real.logb_mul (by positivity : (2*E:ℝ)≠0) (ne_of_gt ht),
    Real.logb_mul (by norm_num : (2:ℝ)≠0) (ne_of_gt hE)] at hlog
  exact ⟨by dsimp [pairLog]; linarith,(Real.logb_le_logb hM hu hE).mpr hb⟩

lemma many_good_small_endpoint (v : ℕ → ℝ) (b M s : ℝ) (N : ℕ) (hN : 2≤N)
    (hM : 1<M) (hv : ∀ j, 1≤j → j<N → |v j|+1≤M)
    (hb : pairMagnitude (linearSolution v 1 b) N≤3*M^(-s)) :
    ((badIndices M v b N).card : ℝ) ≤
      (4*((N:ℝ)-1-s)+2*Real.logb M 2+4*Real.logb M 3)/(1-goodExponent) := by
  have hm : 0<M := lt_trans zero_lt_one hM
  have hh:=goodIndex_failure_bound v b M N hN hM hv
  have he : Real.logb M (3*M^(-s))=Real.logb M 3-s := by
    rw [Real.logb_mul (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos hm _)), Real.logb_rpow hm (ne_of_gt hM)]
    ring
  obtain ⟨ht,hu⟩:=small_endpoint_log_bounds v b M (3*M^(-s)) N hM (by omega) (by positivity) hb
  rw [he] at ht hu
  have hu1:=pairLog_normalized_one_nonneg v b M hM
  apply hh.trans
  apply (div_le_div_iff_of_pos_right (by linarith [goodExponent_lt_one] : 0<1-goodExponent)).mpr
  linarith
end StandardMapEntropy

end OAI
