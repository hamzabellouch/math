import Mathlib
import OAI.Probability.IsingPerceptron.ContactFaces

namespace OAI

/-! Nodal Gaussian Lipschitz. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

theorem nodalGaussianFold_lipschitz_strict {n : ℕ} (a b : ℕ → ℝ) (d : Fin n → ℝ)
    (ha : ∀ i : Fin n, a i.val < a (i.val+1))
    (hb : ∀ i : Fin n, b i.val < b (i.val+1)) (hd : ∀ i, 0 ≤ d i)
    (hfirst : a 0=b 0) (hlast : a n=b n)
    {f : ℝ → ℝ} (F : BoundedC2Data f) (x : ℝ) :
    |nodalGaussianFold b d f x-nodalGaussianFold a d f x| ≤
      F.C^2/2 * ∑ i, |(nextCoefficient d i-d i)*(b (i.val+1)-a (i.val+1))| := by
  let A : Fin n → ℝ := fun i => a (i.val+1)-a i.val
  let B : Fin n → ℝ := fun i => b (i.val+1)-b i.val
  have hA : ∀ i, 0 < A i := fun i => sub_pos.mpr (ha i)
  have hB : ∀ i, 0 < B i := fun i => sub_pos.mpr (hb i)
  let s := finiteAffineStep A B d hA hB hd
  let v : ℕ → ℝ := fun i => b i-a i
  have hs (i : Fin n) : (s i).v = v (i.val+1)-v i.val := by
    dsimp [s,finiteAffineStep,v,A,B]
    ring
  have hv0 : v 0=0 := by simp [v,hfirst]
  have hvn : v n=0 := by simp [v,hlast]
  have hsum : ((List.ofFn s).map AffineGaussianStep.v).sum=0 := by
    rw [List.map_ofFn,List.sum_ofFn]
    simp only [Function.comp_apply,hs,finite_delta_sum,hv0,hvn,sub_self]
  have hw : (∑ i, |variationWeights (List.ofFn s) i|) =
      ∑ i : Fin n, |(nextCoefficient d i-d i)*(b (i.val+1)-a (i.val+1))| := by
    apply Fintype.sum_equiv (finCongr (List.length_ofFn (f := s)))
    intro i
    have hi : variationWeights (List.ofFn s) i=ofFnWeights s (Fin.cast (List.length_ofFn (f := s)) i) := by
      simp only [ofFnWeights,variationWeightAt,Fin.val_cast,i.isLt,dite_eq_left]
    rw [hi,ofFnWeights_eq]
    simp only [hs,Fin.lt_def,finite_tail_delta_sum v n _ (Fin.cast (List.length_ofFn (f := s)) i).isLt,hvn,zero_sub,neg_neg]
    rfl
  have hh := gaussianFold_lipschitz (affineVarianceDomain_open A B)
    (F.family (affineVarianceDomain A B)) (fun _ => rfl) (List.ofFn s) hsum
    (affineVarianceDomain_segment hA hB) x
  rw [hw] at hh
  simp only [BoundedC2Data.family,GaussianFamily.terminal] at hh
  have he (t : ℝ) : (List.ofFn s).foldr
      (fun e U => gaussianTransform (e.a+e.v*t) e.d U) f x =
      (List.ofFn (fun i : Fin n => (A i+(B i-A i)*t,d i))).foldr
        (fun sd U => gaussianTransform sd.1 sd.2 U) f x := by
    have hm : List.ofFn (fun i : Fin n => (A i+(B i-A i)*t,d i)) =
        (List.ofFn s).map (fun e => (e.a+e.v*t,e.d)) := by
      rw [List.map_ofFn]
      rfl
    rw [hm,List.foldr_map]
  rw [he,he] at hh
  simpa only [mul_one,mul_zero,add_zero,add_sub_cancel,A,B,nodalGaussianFold] using hh

theorem nodalGaussianFold_lipschitz {n : ℕ} (a b : ℕ → ℝ) (d : Fin n → ℝ)
    (ha : ∀ i : Fin n, a i.val ≤ a (i.val+1))
    (hb : ∀ i : Fin n, b i.val ≤ b (i.val+1)) (hd : ∀ i, 0 ≤ d i)
    (hfirst : a 0=b 0) (hlast : a n=b n)
    {f : ℝ → ℝ} (F : BoundedC2Data f) (x : ℝ) :
    |nodalGaussianFold b d f x-nodalGaussianFold a d f x| ≤
      F.C^2/2 * ∑ i, |(nextCoefficient d i-d i)*(b (i.val+1)-a (i.val+1))| := by
  let ar := fun ε i => a i+ε*(i:ℝ)
  let br := fun ε i => b i+ε*(i:ℝ)
  have har : Continuous (fun ε : ℝ => nodalGaussianFold (ar ε) d f x) :=
    continuous_nodalGaussianFold_param ar d (fun i => by fun_prop) hd F.continuous F.bf x
  have hbr : Continuous (fun ε : ℝ => nodalGaussianFold (br ε) d f x) :=
    continuous_nodalGaussianFold_param br d (fun i => by fun_prop) hd F.continuous F.bf x
  have he (ε : ℝ) (hε : 0 < ε) :
      |nodalGaussianFold (br ε) d f x-nodalGaussianFold (ar ε) d f x| ≤
        F.C^2/2 * ∑ i, |(nextCoefficient d i-d i)*(b (i.val+1)-a (i.val+1))| := by
    have hw (i : Fin n) : (nextCoefficient d i-d i)*(br ε (i.val+1)-ar ε (i.val+1))=
        (nextCoefficient d i-d i)*(b (i.val+1)-a (i.val+1)) := by dsimp [br,ar]; ring
    have H := nodalGaussianFold_lipschitz_strict (ar ε) (br ε) d
    simp_rw [hw] at H
    apply H
    · intro i
      dsimp [ar]
      push_cast
      have := ha i
      nlinarith
    · intro i
      dsimp [br]
      push_cast
      have := hb i
      nlinarith
    · exact hd
    · simp only [ar,br,hfirst]
    · simp only [ar,br,hlast]
  have hb0 : Tendsto (fun ε => nodalGaussianFold (br ε) d f x) (𝓝[>] (0:ℝ))
      (𝓝 (nodalGaussianFold (br 0) d f x)) := hbr.continuousAt.tendsto.mono_left inf_le_left
  have ha0 : Tendsto (fun ε => nodalGaussianFold (ar ε) d f x) (𝓝[>] (0:ℝ))
      (𝓝 (nodalGaussianFold (ar 0) d f x)) := har.continuousAt.tendsto.mono_left inf_le_left
  have hle : ∀ᶠ ε in 𝓝[>] (0:ℝ), |nodalGaussianFold (br ε) d f x-nodalGaussianFold (ar ε) d f x| ≤
      F.C^2/2 * ∑ i, |(nextCoefficient d i-d i)*(b (i.val+1)-a (i.val+1))| := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact he ε hε
  simpa only [ar,br,zero_mul,add_zero] using le_of_tendsto ((hb0.sub ha0).abs) hle

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma uniformCellAverage_le_on {p q : ℝ → ℝ} (hp : Monotone p) (hq : Monotone q)
    (hpb : ∀ u, p u∈Icc (0:ℝ) 1) (hqb : ∀ u, q u∈Icc (0:ℝ) 1)
    (hle : ∀ u∈Ioo (0:ℝ) 1, p u≤q u) (n i : ℕ) (hi : i≤n) :
    uniformCellAverage p n i≤uniformCellAverage q n i := by
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono_ae (uniformCell_integrable hp hpb n i) (uniformCell_integrable hq hqb n i)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with u hu
  apply hle
  exact ⟨lt_of_le_of_lt (by positivity) hu.1,lt_of_lt_of_le hu.2
    ((div_le_one (by positivity)).mpr (by exact_mod_cast Nat.succ_le_succ hi))⟩

lemma uniformPattern_ordered_bound (p q : OverlapPath)
    (p' q' : ℝ → ℝ) (hpp : p'=ᵐ[pathMeasure] p.val) (hqq : q'=ᵐ[pathMeasure] q.val)
    (hp : Monotone p') (hq : Monotone q')
    (hpb : ∀ u, p' u∈Icc (0:ℝ) 1) (hqb : ∀ u, q' u∈Icc (0:ℝ) 1)
    (hle : ∀ u∈Ioo (0:ℝ) 1, p' u≤q' u) {f : ℝ → ℝ} (F : BoundedC2Data f) (n : ℕ) :
    |uniformPattern f q n-uniformPattern f p n| ≤
      F.C^2/2*((∫ u in Ioo (0:ℝ) 1, q' u)-(∫ u in Ioo (0:ℝ) 1, p' u)) := by
  rw [uniformPattern_eq_nodal,uniformPattern_eq_nodal]
  rw [← uniformNodal_congr (uniformCellAverage p' n) (cellAverage p (n+1)) n
    (uniformCellAverage_eq_cellAverage p p' hpp n)]
  rw [← uniformNodal_congr (uniformCellAverage q' n) (cellAverage q (n+1)) n
    (uniformCellAverage_eq_cellAverage q q' hqq n)]
  have H := nodalGaussianFold_lipschitz (uniformNodal (uniformCellAverage p' n) n)
    (uniformNodal (uniformCellAverage q' n) n) (uniformCoefficient n)
    (uniformNodal_increasing n (uniformCellAverage_monotone hp hpb n) (uniformCellAverage_mem hp hpb n))
    (uniformNodal_increasing n (uniformCellAverage_monotone hq hqb n) (uniformCellAverage_mem hq hqb n))
    (uniformCoefficient_nonneg n) (by simp only [uniformNodal_zero]) (by simp only [uniformNodal_last]) F 0
  have hw (i : Fin (n+1)) : |(1/(n+1:ℕ))*(uniformCellAverage q' n i.val-uniformCellAverage p' n i.val)|=
      (1/(n+1:ℕ))*(uniformCellAverage q' n i.val-uniformCellAverage p' n i.val) :=
    abs_of_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr (uniformCellAverage_le_on hp hq hpb hqb hle n i.val (by omega))))
  rw [Fin.sum_univ_castSucc] at H
  simp only [uniformWeight_last,abs_zero,add_zero,uniformWeight_castSucc,hw] at H
  rw [← Finset.mul_sum,Finset.sum_sub_distrib] at H
  have hs (r : ℝ → ℝ) (hr : Monotone r) : (∑ i : Fin (n+1), uniformCellAverage r n i.val)=
      (n+1:ℕ)*(∫ u in Ioo (0:ℝ) 1, r u) := by
    simpa only [Nat.zero_le,ite_true,Nat.cast_zero,zero_div] using uniformCellAverage_tail_sum hr n 0 (by omega)
  rw [hs q' hq,hs p' hp] at H
  convert H using 1; field_simp

theorem patternFunctional_ordered_bound (p q : OverlapPath)
    (p' q' : ℝ → ℝ) (hpp : p'=ᵐ[pathMeasure] p.val) (hqq : q'=ᵐ[pathMeasure] q.val)
    (hp : Monotone p') (hq : Monotone q')
    (hpb : ∀ u, p' u∈Icc (0:ℝ) 1) (hqb : ∀ u, q' u∈Icc (0:ℝ) 1)
    (hle : ∀ u∈Ioo (0:ℝ) 1, p' u≤q' u) {f : ℝ → ℝ} (F : BoundedC2Data f) :
    |patternFunctional f q-patternFunctional f p| ≤
      F.C^2/2*((∫ u in Ioo (0:ℝ) 1, q' u)-(∫ u in Ioo (0:ℝ) 1, p' u)) := by
  apply le_of_tendsto (((uniformPattern_tendsto q F.continuous F.bf).sub
    (uniformPattern_tendsto p F.continuous F.bf)).abs)
  exact Eventually.of_forall (uniformPattern_ordered_bound p q p' q' hpp hqq hp hq hpb hqb hle F)

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def lowerTrial (p : ℝ → ℝ) (hp : Monotone p) (hb : ∀ u, p u∈Icc (0:ℝ) 1) (n : ℕ) : OverlapPath :=
  overlapPathOfMonotone (lowerGrid p n) (lowerGrid_monotone hp n) (lowerGrid_mem hb n)

lemma lowerTrial_ae (p : ℝ → ℝ) (hp : Monotone p) (hb : ∀ u, p u∈Icc (0:ℝ) 1) (n : ℕ) :
    lowerGrid p n =ᵐ[pathMeasure] (lowerTrial p hp hb n).val := overlapPathOfMonotone_ae _ _ _

lemma lowerTrial_step (p : ℝ → ℝ) (hp : Monotone p) (hb : ∀ u, p u∈Icc (0:ℝ) 1) (n : ℕ) :
    finiteStepFunction (uniformCut n) (fun i : Fin (n+1) => (1-1/(n+1:ℕ))*p ((i.val:ℝ)/(n+1:ℕ)))
      =ᵐ[pathMeasure] (lowerTrial p hp hb n).val :=
  (lowerGrid_step_ae p n).symm.trans (lowerTrial_ae p hp hb n)

lemma lowerTrial_value_lt_one {p : ℝ → ℝ} (hb : ∀ u, p u∈Icc (0:ℝ) 1) (n : ℕ) (u : ℝ) :
    (1-1/(n+1:ℕ))*p u<1 := by
  have H := mul_le_mul_of_nonneg_left (hb u).2 (lowerGrid_factor_nonneg n)
  have hz : (0:ℝ)<1/(n+1:ℕ) := by positivity
  nlinarith

lemma lowerTrial_entropy_le (q : OverlapPath) (p : ℝ → ℝ)
    (hpp : p=ᵐ[pathMeasure] q.val) (hp : Monotone p) (hb : ∀ u, p u∈Icc (0:ℝ) 1) (n : ℕ) :
    isingEntropy (lowerTrial p hp hb n) ≤ isingEntropy q := by
  apply isingEntropy_mono
  filter_upwards [lowerTrial_ae p hp hb n,hpp,ae_restrict_mem measurableSet_Ioo] with u hl hu huI
  rw [← hl,← hu]
  exact lowerGrid_le hp hb n huI.1.le

lemma patternFunctional_lowerTrial_tendsto (q : OverlapPath) (p : ℝ → ℝ)
    (hpp : p=ᵐ[pathMeasure] q.val) (hp : Monotone p) (hb : ∀ u, p u∈Icc (0:ℝ) 1)
    {f : ℝ → ℝ} (F : BoundedC2Data f) :
    Tendsto (fun n => patternFunctional f (lowerTrial p hp hb n)) atTop (𝓝 (patternFunctional f q)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht : Tendsto (fun n => F.C^2/2*((∫ u, p u ∂pathMeasure)-(∫ u, lowerGrid p n u ∂pathMeasure)))
      atTop (𝓝 0) := by
    simpa only [sub_self,mul_zero] using ((tendsto_const_nhds (x := ∫ u, p u ∂pathMeasure)).sub (lowerGrid_integral_tendsto hp hb)).const_mul (F.C^2/2)
  apply squeeze_zero (fun _ => norm_nonneg _) _ ht
  intro n
  rw [Real.norm_eq_abs,abs_sub_comm]
  exact patternFunctional_ordered_bound (lowerTrial p hp hb n) q (lowerGrid p n) p
    (lowerTrial_ae p hp hb n) hpp (lowerGrid_monotone hp n) hp (lowerGrid_mem hb n) hb
    (fun u hu => lowerGrid_le hp hb n hu.1.le) F

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

theorem gaussian_path_upper_tolerance (q : OverlapPath) {f : ℝ → ℝ}
    (F : BoundedC2Data f) (S : ℝ) (α : ℝ≥0) (hS : isingEntropy q ≤ (S:EReal))
    {ε : ℝ} (hε : 0<ε) :
    ∀ᶠ N : ℕ in atTop, expectedPressure α f N ≤ S+(α:ℝ)*patternFunctional f q+ε := by
  obtain ⟨p,hpp,hp,hb⟩ := overlapPath_representative q
  have ht := (patternFunctional_lowerTrial_tendsto q p hpp hp hb F).const_mul (α:ℝ)
  have hev := ht.eventually (gt_mem_nhds (by linarith : (α:ℝ)*patternFunctional f q <
    (α:ℝ)*patternFunctional f q+ε/2))
  obtain ⟨n,hn⟩ := hev.exists
  have H := gaussian_step_upper_tolerance (uniformCut n) (uniformCut_strict n)
    (uniformCut_zero n) (uniformCut_last n) (lowerTrial p hp hb n)
    (fun i : Fin (n+1) => (1-1/(n+1:ℕ))*p ((i.val:ℝ)/(n+1:ℕ)))
    (lowerTrial_step p hp hb n) (fun i => (lowerTrial_value_lt_one hb n _).le)
    (lowerTrial_value_lt_one hb n _) F S α ((lowerTrial_entropy_le q p hpp hp hb n).trans hS)
    (ε := ε/2) (by positivity)
  filter_upwards [H] with N hN
  linarith

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

def boundedC2DataOfSmoothCompact {f : ℝ → ℝ} (hf : ContDiff ℝ ⊤ f)
    (hc : HasCompactSupport f) : BoundedC2Data f := by
  have hd : ContDiff ℝ ⊤ (deriv f) := ContDiff.deriv' (by simpa using hf)
  have hdd : ContDiff ℝ ⊤ (deriv (deriv f)) := ContDiff.deriv' (by simpa using hd)
  let K := Classical.choose (hc.exists_bound_of_continuous hf.continuous)
  let C := Classical.choose (hc.deriv.exists_bound_of_continuous hd.continuous)
  let D := Classical.choose (hc.deriv.deriv.exists_bound_of_continuous hdd.continuous)
  refine ⟨deriv f,deriv (deriv f),K,C,D,hf.continuous.measurable,hd.continuous.measurable,
    hdd.continuous.measurable,?_,?_,?_,?_,?_⟩
  · simpa only [Real.norm_eq_abs] using Classical.choose_spec (hc.exists_bound_of_continuous hf.continuous)
  · simpa only [Real.norm_eq_abs] using Classical.choose_spec (hc.deriv.exists_bound_of_continuous hd.continuous)
  · simpa only [Real.norm_eq_abs] using Classical.choose_spec (hc.deriv.deriv.exists_bound_of_continuous hdd.continuous)
  · intro x
    exact (hf.differentiable (by simp) x).hasDerivAt
  · intro x
    exact (hd.differentiable (by simp) x).hasDerivAt

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma pressure_eq_finiteLogIntegral (α : ℝ) (f : ℝ → ℝ) (N : ℕ)
    (g : Patterns (patternCount α N) N) :
    pressure α f N g = finiteLogIntegral (spinLaw N)
      (fun x => ∑ a : Fin (patternCount α N), f (projection g a x))/(N:ℝ) := by
  simp only [pressure,partitionFunction,finiteLogIntegral,spinLaw_integral]

lemma pressure_abs_bound {α : ℝ} (hα : 0≤α) {f : ℝ → ℝ} {K : ℝ}
    (hK : 0≤K) (hf : ∀ x, |f x|≤K) (N : ℕ) (g : Patterns (patternCount α N) N) :
    |pressure α f N g|≤α*K := by
  rw [pressure_eq_finiteLogIntegral,abs_div,abs_of_nonneg (show (0:ℝ)≤N from Nat.cast_nonneg N)]
  by_cases hN : N=0
  · simp [hN,mul_nonneg hα hK]
  have hn : (0:ℝ)<N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hb : ∀ x : Spin N, |∑ a : Fin (patternCount α N), f (projection g a x)| ≤ (patternCount α N:ℝ)*K := by
    intro x
    calc
      _ ≤ ∑ a : Fin (patternCount α N), |f (projection g a x)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : Fin (patternCount α N), K := Finset.sum_le_sum (fun _ _ => hf _)
      _ = _ := by simp
  have H := logMean_bounds (spinLaw N) (show Measurable (fun x : Spin N =>
    ∑ a : Fin (patternCount α N), f (projection g a x)) from measurable_of_countable _) (b:=1) (by norm_num) hb
  rw [finiteLogIntegral_eq_logMean]
  apply (div_le_iff₀ hn).mpr
  calc
    _ ≤ (patternCount α N:ℝ)*K := H
    _ ≤ (α*(N:ℝ))*K := mul_le_mul_of_nonneg_right (Nat.floor_le (mul_nonneg hα hn.le)) hK
    _ = _ := by ring

lemma expectedPressure_abs_bound {α : ℝ} (hα : 0≤α) {f : ℝ → ℝ} (hm : Measurable f)
    {K : ℝ} (hK : 0≤K) (hf : ∀ x, |f x|≤K) (N : ℕ) :
    |expectedPressure α f N|≤α*K := by
  let : IsProbabilityMeasure (gaussianPatterns (patternCount α N) N) := by
    unfold gaussianPatterns
    infer_instance
  exact abs_integral_le_const_of_bound (measurable_pressure α hm N) (pressure_abs_bound hα hK hf N)

end IsingPerceptron

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma isingEntropy_ne_bot (q : OverlapPath) : isingEntropy q ≠ ⊥ := by
  let h := chainFieldStep 0 (uniformCut 0) (uniformCut_strict 0) (uniformCut_zero 0)
    (uniformCut_last 0) (fun _ => 0) monotone_const le_rfl
  have H : ((fieldRecursion h+(∫ u, stepFunction h u*q.val u ∂pathMeasure)/2:ℝ):EReal)
      ≤ isingEntropy q := le_iSup (fun h : FieldStep =>
        ((fieldRecursion h+(∫ u, stepFunction h u*q.val u ∂pathMeasure)/2:ℝ):EReal)) h
  exact ne_of_gt (lt_of_lt_of_le (EReal.bot_lt_coe _) H)

lemma gaussian_upper_bound_C2 {α : ℝ} (hα : 0<α) {f : ℝ → ℝ}
    (F : BoundedC2Data f) (q : OverlapPath) :
    ((limsup (expectedPressure α f) atTop : ℝ):EReal) ≤
      (α*patternFunctional f q:ℝ)+isingEntropy q := by
  by_cases htop : isingEntropy q=⊤
  · simp only [htop,EReal.coe_add_top,le_top]
  have hreal := EReal.coe_toReal htop (isingEntropy_ne_bot q)
  have hb := expectedPressure_abs_bound hα.le F.mf ((abs_nonneg (f 0)).trans (F.bf 0)) F.bf
  have hc : IsCoboundedUnder (· ≤ ·) atTop (expectedPressure α f) :=
    isCoboundedUnder_le_of_le atTop (fun N => (abs_le.mp (hb N)).1)
  have H : limsup (expectedPressure α f) atTop ≤ (isingEntropy q).toReal+α*patternFunctional f q := by
    apply le_of_forall_pos_le_add
    intro ε hε
    apply limsup_le_of_le hc
    exact gaussian_path_upper_tolerance q F (isingEntropy q).toReal ⟨α,hα.le⟩ hreal.ge hε
  calc
    _ ≤ (((isingEntropy q).toReal+α*patternFunctional f q:ℝ):EReal) := EReal.coe_le_coe H
    _ = _ := by rw [EReal.coe_add,hreal]; ac_rfl

theorem gaussian_upper_bound {α : ℝ} (hα : 0<α) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hc : HasCompactSupport f) (q : OverlapPath) :
    ((limsup (expectedPressure α f) atTop : ℝ):EReal) ≤
      (α*patternFunctional f q:ℝ)+isingEntropy q :=
  gaussian_upper_bound_C2 hα (boundedC2DataOfSmoothCompact hf hc) q

theorem gaussian_upper_variational {α : ℝ} (hα : 0<α) {f : ℝ → ℝ}
    (hf : ContDiff ℝ ⊤ f) (hc : HasCompactSupport f) :
    ((limsup (expectedPressure α f) atTop : ℝ):EReal) ≤ variationalValue α f := by
  exact le_iInf (gaussian_upper_bound hα hf hc)

end IsingPerceptron

namespace IsingPerceptron.Main
open MeasureTheory ProbabilityTheory Filter Set Real
open scoped BigOperators NNReal ENNReal Topology Classical
variable {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]

lemma bounded_integrable (μ : Measure A) [IsFiniteMeasure μ] {F : A → ℝ}
    (hF : Measurable F) {C : ℝ} (hC : ∀x, |F x|≤C) : Integrable F μ :=
  Integrable.of_bound hF.aestronglyMeasurable C (ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs] using hC x)

lemma bounded_memLp (μ : Measure A) [IsFiniteMeasure μ] {F : A → ℝ}
    (hF : Measurable F) {C : ℝ} (hC : ∀x, |F x|≤C) : MemLp F 2 μ := by
  apply MemLp.of_bound hF.aestronglyMeasurable C
  exact ae_of_all _ fun x => show ‖F x‖≤C by simpa only [Real.norm_eq_abs] using hC x

lemma bounded_squared (μ : Measure A) [IsFiniteMeasure μ] {F : A → ℝ}
    (hF : Measurable F) {C : ℝ} (hC : ∀x, |F x|≤C) :
    Integrable (fun x => F x ^ 2) μ := (bounded_memLp μ hF hC).integrable_sq

lemma bounded_mean (μ : Measure A) [IsProbabilityMeasure μ] {F : A → ℝ}
    {C : ℝ} (hC : ∀x, |F x|≤C) : |∫x,F x ∂μ|≤C := by
  simpa using norm_integral_le_of_norm_le_const
    (μ:=μ) (f:=F) (ae_of_all _ fun x => show ‖F x‖≤C by
      simpa only [Real.norm_eq_abs] using hC x)

lemma variance_prod_le [Nonempty A] (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {F : A × B → ℝ}
    (hF : Measurable F) {M c : ℝ} (hM : ∀p,|F p|≤M)
    (hc : ∀x x' y,|F (x,y)-F (x',y)|≤c) :
    variance F (μ.prod ν) ≤ c^2 + variance (fun y => ∫x,F (x,y) ∂μ) ν := by
  let G : B → ℝ := fun y => ∫x,F (x,y) ∂μ
  have hmG : Measurable G := hF.stronglyMeasurable.integral_prod_left'.measurable
  have hbG (y) : |G y|≤M := bounded_mean μ (fun x => hM (x,y))
  have hiG := bounded_integrable ν hmG hbG
  have hiG2 := bounded_squared ν hmG hbG
  have hiF := bounded_integrable (μ.prod ν) hF hM
  have hiF2 := bounded_squared (μ.prod ν) hF hM
  have hmean : ∫p,F p ∂μ.prod ν = ∫y,G y ∂ν := integral_prod_symm F hiF
  have hsquare : ∫p,F p^2 ∂μ.prod ν = ∫y,∫x,F (x,y)^2 ∂μ ∂ν :=
    integral_prod_symm _ hiF2
  have hslice (y : B) : (∫x,F (x,y)^2 ∂μ) ≤ c^2 + G y ^2 := by
    let x₀ : A := Classical.arbitrary A
    have hm : Measurable (fun x => F (x,y)) := hF.comp (measurable_id.prodMk measurable_const)
    have hb : ∀ᵐ x ∂μ,F (x,y)∈Icc (F (x₀,y)-c) (F (x₀,y)+c) :=
      ae_of_all _ fun x => by have h := abs_le.mp (hc x x₀ y); constructor <;> linarith
    have hv := variance_le_sq_of_bounded hb hm.aemeasurable
    rw [variance_eq_sub (bounded_memLp μ hm (fun x => hM (x,y)))] at hv
    simp only [Pi.pow_apply] at hv
    dsimp [G]
    nlinarith
  have hiInner : Integrable (fun y => ∫x,F (x,y)^2 ∂μ) ν := hiF2.integral_prod_right
  have hbound := integral_mono hiInner ((integrable_const (c^2)).add hiG2) hslice
  simp only [Pi.add_apply] at hbound
  rw [integral_add (integrable_const _) hiG2,integral_const] at hbound
  rw [variance_eq_sub (bounded_memLp (μ.prod ν) hF hM),
    variance_eq_sub (bounded_memLp ν hmG hbG)]
  simp only [Pi.pow_apply]
  rw [hmean,hsquare]
  simp only [Measure.real,measure_univ,ENNReal.toReal_one,one_smul] at hbound
  linarith

theorem variance_pi_bounded_differences [Nonempty A] {n : ℕ}
    (μ : Fin n → Measure A) [∀i,IsProbabilityMeasure (μ i)]
    {F : (Fin n → A) → ℝ} (hF : Measurable F) {M : ℝ}
    (hM : ∀x,|F x|≤M) (c : Fin n → ℝ)
    (hc : ∀i x y,(∀j,j≠i → x j=y j) → |F x-F y|≤c i) :
    variance F (Measure.pi μ) ≤ ∑i,c i ^2 := by
  induction n with
  | zero =>
    have hconst : F = fun _ => F (Fin.elim0) := by
      funext x
      congr 1
      exact Subsingleton.elim _ _
    rw [hconst]
    rw [variance_eq_integral measurable_const.aemeasurable]
    simp
  | succ n ih =>
    let ν : Measure (Fin n → A) := Measure.pi (fun i => μ i.succ)
    let H : A × (Fin n → A) → ℝ := fun p => F (Fin.cons p.1 p.2)
    have hmH : Measurable H := by
      apply hF.comp
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact measurable_fst
      · exact (measurable_pi_apply j).comp measurable_snd
    have hbH (p) : |H p|≤M := hM _
    have hmp := (measurePreserving_piFinSuccAbove μ 0).symm
    have he (p : A × (Fin n → A)) :
        (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => A) 0).symm p =
          Fin.cons p.1 p.2 := by
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply,Fin.insertNthEquiv]
    have hvar : variance F (Measure.pi μ) = variance H ((μ 0).prod ν) := by
      rw [← hmp.map_eq,variance_map hF.aemeasurable hmp.measurable.aemeasurable]
      congr 1
      funext p
      exact congrArg F (he p)
    have hcH : ∀x x' y,|H (x,y)-H (x',y)|≤c 0 := by
      intro x x' y
      apply hc 0
      intro j
      refine Fin.cases ?_ (fun i => ?_) j
      · intro hj; exact False.elim (hj rfl)
      · intro _; rfl
    let G : (Fin n → A) → ℝ := fun y => ∫x,H (x,y) ∂μ 0
    have hmG : Measurable G := hmH.stronglyMeasurable.integral_prod_left'.measurable
    have hbG (y) : |G y|≤M := bounded_mean (μ 0) (fun x => hbH (x,y))
    have hcG : ∀i x y,(∀j,j≠i → x j=y j) → |G x-G y|≤c i.succ := by
      intro i x y hxy
      have hix : Integrable (fun a => H (a,x)) (μ 0) := bounded_integrable (μ 0)
        (hmH.comp (measurable_id.prodMk measurable_const)) (fun a => hbH (a,x))
      have hiy : Integrable (fun a => H (a,y)) (μ 0) := bounded_integrable (μ 0)
        (hmH.comp (measurable_id.prodMk measurable_const)) (fun a => hbH (a,y))
      dsimp [G]
      rw [← integral_sub hix hiy]
      apply bounded_mean
      intro a
      apply hc i.succ
      intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · intro _; rfl
      · intro hj; exact hxy k (fun h => hj (congrArg Fin.succ h))
    have htail := ih (fun i : Fin n => μ i.succ) hmG hbG (fun i => c i.succ) hcG
    rw [hvar,Fin.sum_univ_succ]
    exact (variance_prod_le (μ 0) ν hmH hbH hcH).trans (add_le_add_right htail _)

end IsingPerceptron.Main

end

end OAI
