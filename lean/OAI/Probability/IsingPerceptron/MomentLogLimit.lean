import Mathlib
import OAI.Probability.IsingPerceptron.CascadeFreshMoments
import OAI.Probability.IsingPerceptron.FieldChain

namespace OAI

/-! Moment Log Limit. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology Polynomial
namespace IsingPerceptron

lemma integrable_pow_of_pos_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z)
    {a b : ℝ} (ha : 0 < a) (hb : ∀ ω, Z ω ∈ Icc a b) (k : ℕ) :
    Integrable (fun ω => Z ω ^ k) P := by
  apply Integrable.of_bound (hZ.pow_const k).aestronglyMeasurable (b^k)
  exact ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs,abs_pow,abs_of_nonneg (ha.le.trans (hb ω).1)]
    exact pow_le_pow_left₀ (ha.le.trans (hb ω).1) (hb ω).2 _)

lemma integral_polynomial_of_pos_bounds {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {Z : Ω → ℝ} (hZ : Measurable Z)
    {a b : ℝ} (ha : 0 < a) (hb : ∀ ω, Z ω ∈ Icc a b) (p : ℝ[X]) :
    (∫ ω, p.eval (Z ω) ∂P) = ∑ k ∈ p.support, p.coeff k * ∫ ω, Z ω ^ k ∂P := by
  simp only [Polynomial.eval_eq_sum,Polynomial.sum]
  rw [integral_finsetSum _ (fun k _ => (integrable_pow_of_pos_bounds hZ ha hb k).const_mul _)]
  simp only [integral_const_mul]

lemma integral_log_polynomial_error {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω')
      [IsProbabilityMeasure P'] (Z' : Ω' → ℝ) (hZ' : Measurable Z')
      {a b : ℝ} (hc : ContinuousOn Real.log (Icc a b))
    (hb' : ∀ ω, Z' ω ∈ Icc a b) (p : ℝ[X]) {ε : ℝ} (_hε : 0 < ε)
      (hp : ∀ x ∈ Icc a b, |p.eval x - Real.log x| < ε) :
      |(∫ ω, p.eval (Z' ω) ∂P') - ∫ ω, Real.log (Z' ω) ∂P'| ≤ ε := by
    have hip : Integrable (fun ω => p.eval (Z' ω)) P' := by
      have hpc : ContinuousOn (fun x => p.eval x) (Icc a b) := p.continuous.continuousOn
      obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hpc
      exact Integrable.of_bound (p.continuous.measurable.comp hZ').aestronglyMeasurable C
        (ae_of_all _ (fun ω => hC _ (hb' ω)))
    have hil : Integrable (fun ω => Real.log (Z' ω)) P' := by
      obtain ⟨C,hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
      exact Integrable.of_bound (hZ'.log).aestronglyMeasurable C
        (ae_of_all _ (fun ω => hC _ (hb' ω)))
    rw [← integral_sub hip hil,← Real.norm_eq_abs]
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := P') (C := ε) (ae_of_all _ (fun ω => by
        simpa only [Real.norm_eq_abs] using (hp _ (hb' ω)).le))

 

theorem tendsto_integral_log_of_moments
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] {Ωlim : Type*} [MeasurableSpace Ωlim]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Q : Measure Ωlim) [IsProbabilityMeasure Q]
    (Z : ∀ n, Ω n → ℝ) (W : Ωlim → ℝ)
    (hZ : ∀ n, Measurable (Z n)) (hW : Measurable W)
    {a b : ℝ} (ha : 0 < a) (_hb : a ≤ b)
    (hbound : ∀ n ω, Z n ω ∈ Icc a b) (hwbound : ∀ ω, W ω ∈ Icc a b)
    (hmoment : ∀ k : ℕ, Tendsto (fun n => ∫ ω, Z n ω ^ k ∂P n) atTop
      (𝓝 (∫ ω, W ω ^ k ∂Q))) :
    Tendsto (fun n => ∫ ω, Real.log (Z n ω) ∂P n) atTop
      (𝓝 (∫ ω, Real.log (W ω) ∂Q)) := by
  have hc : ContinuousOn Real.log (Icc a b) := Real.continuousOn_log.mono
    (fun x hx => ne_of_gt (ha.trans_le hx.1))
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨p,hp⟩ := exists_polynomial_near_of_continuousOn a b Real.log hc (ε/3) (by positivity)
  have ht : Tendsto (fun n => ∫ ω, p.eval (Z n ω) ∂P n) atTop
      (𝓝 (∫ ω, p.eval (W ω) ∂Q)) := by
    simp_rw [integral_polynomial_of_pos_bounds (hZ _) ha (hbound _) p,
      integral_polynomial_of_pos_bounds hW ha hwbound p]
    exact tendsto_finsetSum _ (fun k _ => tendsto_const_nhds.mul (hmoment k))
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp ht (ε/3) (by positivity)
  use N
  intro n hn
  rw [Real.dist_eq]
  have h1 := integral_log_polynomial_error (P n) (Z n) (hZ n) hc (hbound n) p (by positivity : 0 < ε/3) hp
  have h2 := integral_log_polynomial_error Q W hW hc hwbound p (by positivity : 0 < ε/3) hp
  have h3 := hN n hn
  rw [Real.dist_eq] at h3
  have htri := abs_add_three
    ((∫ ω, Real.log (Z n ω) ∂P n) - ∫ ω, p.eval (Z n ω) ∂P n)
    ((∫ ω, p.eval (Z n ω) ∂P n) - ∫ ω, p.eval (W ω) ∂Q)
    ((∫ ω, p.eval (W ω) ∂Q) - ∫ ω, Real.log (W ω) ∂Q)
  rw [abs_sub_comm] at h1
  have he : ((∫ ω, Real.log (Z n ω) ∂P n) - ∫ ω, p.eval (Z n ω) ∂P n) +
      ((∫ ω, p.eval (Z n ω) ∂P n) - ∫ ω, p.eval (W ω) ∂Q) +
      ((∫ ω, p.eval (W ω) ∂Q) - ∫ ω, Real.log (W ω) ∂Q) =
      (∫ ω, Real.log (Z n ω) ∂P n) - ∫ ω, Real.log (W ω) ∂Q := by ring
  rw [he] at htri
  linarith

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal BoundedContinuousFunction
namespace IsingPerceptron

 

theorem exists_positive_factor_of_moments
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Z : ∀ n, Ω n → ℝ) (hZ : ∀ n, Measurable (Z n))
    {a b : ℝ} (hab : a ≤ b) (hb : ∀ n ω, Z n ω ∈ Icc a b)
    (L : ℕ → ℝ) (hL : ∀ k, Tendsto (fun n => ∫ ω, Z n ω^k ∂P n) atTop (𝓝 (L k))) :
    ∃ Q : ProbabilityMeasure (Icc a b), ∀ k, (∫ x, (x:ℝ)^k ∂(Q : Measure (Icc a b))) = L k := by
  let : Nonempty (Icc a b) := ⟨⟨a,le_rfl,hab⟩⟩
  let F (n : ℕ) : Ω n → Icc a b := fun ω => ⟨Z n ω,hb n ω⟩
  have hF (n) : Measurable (F n) := (hZ n).subtype_mk
  let M (n : ℕ) : ProbabilityMeasure (Icc a b) := ⟨(P n).map (F n),inferInstance⟩
  obtain ⟨Q,_,ns,hns,hQ⟩ := isSeqCompact_univ.subseq_of_frequently_in
    (x := M) (Filter.Frequently.of_forall (fun _ => Set.mem_univ _))
  refine ⟨Q,?_⟩
  intro k
  have hT := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hQ)
    (BoundedContinuousFunction.mkOfCompact ⟨fun x : Icc a b => (x:ℝ)^k,by fun_prop⟩)
  have he (n) : (∫ x : Icc a b, (x:ℝ)^k ∂(M n : Measure (Icc a b))) = ∫ ω, Z n ω^k ∂P n := by
    exact integral_map (hF n).aemeasurable (by fun_prop : Continuous (fun x : Icc a b => (x:ℝ)^k)).aestronglyMeasurable
  change Tendsto (fun n => ∫ x : Icc a b, (x:ℝ)^k ∂(M (ns n) : Measure (Icc a b))) atTop
    (𝓝 (∫ x : Icc a b, (x:ℝ)^k ∂(Q : Measure (Icc a b)))) at hT
  simp only [he] at hT
  exact tendsto_nhds_unique hT ((hL k).comp hns.tendsto_atTop)

lemma factor_log_converges_of_moments
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Z : ∀ n, Ω n → ℝ) (hZ : ∀ n, Measurable (Z n))
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : ∀ n ω, Z n ω ∈ Icc a b)
    (L : ℕ → ℝ) (hL : ∀ k, Tendsto (fun n => ∫ ω, Z n ω^k ∂P n) atTop (𝓝 (L k))) :
    ∃ Q : ProbabilityMeasure (Icc a b),
      (∀ k, (∫ x, (x:ℝ)^k ∂(Q : Measure (Icc a b))) = L k) ∧
      Tendsto (fun n => ∫ ω, Real.log (Z n ω) ∂P n) atTop
        (𝓝 (∫ x, Real.log (x:ℝ) ∂(Q : Measure (Icc a b)))) := by
  obtain ⟨Q,hQ⟩ := exists_positive_factor_of_moments P Z hZ hab hb L hL
  refine ⟨Q,hQ,?_⟩
  exact tendsto_integral_log_of_moments P (Q : Measure (Icc a b)) Z (fun x => (x:ℝ)) hZ
    measurable_subtype_coe ha hab hb (fun x => x.property) (fun k => by rw [hQ k]; exact hL k)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

 

theorem patternFunctional_factor_law (q : OverlapPath) (p : ℝ → ℝ)
    (hpq : p =ᵐ[pathMeasure] q.val) (hp : Monotone p) (hb : ∀ u, p u ∈ Icc (0:ℝ) 1)
    (μ : ProbabilityMeasure JointArray) (hGG : HasGhirlandaGuerra spinArray (μ : Measure JointArray))
    (hG : ∀ᵐ x ∂(μ : Measure JointArray), GramDiagonal 1 (spinArray x))
    (hU : ∀ᵐ x ∂(μ : Measure JointArray), IsUltrametricArray (spinArray x))
    (hpair : (μ : Measure JointArray).map (fun x => spinArray x 0 1) = unitUniform.map p)
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    ∃ Q : ProbabilityMeasure (Icc (Real.exp (-K)) (Real.exp K)),
      (∀ m, (∫ x, (x:ℝ)^m ∂(Q : Measure (Icc (Real.exp (-K)) (Real.exp K)))) =
        ∫ x, gaussianMoment m f (fun i j => spinArray x i j) ∂(μ : Measure JointArray)) ∧
      (∫ x, Real.log (x:ℝ) ∂(Q : Measure (Icc (Real.exp (-K)) (Real.exp K)))) = patternFunctional f q ∧
      Tendsto (uniformPattern f q) atTop (𝓝 (patternFunctional f q)) := by
  have hK0 : 0 ≤ K := (abs_nonneg (f 0)).trans (hK 0)
  have he : Real.exp (-K) ≤ Real.exp K := Real.exp_le_exp.mpr (by linarith)
  obtain ⟨Q,hQ,hT⟩ := factor_log_converges_of_moments
    (fun n => (labeledCascadeLaw n (uniformExponent n) : Measure (LabeledTree n)).prod gaussianCoordinates)
    (fun n => cascadeFreshFactor n (uniformCellAverage p n) f)
    (fun n => measurable_cascadeFreshFactor n _ hf.measurable) (Real.exp_pos _) he
    (fun n x => cascadeFreshFactor_bound n _ hf.measurable hK x)
    (fun m => ∫ x, gaussianMoment m f (fun i j => spinArray x i j) ∂(μ : Measure JointArray))
    (cascadeFresh_moments_tendsto hp hb μ hGG hG hU hpair hf hK)
  have hv : Tendsto (uniformPattern f q) atTop (𝓝 (∫ x, Real.log (x:ℝ) ∂(Q : Measure (Icc (Real.exp (-K)) (Real.exp K))))) := by
    simpa only [cascadeFresh_uniformPattern q p hpq _ hf.measurable hK] using hT
  have heq : patternFunctional f q = ∫ x, Real.log (x:ℝ) ∂(Q : Measure (Icc (Real.exp (-K)) (Real.exp K))) := hv.limUnder_eq
  exact ⟨Q,hQ,heq.symm,by simpa only [heq] using hv⟩

 

theorem freshLog_tendsto_patternFunctional
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (Z : ∀ n, Ω n → ℝ) (hZ : ∀ n, Measurable (Z n))
    (q : OverlapPath) (p : ℝ → ℝ) (hpq : p =ᵐ[pathMeasure] q.val)
    (hp : Monotone p) (hb : ∀ u, p u ∈ Icc (0:ℝ) 1)
    (μ : ProbabilityMeasure JointArray) (hGG : HasGhirlandaGuerra spinArray (μ : Measure JointArray))
    (hG : ∀ᵐ x ∂(μ : Measure JointArray), GramDiagonal 1 (spinArray x))
    (hU : ∀ᵐ x ∂(μ : Measure JointArray), IsUltrametricArray (spinArray x))
    (hpair : (μ : Measure JointArray).map (fun x => spinArray x 0 1) = unitUniform.map p)
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K)
    (hbound : ∀ n x, Z n x ∈ Icc (Real.exp (-K)) (Real.exp K))
    (hMom : ∀ m, Tendsto (fun n => ∫ x, (Z n x)^m ∂P n) atTop
      (𝓝 (∫ x, gaussianMoment m f (fun i j => spinArray x i j) ∂(μ : Measure JointArray)))) :
    Tendsto (fun n => ∫ x, Real.log (Z n x) ∂P n) atTop (𝓝 (patternFunctional f q)) := by
  obtain ⟨Q,hQ,hlog,_⟩ := patternFunctional_factor_law q p hpq hp hb μ hGG hG hU hpair hf hK
  rw [← hlog]
  have hK0 : 0 ≤ K := (abs_nonneg (f 0)).trans (hK 0)
  apply tendsto_integral_log_of_moments P (Q : Measure (Icc (Real.exp (-K)) (Real.exp K))) Z (fun x => (x:ℝ)) hZ measurable_subtype_coe
    (Real.exp_pos _) (Real.exp_le_exp.mpr (by linarith)) hbound (fun x => x.property)
  intro m
  rw [hQ m]
  exact hMom m

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

 

theorem uniformPattern_tendsto (q : OverlapPath) {f : ℝ → ℝ}
    (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    Tendsto (uniformPattern f q) atTop (𝓝 (patternFunctional f q)) := by
  obtain ⟨p,hpq,hp,hb⟩ := overlapPath_representative q
  obtain ⟨μ,ns,hns,hL⟩ := jointArrayLaw_subsequence
    (fun k => cascadeCompactLaw k (uniformExponent k) (uniformCellAverage p k))
  have hL' : Tendsto (fun k => cascadeCompactLaw (ns k) (uniformExponent (ns k))
      (uniformCellAverage p (ns k))) atTop (𝓝 μ) := hL
  have hgeom := cascadeCompact_limit_geometry
    (fun k => uniformCellAverage_monotone hp hb (ns k))
    (fun k => (uniformCellAverage_mem hp hb (ns k) 0).1)
    (fun k => (uniformCellAverage_mem hp hb (ns k) (ns k)).2) hL'
  have hGG : HasGhirlandaGuerra spinArray (μ : Measure JointArray) :=
    (cascadeCompact_limit_GG (fun k => uniformExponent_cascade (ns k)) hL').real_map
      (f := fun x => x.1.1) (by fun_prop)
  have hpair := cascadeCompact_limit_pairLaw hp hb hns.tendsto_atTop hL'
  obtain ⟨Q,hQ,hlog,hlim⟩ := patternFunctional_factor_law q p hpq hp hb μ hGG
    hgeom.1 hgeom.2 hpair hf hK
  exact hlim

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma uniformNodal_congr (a b : ℕ → ℝ) (n : ℕ) (h : ∀ i ≤ n, a i=b i) :
    uniformNodal a n=uniformNodal b n := by
  funext j
  unfold uniformNodal
  split
  · rfl
  · split
    · exact h (j-1) (by omega)
    · rfl

lemma uniformNodal_tail_weights {p q : ℝ → ℝ} (hp : Monotone p) (hq : Monotone q)
    (n : ℕ) (ht : ∀ s ∈ Icc (0:ℝ) 1,
      (∫ u in Ioo s 1, q u) ≤ ∫ u in Ioo s 1, p u) :
    FinTailNonneg (fun i : Fin (n+2) =>
      (nextCoefficient (uniformCoefficient n) i-uniformCoefficient n i)*
      (uniformNodal (uniformCellAverage p n) n (i.val+1)-
        uniformNodal (uniformCellAverage q n) n (i.val+1))) := by
  intro j
  rw [Fin.sum_univ_castSucc]
  simp only [uniformWeight_last,ite_self,add_zero]
  simp only [Fin.le_def,Fin.val_castSucc]
  have hw (i : Fin (n+1)) := uniformWeight_castSucc (uniformCellAverage q n) (uniformCellAverage p n) n i
  simp only [Fin.val_castSucc] at hw
  simp_rw [hw]
  have he (i : Fin (n+1)) :
      (if j.val ≤ i.val then (1/(n+1:ℕ))*(uniformCellAverage p n i.val-uniformCellAverage q n i.val) else 0) =
      (1/(n+1:ℕ))*(if j.val ≤ i.val then uniformCellAverage p n i.val-uniformCellAverage q n i.val else 0) := by
    split <;> simp
  simp_rw [he]
  rw [← Finset.mul_sum]
  apply mul_nonneg (by positivity)
  apply uniformCellAverage_tail_difference hp hq n j.val (by omega)
  apply ht
  constructor
  · positivity
  · exact (div_le_one (by positivity : (0:ℝ) < (n+1:ℕ))).mpr (by exact_mod_cast Nat.le_of_lt_succ j.isLt)

lemma uniformPattern_tail_comparison (p q : OverlapPath)
    (p' q' : ℝ → ℝ) (hpq : p' =ᵐ[pathMeasure] p.val) (hqq : q' =ᵐ[pathMeasure] q.val)
    (hp : Monotone p') (hq : Monotone q')
    (hpb : ∀ u, p' u ∈ Icc (0:ℝ) 1) (hqb : ∀ u, q' u ∈ Icc (0:ℝ) 1)
    (ht : ∀ s ∈ Icc (0:ℝ) 1, (∫ u in Ioo s 1, q' u) ≤ ∫ u in Ioo s 1, p' u)
    {f : ℝ → ℝ} (F : BoundedC2Data f) (n : ℕ) :
    uniformPattern f p n ≤ uniformPattern f q n := by
  rw [uniformPattern_eq_nodal,uniformPattern_eq_nodal]
  have hpn := uniformNodal_congr (uniformCellAverage p' n) (cellAverage p (n+1)) n
    (uniformCellAverage_eq_cellAverage p p' hpq n)
  have hqn := uniformNodal_congr (uniformCellAverage q' n) (cellAverage q (n+1)) n
    (uniformCellAverage_eq_cellAverage q q' hqq n)
  rw [← hpn,← hqn]
  exact nodalGaussianFold_antitone _ _ _
    (uniformNodal_increasing n (uniformCellAverage_monotone hq hqb n)
      (uniformCellAverage_mem hq hqb n))
    (uniformNodal_increasing n (uniformCellAverage_monotone hp hpb n)
      (uniformCellAverage_mem hp hpb n))
    (uniformCoefficient_nonneg n)
    (by simp only [uniformNodal_zero]) (by simp only [uniformNodal_last])
    (uniformNodal_tail_weights hp hq n ht) F 0

lemma tail_integral_representative (q : OverlapPath) {p : ℝ → ℝ}
    (hp : p =ᵐ[pathMeasure] q.val) {s : ℝ} (hs : 0 ≤ s) :
    (∫ u in Ioo s 1, p u) = ∫ u in Ioo s 1, q.val u ∂pathMeasure := by
  have hm : pathMeasure.restrict (Ioo s 1)=volume.restrict (Ioo s 1) := by
    rw [pathMeasure,Measure.restrict_restrict measurableSet_Ioo,inter_eq_left.mpr]
    intro u hu
    exact ⟨hs.trans_lt hu.1,hu.2⟩
  rw [← hm]
  exact integral_congr_ae hp.restrict

 

theorem patternFunctional_tail_order {f : ℝ → ℝ} (F : BoundedC2Data f)
    (p q : OverlapPath)
    (ht : ∀ s ∈ Icc (0:ℝ) 1,
      (∫ u in Ioo s 1, q.val u ∂pathMeasure) ≤ ∫ u in Ioo s 1, p.val u ∂pathMeasure) :
    patternFunctional f p ≤ patternFunctional f q := by
  obtain ⟨p',hpp,hp,hpb⟩ := overlapPath_representative p
  obtain ⟨q',hqq,hq,hqb⟩ := overlapPath_representative q
  apply le_of_tendsto_of_tendsto (uniformPattern_tendsto p F.continuous F.bf)
    (uniformPattern_tendsto q F.continuous F.bf)
  apply Eventually.of_forall
  intro n
  apply uniformPattern_tail_comparison p q p' q' hpp hqq hp hq hpb hqb _ F n
  intro s hs
  rw [tail_integral_representative p hpp hs.1,tail_integral_representative q hqq hs.1]
  exact ht s hs

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

 

lemma monotone_tail_chord_lower {p : ℝ → ℝ} (hp : Monotone p)
    {a s b c A B T : ℝ} (has : a ≤ s) (hsb : s ≤ b)
    (hA : A ≤ ∫ u in a..1, p u) (hB : B ≤ ∫ u in b..1, p u)
    (hAT : A=T+(s-a)*c) (hTB : T=B+(b-s)*c) :
    T ≤ ∫ u in s..1, p u := by
  by_cases hc : p s ≤ c
  · have H := intervalIntegral.integral_mono_on (μ := volume) has hp.intervalIntegrable
      (f := p) (g := fun _ => c) intervalIntegrable_const
      (fun u hu => (hp hu.2).trans hc)
    rw [intervalIntegral.integral_const,smul_eq_mul] at H
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := p) (a := a) (b := s) (c := 1) hp.intervalIntegrable hp.intervalIntegrable
    linarith
  · have H := intervalIntegral.integral_mono_on (μ := volume) hsb intervalIntegrable_const hp.intervalIntegrable
      (f := fun _ => c) (g := p) (fun u hu => (le_of_not_ge hc).trans (hp hu.1))
    rw [intervalIntegral.integral_const,smul_eq_mul] at H
    have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
      (f := p) (a := s) (b := b) (c := 1) hp.intervalIntegrable hp.intervalIntegrable
    linarith

lemma monotone_tail_of_cell {p q : ℝ → ℝ} (hp : Monotone p) (hq : Monotone q)
    {a s b c : ℝ} (has : a ≤ s) (hsb : s ≤ b)
    (hc : ∀ u ∈ Ioo a b, q u=c)
    (ha : (∫ u in a..1, q u) ≤ ∫ u in a..1, p u)
    (hb : (∫ u in b..1, q u) ≤ ∫ u in b..1, p u) :
    (∫ u in s..1, q u) ≤ ∫ u in s..1, p u := by
  have he₁ : (∫ u in a..s, q u)=(s-a)*c := by
    calc
      _ = ∫ _ in a..s, c := intervalIntegral.integral_congr_Ioo_of_le has
        (fun u hu => hc u ⟨hu.1,hu.2.trans_le hsb⟩)
      _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul]
  have he₂ : (∫ u in s..b, q u)=(b-s)*c := by
    calc
      _ = ∫ _ in s..b, c := intervalIntegral.integral_congr_Ioo_of_le hsb
        (fun u hu => hc u ⟨has.trans_lt hu.1,hu.2⟩)
      _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul]
  have h₁ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f := q) (a := a) (b := s) (c := 1) hq.intervalIntegrable hq.intervalIntegrable
  have h₂ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f := q) (a := s) (b := b) (c := 1) hq.intervalIntegrable hq.intervalIntegrable
  rw [he₁] at h₁
  rw [he₂] at h₂
  exact monotone_tail_chord_lower (c := c) hp has hsb ha hb (by linarith) (by linarith)

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma path_tail_interval (p : ℝ → ℝ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (∫ u in Ioi s, p u ∂pathMeasure) = ∫ u in s..1, p u := by
  have he : Ioi s ∩ Ioo (0:ℝ) 1=Ioo s 1 := by
    ext u
    simp only [mem_inter_iff,mem_Ioi,mem_Ioo]
    exact ⟨fun h => ⟨h.1,h.2.2⟩,fun h => ⟨h.1,hs0.trans_lt h.1,h.2⟩⟩
  rw [pathMeasure,Measure.restrict_restrict measurableSet_Ioi,he,
    intervalIntegral.integral_of_le hs1,integral_Ioc_eq_integral_Ioo]

lemma finite_partition_cell {k : ℕ} (ζ : Fin (k+1) → ℝ)
    {s : ℝ} (hs0 : ζ 0 ≤ s) (hs1 : s < ζ (Fin.last k)) :
    ∃ i : Fin k, ζ i.castSucc ≤ s ∧ s < ζ i.succ := by
  classical
  let T := Finset.univ.filter (fun i => s < ζ i)
  have hT : T.Nonempty := ⟨Fin.last k,by simp [T,hs1]⟩
  let d := T.min' hT
  have hd : s < ζ d := (Finset.mem_filter.mp (Finset.min'_mem T hT)).2
  have hd0 : 0 < d.val := by
    by_contra h
    have he : d=0 := Fin.ext (by change d.val=0; omega)
    rw [he] at hd
    linarith
  let i : Fin k := ⟨d.val-1,by have := d.isLt; omega⟩
  have he : i.succ=d := Fin.ext (by dsimp [i]; omega)
  refine ⟨i,?_,by simpa only [he] using hd⟩
  by_contra! h
  have hm : i.castSucc∈T := by simp [T,h]
  have H := Finset.min'_le T i.castSucc hm
  change d.val ≤ i.val at H
  dsimp [i] at H
  omega

lemma intervalIntegral_const_of_ae_cell {q : ℝ → ℝ} {a b x y c : ℝ}
    (hxy : x ≤ y) (hax : a ≤ x) (hyb : y ≤ b)
    (hc : q =ᵐ[volume.restrict (Ioo a b)] (fun _ => c)) :
    (∫ u in x..y, q u) = (y-x)*c := by
  calc
    _ = ∫ _ in x..y, c := by
      rw [intervalIntegral.integral_of_le hxy,intervalIntegral.integral_of_le hxy,
        integral_Ioc_eq_integral_Ioo,integral_Ioc_eq_integral_Ioo]
      apply integral_congr_ae
      exact ae_restrict_of_ae_restrict_of_subset (t := Ioo a b) (s := Ioo x y)
        (fun u hu => ⟨hax.trans_lt hu.1,hu.2.trans_le hyb⟩) hc
    _ = _ := by rw [intervalIntegral.integral_const,smul_eq_mul]

lemma monotone_tail_of_ae_cell {p q : ℝ → ℝ} (hp : Monotone p) (hq : Monotone q)
    {a s b c : ℝ} (has : a ≤ s) (hsb : s ≤ b)
    (hc : q =ᵐ[volume.restrict (Ioo a b)] (fun _ => c))
    (ha : (∫ u in a..1, q u) ≤ ∫ u in a..1, p u)
    (hb : (∫ u in b..1, q u) ≤ ∫ u in b..1, p u) :
    (∫ u in s..1, q u) ≤ ∫ u in s..1, p u := by
  have he₁ := intervalIntegral_const_of_ae_cell has le_rfl hsb hc
  have he₂ := intervalIntegral_const_of_ae_cell hsb has le_rfl hc
  have h₁ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f := q) (a := a) (b := s) (c := 1) hq.intervalIntegrable hq.intervalIntegrable
  have h₂ := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (f := q) (a := s) (b := b) (c := 1) hq.intervalIntegrable hq.intervalIntegrable
  rw [he₁] at h₁
  rw [he₂] at h₂
  exact monotone_tail_chord_lower (c := c) hp has hsb ha hb (by linarith) (by linarith)

lemma nodal_tails_imply_all_tails {n : ℕ} (ζ : Fin (n+2) → ℝ)
    (hz : StrictMono ζ) (hz0 : ζ 0=0) (hz1 : ζ (Fin.last (n+1))=1)
    (v : Fin (n+1) → ℝ) {p q : ℝ → ℝ} (hp : Monotone p) (hq : Monotone q)
    (hstep : finiteStepFunction ζ v =ᵐ[pathMeasure] q)
    (ht : ∀ j : Fin (n+1), (∑ i, if j ≤ i then chainWeight ζ i*v i else 0) ≤
      ∫ u in Ioi (ζ j.castSucc), p u ∂pathMeasure) :
    ∀ s ∈ Icc (0:ℝ) 1, (∫ u in Ioo s 1, q u) ≤ ∫ u in Ioo s 1, p u := by
  have hzbound (j) : ζ j∈Icc (0:ℝ) 1 :=
    ⟨by rw [← hz0]; exact hz.monotone (Fin.zero_le _),by rw [← hz1]; exact hz.monotone (Fin.le_last _)⟩
  have hn : ∀ j : Fin (n+2), (∫ u in ζ j..1, q u) ≤ ∫ u in ζ j..1, p u := by
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [hz1,intervalIntegral.integral_same,le_refl]
    · rw [← path_tail_interval q (hzbound i.castSucc).1 (hzbound i.castSucc).2,
        ← path_tail_interval p (hzbound i.castSucc).1 (hzbound i.castSucc).2,
        ← integral_congr_ae hstep.restrict,integral_finiteStep_tail ζ hz hz0 hz1]
      simpa only [Fin.le_def,Fin.val_castSucc,chainWeight] using ht i
  intro s hs
  by_cases he : s=1
  · simp [he]
  have hs1 : s < 1 := lt_of_le_of_ne hs.2 he
  obtain ⟨i,hia,hib⟩ := finite_partition_cell ζ (by simpa only [hz0] using hs.1) (by simpa only [hz1] using hs1)
  have hcell : q =ᵐ[volume.restrict (Ioo (ζ i.castSucc) (ζ i.succ))] (fun _ => v i) := by
    have heq : finiteStepFunction ζ v =ᵐ[volume.restrict (Ioo (ζ i.castSucc) (ζ i.succ))] q :=
      ae_restrict_of_ae_restrict_of_subset (t := Ioo (0:ℝ) 1)
        (s := Ioo (ζ i.castSucc) (ζ i.succ)) (fun u hu =>
        ⟨(hzbound i.castSucc).1.trans_lt hu.1,hu.2.trans_le (hzbound i.succ).2⟩) hstep
    filter_upwards [heq,ae_restrict_mem measurableSet_Ioo] with u hu hu'
    exact hu.symm.trans (finiteStepFunction_on_cell hz v hu')
  have H := monotone_tail_of_ae_cell hp hq hia hib.le hcell (hn i.castSucc) (hn i.succ)
  simpa only [intervalIntegral.integral_of_le hs.2,integral_Ioc_eq_integral_Ioo] using H

end IsingPerceptron

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal Matrix
namespace IsingPerceptron

lemma overlapArrayLaw_gram {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    [Countable X] [MeasurableSingletonClass X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X)
    (hν : Measurable ν) [∀ ω, IsProbabilityMeasure (ν ω)]
    (A : X → ℕ →₀ ℝ) (κ : X → X → JointEntry)
    (hA : ∀ x y, cylinderCross (A x) (A y) = (κ x y).1.1)
    (hd : ∀ x, (κ x x).1.1 = 1) :
    ∀ᵐ x ∂(overlapArrayLaw P ν hν κ : Measure JointArray), GramDiagonal 1 (spinArray x) := by
  change ∀ᵐ x ∂(replicaLaw P ν hν).map (sampledOverlapArray κ), _
  apply (ae_map_iff (measurable_sampledOverlapArray κ).aemeasurable
    ((isClosed_gramDiagonal 1).preimage continuous_spinArray).measurableSet).mpr
  filter_upwards [] with σ
  constructor
  · intro m
    have he : (fun i j : Fin m => spinArray (sampledOverlapArray κ σ) i j) =
        (fun i j : Fin m => cylinderCross (A (σ i)) (A (σ j))) := by
      funext i j
      exact (hA (σ i) (σ j)).symm
    rw [he]
    exact cylinderCross_matrix_posSemidef (fun i : Fin m => A (σ i))
  · intro i
    exact hd (σ i)

 

theorem freshPattern_array_limit
    {Ω X : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (X n)]
    [∀ n, Countable (X n)] [∀ n, MeasurableSingletonClass (X n)]
    (P : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (P n)]
    (ν : ∀ n, Ω n → Measure (X n)) (hν : ∀ n, Measurable (ν n))
    [∀ n ω, IsProbabilityMeasure (ν n ω)]
    (A : ∀ n, X n → ℕ →₀ ℝ) (κ : ∀ n, X n → X n → JointEntry)
    (hA : ∀ n x y, cylinderCross (A n x) (A n y) = (κ n x y).1.1)
    (hd : ∀ n x, (κ n x x).1.1 = 1)
    (μ : ProbabilityMeasure JointArray)
    (hL : Tendsto (fun n => overlapArrayLaw (P n) (ν n) (hν n) (κ n)) atTop (𝓝 μ))
    (hGG : HasGhirlandaGuerra spinArray (μ : Measure JointArray))
    (q : OverlapPath)
    (hq : quantileFunction ((μ : Measure JointArray).map (fun x => spinArray x 0 1)) =ᵐ[pathMeasure] q.val)
    {f : ℝ → ℝ} (hf : Continuous f) {K : ℝ} (hK : ∀ x, |f x| ≤ K) :
    Tendsto (fun n => ∫ z : Ω n × (ℕ → ℝ), Real.log (freshPatternFactor (ν n z.1) (A n) f z.2)
      ∂(P n).prod gaussianCoordinates) atTop (𝓝 (patternFunctional f q)) := by
  have hGn (n) := overlapArrayLaw_gram (P n) (ν n) (hν n) (A n) (κ n) (hA n) (hd n)
  have hG := ae_closed_of_weak_limit hL ((isClosed_gramDiagonal 1).preimage continuous_spinArray) hGn
  have hE : ∀ e : Equiv.Perm ℕ, (μ : Measure JointArray).map (permuteJointArray e) = μ := by
    intro e
    exact jointArray_limit_reindex hL e (fun n => overlapArrayLaw_map_reindex (P n) (ν n) (hν n) (κ n) e e.injective)
  have hU := gg_ultrametric_ae continuous_spinArray.measurable
    (scalar_of_joint_exchangeable hE (fun x => x.1.1) (by fun_prop)) hGG (by norm_num : (0:ℝ) ≤ 1) hG
  have hpos := gg_pair_nonnegative_ae continuous_spinArray.measurable hGG (by norm_num : (0:ℝ) ≤ 1) hG
  let Q := (μ : Measure JointArray).map (fun x => spinArray x 0 1)
  have hm : Measurable (fun x : JointArray => spinArray x 0 1) := by unfold spinArray; fun_prop
  let : IsProbabilityMeasure Q := inferInstance
  have hs : ∀ᵐ r ∂Q, r ∈ Icc (0:ℝ) 1 := by
    apply (ae_map_iff hm.aemeasurable measurableSet_Icc).mpr
    filter_upwards [hpos] with x hx
    exact ⟨hx,(x (0,1)).1.property.2⟩
  have hqp := monotone_quantileFunction hs
  have hqb := quantileFunction_mem hs
  apply freshLog_tendsto_patternFunctional (fun n => (P n).prod gaussianCoordinates)
    (fun n z => freshPatternFactor (ν n z.1) (A n) f z.2)
    (fun n => measurable_random_freshPatternFactor (hν n) (A n) hf.measurable)
    q (quantileFunction Q) hq hqp hqb μ hGG hG hU (quantileFunction_law hs).symm hf hK
    (fun n z => freshPatternFactor_bound (ν n z.1) (A n) f hK z.2)
  intro m
  simp_rw [freshPatternFactor_array_moment (P _) (ν _) (hν _) (A _) (κ _) (hA _) hf hK m]
  exact jointArray_tendsto_gaussianMoment hL hGn hG m hf hK

end IsingPerceptron

 

 

 

open MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators Topology ENNReal NNReal
namespace IsingPerceptron

lemma prefix_next_preserving {A : Type*} [MeasurableSpace A] (P : Measure A)
    [IsProbabilityMeasure P] (m : ℕ) :
    MeasurePreserving (fun y : ℕ → A => ((fun i : Fin m => y i), y m))
      (Measure.infinitePi (fun _ : ℕ => P)) ((Measure.pi (fun _ : Fin m => P)).prod P) := by
  have hp := (Measure.measurePreserving_swap (μ := P) (ν := Measure.pi (fun _ : Fin m => P))).comp
    ((measurePreserving_piFinSuccAbove (fun _ : Fin (m+1) => P) (Fin.last m)).comp
      (infinite_prefix_preserving P (m+1)))
  convert hp using 1
  funext y
  apply Prod.ext
  · funext i
    simp [Function.comp_def,MeasurableEquiv.piFinSuccAbove,Fin.init]
  · simp [Function.comp_def,MeasurableEquiv.piFinSuccAbove,Fin.snocEquiv]

 

theorem integral_next_row_of_prefix {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    (P : Measure A) [IsProbabilityMeasure P] (Q : Measure B) [IsProbabilityMeasure Q]
    (m : ℕ) (F : (Fin m → A) × B × A → ℝ) (hF : Measurable F)
    :
    (∫ z : (ℕ → A) × B, F ((fun i => z.1 i),z.2,z.1 m)
      ∂(Measure.infinitePi (fun _ : ℕ => P)).prod Q) =
    ∫ z : ((ℕ → A) × B) × A, F ((fun i => z.1.1 i),z.1.2,z.2)
      ∂((Measure.infinitePi (fun _ : ℕ => P)).prod Q).prod P := by
  let R := Measure.pi (fun _ : Fin m => P)
  let H : ((Fin m → A) × A) × B → ℝ := fun z => F (z.1.1,z.2,z.1.2)
  have hH : Measurable H := hF.comp (by fun_prop)
  have he1 := ((prefix_next_preserving P m).prod (MeasurePreserving.id Q)).hasLaw.integral_comp
    hH.aestronglyMeasurable
  have hm : Measurable (fun z : ((Fin m → A) × B) × A => F (z.1.1,z.1.2,z.2)) := hF.comp (by fun_prop)
  have he2 := (((infinite_prefix_preserving P m).prod (MeasurePreserving.id Q)).prod
    (MeasurePreserving.id P)).hasLaw.integral_comp hm.aestronglyMeasurable
  have hs := ((measurePreserving_prodAssoc R Q P).symm MeasurableEquiv.prodAssoc).comp
    (((MeasurePreserving.id R).prod (Measure.measurePreserving_swap (μ := P) (ν := Q))).comp
      (measurePreserving_prodAssoc R P Q))
  calc
    _ = ∫ z : ((Fin m → A) × A) × B, F (z.1.1,z.2,z.1.2) ∂(R.prod P).prod Q := he1
    _ = ∫ z : ((Fin m → A) × B) × A, F (z.1.1,z.1.2,z.2) ∂(R.prod Q).prod P :=
      hs.hasLaw.integral_comp hm.aestronglyMeasurable
    _ = _ := he2.symm

end IsingPerceptron

end

end OAI
