import Mathlib
import OAI.Probability.JammingConcavity.SphericalGridDensity

namespace OAI

/-! Row Zero Refinement Closure. -/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open Set Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory Filter Set
open scoped ENNReal NNReal BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
open scoped NNReal ENNReal Topology
open scoped NNReal Topology
open Set
open Set Filter MeasureTheory
open scoped BigOperators
open scoped Topology NNReal
open scoped Topology BigOperators
open scoped ENNReal NNReal
open MeasureTheory Set
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators Classical
open Classical
open scoped ENNReal NNReal Topology BigOperators MatrixOrder
open scoped NNReal BigOperators
open MeasureTheory Metric Set
open Metric
open scoped RealInnerProductSpace
open Filter
open Finset Set
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal BigOperators Topology
open MeasureTheory ProbabilityTheory Filter Metric
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction
open scoped BigOperators Classical
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder
open scoped BigOperators RealInnerProductSpace
open scoped NNReal Topology BigOperators
open scoped NNReal BigOperators RealInnerProductSpace
open scoped ENNReal NNReal BigOperators MatrixOrder
open scoped MatrixOrder
open scoped NNReal
open scoped BigOperators NNReal
open scoped NNReal ENNReal BigOperators Topology
open scoped Topology ENNReal NNReal
open scoped Matrix.Norms.L2Operator MatrixOrder Topology NNReal ENNReal BigOperators
open scoped Topology ENNReal NNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open scoped Topology NNReal ENNReal BigOperators
open scoped BigOperators NNReal Topology
open scoped Topology NNReal ENNReal BigOperators MatrixOrder
open scoped Topology NNReal ENNReal BigOperators MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators MatrixOrder

namespace MicroscopicJamming

lemma replica_coordinate_map {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (ν : Measure Ω) [SFinite ν] (G : Kernel Ω S) [IsMarkovKernel G]
    {r : ℕ} (i : Fin r) :
    (ν ⊗ₘ replicaKernel G r).map (fun z => (z.1,z.2 i)) = ν ⊗ₘ G := by
  have he : (replicaKernel G r).map (Function.eval i) = G := by
    ext ω : 1
    rw [Kernel.map_apply _ (measurable_pi_apply i)]
    rw [replicaKernel_apply]
    change (Measure.pi (fun _ : Fin r => G ω)).map (Function.eval i) = G ω
    simp [Measure.pi_map_eval]
  calc
    _ = ν ⊗ₘ ((replicaKernel G r).map (Function.eval i)) :=
      (Measure.compProd_map (measurable_pi_apply i)).symm
    _ = _ := by rw [he]

lemma gaussianAdjunction_constant_snd {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsProbabilityMeasure μ] (r : ℕ) (C : Matrix (Fin r) (Fin r) ℝ) :
    (gaussianAdjunctionMeasure r (fun _ : A => C) μ).map Prod.snd = multivariateGaussian 0 C := by
  have hF : Measurable (gaussianAdjunctionMap r (fun _ : A => C)) := by
    exact measurable_fst.prodMk ((Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt C)).continuous.measurable.comp measurable_snd)
  unfold gaussianAdjunctionMeasure
  rw [Measure.map_map measurable_snd hF]
  change (μ.prod (stdGaussian (EuclideanSpace ℝ (Fin r)))).map
    ((Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt C)) ∘ Prod.snd) = _
  rw [←Measure.map_map (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt C)).continuous.measurable measurable_snd,
    Measure.map_snd_prod]
  simp only [measure_univ,one_smul]
  unfold multivariateGaussian
  simp

lemma rowSingleField_law (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (hm : ∀ m ∈ ms, 0 < m ∧ m < 1) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) :
    ((rowReplicaEnvironmentLaw ms d p₀) ⊗ₘ rowReplicaKernel ms Δ).map
      (rowReplicaSiteField ms.length) = gaussianReal 0 (rowReplicaDiagonal ms.length d p₀ Δ) := by
  have : IsProbabilityMeasure (rowReplicaEnvironmentLaw ms d p₀) := by
    unfold rowReplicaEnvironmentLaw
    infer_instance
  let Q := rowReplicaDiagonal ms.length d p₀ Δ
  have he := rowReplicaFields_law ms hms hm 1 d p₀ Δ
  have hc : rowFullRankCovariance 1 Q (rowCascadeProfile ms d p₀) =
      fun _ : RankArray => Matrix.diagonal (fun _ : Fin 1 => (Q:ℝ)) := by
    funext U i j
    have hij : i=j := Subsingleton.elim _ _
    subst j
    simp [rowFullRankCovariance]
  rw [hc,gaussianAdjunction_constant_snd] at he
  have hproj := congrArg (fun μ : Measure (EuclideanSpace ℝ (Fin 1)) => μ.map (fun x => x 0)) he
  have hps : (Matrix.diagonal (fun _ : Fin 1 => (Q:ℝ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun _ => Q.coe_nonneg)
  rw [(measurePreserving_eval_multivariateGaussian (μ := (0:EuclideanSpace ℝ (Fin 1))) hps).map_eq] at hproj
  rw [Measure.map_map (by fun_prop) (by
    apply (WithLp.measurable_toLp 2 _).comp
    apply Measurable.of_eval
    intro i
    exact (measurable_rowReplicaSiteField _).comp (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)))] at hproj
  have hh := congrArg (fun μ : Measure (RowReplicaEnvironment ms.length × RowReplicaSite ms.length) =>
      μ.map (rowReplicaSiteField ms.length))
    (replica_coordinate_map (rowReplicaEnvironmentLaw ms d p₀) (rowReplicaKernel ms Δ) (0:Fin 1))
  rw [Measure.map_map (measurable_rowReplicaSiteField _) (by fun_prop)] at hh
  exact hh.symm.trans (by simpa [Q,Function.comp_def,Matrix.diagonal_apply,rowReplicaKernelView] using hproj)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma rowExpAbs_gaussian_integrable {u : ℝ → ℝ} {L H : ℝ}
    (hu : RowBoundedTerminal u L H) {a : ℝ} (ha : 0 < a) (Q : ℝ≥0) :
    Integrable (fun x => Real.exp (a*|u x|)) (gaussianReal 0 Q) := by
  have hg : RowExpGrowth (fun x => Real.exp (a*|u x|)) := by
    refine ⟨Real.exp (a*|u 0|),a*L,(Real.exp_pos _).le,mul_nonneg ha.le hu.L_nonneg,fun x => ?_⟩
    rw [abs_of_pos (Real.exp_pos _),←Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left (bounded_deriv_linear hu.diff hu.slope x) ha.le
    nlinarith only [h]
  have hm : Measurable (fun x => Real.exp (a*|u x|)) := by
    exact (hu.diff.continuous.measurable.abs.const_mul a).exp
  apply (rowGaussian_integrable Q hm).mpr
  simpa only [zero_add] using hg.integrable_affine hm 0 (Real.sqrt Q)

lemma rowUniformMoments {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (Q : ℝ) (P : ℕ → RowFiniteProfile Q) :
    ∀ a : ℝ, 0 < a → ∃ C : ℝ, ∀ n,
      Integrable (fun z => Real.exp (a*|rowFullPotential (P n).ranks u z|))
        (rowReplicaEnvironmentLaw (P n).ranks (P n).increment (P n).root ⊗ₘ
          rowReplicaKernel (P n).ranks (P n).residual) ∧
      (∫ z, Real.exp (a*|rowFullPotential (P n).ranks u z|)
        ∂(rowReplicaEnvironmentLaw (P n).ranks (P n).increment (P n).root ⊗ₘ
          rowReplicaKernel (P n).ranks (P n).residual)) ≤ C := by
  intro a ha
  refine ⟨∫ x, Real.exp (a*|u x|) ∂gaussianReal 0 Q.toNNReal,fun n => ?_⟩
  have hd : rowReplicaDiagonal (P n).ranks.length (P n).increment (P n).root (P n).residual = Q.toNNReal := by
    apply NNReal.eq
    rw [Real.coe_toNNReal _ (by rw [←(P n).diagonal]; positivity)]
    exact (P n).diagonal
  have hmap := rowSingleField_law (P n).ranks (P n).ordered (P n).valid (P n).increment (P n).root (P n).residual
  rw [hd] at hmap
  have hm : Measurable (fun x => Real.exp (a*|u x|)) := (hu.diff.continuous.measurable.abs.const_mul a).exp
  constructor
  · have hi := rowExpAbs_gaussian_integrable hu ha Q.toNNReal
    rw [←hmap] at hi
    exact (integrable_map_measure hm.aestronglyMeasurable (measurable_rowReplicaSiteField _).aemeasurable).mp hi
  · have he := integral_map (μ := rowReplicaEnvironmentLaw (P n).ranks (P n).increment (P n).root ⊗ₘ rowReplicaKernel (P n).ranks (P n).residual) (measurable_rowReplicaSiteField (P n).ranks.length).aemeasurable hm.aestronglyMeasurable
    rw [hmap] at he
    exact le_of_eq he.symm
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming
lemma replica_cauchy_of_uniform_approx (f : ℕ → ℝ)
    (h : ∀ ε > 0, ∃ g : ℕ → ℝ, CauchySeq g ∧ ∀ n, |f n - g n| ≤ ε) :
    CauchySeq f := by
  rw [Metric.cauchySeq_iff]
  intro ε hε
  obtain ⟨g,hg,he⟩ := h (ε/4) (by positivity)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp hg (ε/4) (by positivity)
  refine ⟨N,fun m hm n hn => ?_⟩
  have hgmn := hN m hm n hn
  rw [Real.dist_eq] at hgmn ⊢
  calc
    |f m-f n| = |(f m-g m)+(g m-g n)+(g n-f n)| := by congr 1; ring
    _ ≤ |f m-g m|+|g m-g n|+|g n-f n| := abs_add_three _ _ _
    _ < ε := by rw [abs_sub_comm (g n)]; linarith [he m,he n]

lemma replica_integrable_of_bound {Ω : Type*} [MeasurableSpace Ω]
    {ν : Measure Ω} [IsFiniteMeasure ν] {f : Ω → ℝ} (hf : Measurable f)
    {C : ℝ} (hC : ∀ x, |f x| ≤ C) : Integrable f ν :=
  (integrable_const C).mono' hf.aestronglyMeasurable
    (Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using hC x))

lemma replica_cauchy_polynomial_moments
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (ν : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (ν n)]
    (Z W : ∀ n, Ω n → ℝ) (hZ : ∀ n, Measurable (Z n)) (hW : ∀ n, Measurable (W n))
    {M C : ℝ} (_hM : 0 ≤ M) (hC : 0 ≤ C)
    (hz : ∀ n x, |Z n x| ≤ M) (hw : ∀ n x, |W n x| ≤ C)
    (hm : ∀ k : ℕ, CauchySeq (fun n => ∫ x, W n x * (Z n x)^k ∂ν n))
    (p : Polynomial ℝ) :
    CauchySeq (fun n => ∫ x, W n x * p.eval (Z n x) ∂ν n) := by
  have hi (n k : ℕ) : Integrable (fun x => W n x * (Z n x)^k) (ν n) := by
    apply replica_integrable_of_bound (C := C*M^k) ((hW n).mul ((hZ n).pow_const k))
    intro x
    dsimp only [Pi.mul_apply]
    rw [abs_mul,abs_pow]
    exact mul_le_mul (hw n x) (pow_le_pow_left₀ (abs_nonneg _) (hz n x) k)
      (pow_nonneg (abs_nonneg _) _) hC
  choose a ha using fun k => cauchySeq_tendsto_of_complete (hm k)
  have hp (n : ℕ) : (∫ x, W n x * p.eval (Z n x) ∂ν n) =
      ∑ k ∈ Finset.range (p.natDegree+1), p.coeff k * ∫ x, W n x * (Z n x)^k ∂ν n := by
    simp_rw [Polynomial.eval_eq_sum_range,Finset.mul_sum]
    rw [integral_finsetSum _ (fun k _ => (hi n k).const_mul (p.coeff k) |>.congr
      (Eventually.of_forall fun x => by dsimp; ring))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [←integral_const_mul]
    congr 1
    ext x
    ring
  simp_rw [hp]
  exact (tendsto_finsetSum _ (fun k _ => (ha k).const_mul (p.coeff k))).cauchySeq

lemma replica_cauchy_continuous_moments
    (Ω : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)]
    (ν : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (ν n)]
    (Z W : ∀ n, Ω n → ℝ) (hZ : ∀ n, Measurable (Z n)) (hW : ∀ n, Measurable (W n))
    {M C a b : ℝ} (hM : 0 ≤ M) (hC : 0 ≤ C)
    (hz : ∀ n x, |Z n x| ≤ M) (hw : ∀ n x, |W n x| ≤ C)
    (hzI : ∀ n x, Z n x ∈ Set.Icc a b)
    (hm : ∀ k : ℕ, CauchySeq (fun n => ∫ x, W n x * (Z n x)^k ∂ν n))
    (f : ℝ → ℝ) (hf : Measurable f) (hfc : ContinuousOn f (Set.Icc a b)) :
    CauchySeq (fun n => ∫ x, W n x * f (Z n x) ∂ν n) := by
  apply replica_cauchy_of_uniform_approx
  intro ε hε
  obtain ⟨p,hp⟩ := exists_polynomial_near_of_continuousOn a b f hfc
    (ε/(C+1)) (by positivity)
  refine ⟨fun n => ∫ x, W n x * p.eval (Z n x) ∂ν n,
    replica_cauchy_polynomial_moments Ω ν Z W hZ hW hM hC hz hw hm p,?_⟩
  intro n
  have hb : ∀ x, |W n x * (f (Z n x)-p.eval (Z n x))| ≤ ε := by
    intro x
    rw [abs_mul]
    have hx : |f (Z n x)-p.eval (Z n x)| ≤ ε/(C+1) := by
      rw [abs_sub_comm]; exact (hp _ (hzI n x)).le
    calc
      _ ≤ C*(ε/(C+1)) := mul_le_mul (hw n x) hx (abs_nonneg _) hC
      _ ≤ ε := by field_simp; nlinarith
  have hsmall : Integrable (fun x => W n x * (f (Z n x)-p.eval (Z n x))) (ν n) :=
    replica_integrable_of_bound ((hW n).mul ((hf.comp (hZ n)).sub
      (p.continuous.measurable.comp (hZ n)))) hb
  have hpoly : Integrable (fun x => W n x * p.eval (Z n x)) (ν n) := by
    obtain ⟨K,hK⟩ := (isCompact_Icc : IsCompact (Set.Icc a b)).exists_bound_of_continuousOn p.continuous.continuousOn
    apply replica_integrable_of_bound (C := C*K) ((hW n).mul (p.continuous.measurable.comp (hZ n)))
    intro x
    dsimp only [Pi.mul_apply,Function.comp_apply]
    rw [abs_mul]
    exact mul_le_mul (hw n x) (by simpa only [Real.norm_eq_abs] using hK _ (hzI n x))
      (abs_nonneg _) hC
  have hfi : Integrable (fun x => W n x * f (Z n x)) (ν n) :=
    (hsmall.add hpoly).congr (Eventually.of_forall fun x => by dsimp; ring)
  rw [←integral_sub hfi hpoly]
  calc
    _ = |∫ x, W n x * (f (Z n x)-p.eval (Z n x)) ∂ν n| := by congr 2; ext x; ring
    _ ≤ ∫ x, |W n x * (f (Z n x)-p.eval (Z n x))| ∂ν n := abs_integral_le_integral_abs
    _ ≤ ∫ _ : Ω n, ε ∂ν n := integral_mono hsmall.norm (integrable_const ε) hb
    _ = ε := by simp
end MicroscopicJamming

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma replica_product_between {r : ℕ} (f g : Fin r → ℝ)
    (hf : ∀ i, 0 ≤ f i) (hg : ∀ i, 0 ≤ g i) :
    |(∏ i, f i)-(∏ i,g i)| ≤ (∏ i,max (f i) (g i))-(∏ i,min (f i) (g i)) := by
  have hmn : ∀ i, 0 ≤ min (f i) (g i) := fun i => le_min (hf i) (hg i)
  have lf : (∏ i, min (f i) (g i)) ≤ ∏ i, f i :=
    Finset.prod_le_prod₀ (fun i _ => hmn i) (fun i _ => min_le_left _ _)
  have lg : (∏ i, min (f i) (g i)) ≤ ∏ i, g i :=
    Finset.prod_le_prod₀ (fun i _ => hmn i) (fun i _ => min_le_right _ _)
  have uf : (∏ i, f i) ≤ ∏ i, max (f i) (g i) :=
    Finset.prod_le_prod₀ (fun i _ => hf i) (fun i _ => le_max_left _ _)
  have ug : (∏ i, g i) ≤ ∏ i, max (f i) (g i) :=
    Finset.prod_le_prod₀ (fun i _ => hg i) (fun i _ => le_max_right _ _)
  exact abs_le.mpr ⟨by linarith,by linarith⟩

lemma replica_product_integral_difference
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {f g : S → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfp : ∀ x, 0 ≤ f x) (hgp : ∀ x, 0 ≤ g x)
    (hf1 : ∫ x, f x ∂μ = 1) (hg1 : ∫ x, g x ∂μ = 1)
    (r : ℕ) {B : (Fin r → S) → ℝ} (hB : Measurable B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ x, |B x| ≤ K) :
    |(∫ xs, B xs * ∏ i, f (xs i) ∂Measure.pi (fun _ : Fin r => μ))-
      (∫ xs, B xs * ∏ i, g (xs i) ∂Measure.pi (fun _ : Fin r => μ))| ≤
      K * (r:ℝ) * (2:ℝ)^(r-1) * ∫ x, |f x-g x| ∂μ := by
  let H := ∫ x, max (f x) (g x) ∂μ
  let L := ∫ x, min (f x) (g x) ∂μ
  have hmax : Integrable (fun x => max (f x) (g x)) μ := hf.sup hg
  have hmin : Integrable (fun x => min (f x) (g x)) μ := hf.inf hg
  have hL : 0 ≤ L := integral_nonneg (fun x => le_min (hfp x) (hgp x))
  have hLH : L ≤ H := integral_mono hmin hmax (fun x => (min_le_left _ _).trans (le_max_left _ _))
  have hH : H ≤ 2 := by
    calc
      H ≤ ∫ x, f x+g x ∂μ := integral_mono hmax (hf.add hg) (fun x => max_le (by linarith [hgp x]) (by linarith [hfp x]))
      _ = 2 := by rw [integral_add hf hg,hf1,hg1]; norm_num
  have hdiff : H-L = ∫ x, |f x-g x| ∂μ := by
    rw [←integral_sub hmax hmin]
    congr 1
    ext x
    simpa only [abs_sub_comm] using max_sub_min_eq_abs (f x) (g x)
  have hfi : Integrable (fun xs : Fin r → S => ∏ i, f (xs i)) (Measure.pi (fun _ => μ)) :=
    Integrable.fintype_prod (fun _ => hf)
  have hgi : Integrable (fun xs : Fin r → S => ∏ i, g (xs i)) (Measure.pi (fun _ => μ)) :=
    Integrable.fintype_prod (fun _ => hg)
  have hbi := hfi.bdd_mul hB.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hbgi := hgi.bdd_mul hB.aestronglyMeasurable
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  have hiH : Integrable (fun xs : Fin r → S => ∏ i, max (f (xs i)) (g (xs i))) (Measure.pi (fun _ => μ)) :=
    Integrable.fintype_prod (fun _ => hmax)
  have hiL : Integrable (fun xs : Fin r → S => ∏ i, min (f (xs i)) (g (xs i))) (Measure.pi (fun _ => μ)) :=
    Integrable.fintype_prod (fun _ => hmin)
  have hpoint (xs : Fin r → S) :
      |B xs * ∏ i,f (xs i)-B xs * ∏ i,g (xs i)| ≤
        K*((∏ i,max (f (xs i)) (g (xs i)))-(∏ i,min (f (xs i)) (g (xs i)))) := by
    rw [←mul_sub,abs_mul]
    exact mul_le_mul (hb xs) (replica_product_between _ _ (fun i => hfp _) (fun i => hgp _))
      (abs_nonneg _) hK
  have hpp : 0 ≤ H^r-L^r := sub_nonneg.mpr (pow_le_pow_left₀ hL hLH r)
  calc
    _ = |∫ xs, B xs * ∏ i,f (xs i)-B xs * ∏ i,g (xs i) ∂Measure.pi (fun _ : Fin r => μ)| :=
      congrArg abs (integral_sub hbi hbgi).symm
    _ ≤ ∫ xs, K*((∏ i,max (f (xs i)) (g (xs i)))-(∏ i,min (f (xs i)) (g (xs i))))
        ∂Measure.pi (fun _ : Fin r => μ) := by
      simpa only [Real.norm_eq_abs,Pi.sub_apply] using norm_integral_le_of_norm_le (f := fun xs : Fin r → S => B xs * ∏ i,f (xs i)-B xs * ∏ i,g (xs i))
        ((hiH.sub hiL).const_mul K) (Eventually.of_forall fun xs => by simpa only [Real.norm_eq_abs,Pi.sub_apply] using hpoint xs)
    _ = K*(H^r-L^r) := by
      rw [integral_const_mul,integral_sub hiH hiL,
        integral_fintype_prod_eq_pow (fun x => max (f x) (g x)),
        integral_fintype_prod_eq_pow (fun x => min (f x) (g x))]
      simp only [Fintype.card_fin,H,L]
    _ ≤ K*((H-L)*(r:ℝ)*(2:ℝ)^(r-1)) := by
      apply mul_le_mul_of_nonneg_left _ hK
      calc
        H^r-L^r = |H^r-L^r| := (abs_of_nonneg hpp).symm
        _ ≤ |H-L| *(r:ℝ)*max |H| |L|^(r-1) := abs_pow_sub_pow_le H L r
        _ ≤ (H-L)*(r:ℝ)*(2:ℝ)^(r-1) := by
          rw [abs_of_nonneg (sub_nonneg.mpr hLH),abs_of_nonneg (hL.trans hLH),abs_of_nonneg hL,max_eq_left hLH]
          gcongr
          exact hL.trans hLH
    _ = _ := by rw [hdiff]; ring

lemma replica_density_difference
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {f g : S → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hgp : ∀ x, 0 ≤ g x)
    (hZ : 0 < ∫ x, f x ∂μ) (hW : 0 < ∫ x, g x ∂μ) :
    (∫ x, |f x/(∫ y, f y ∂μ)-g x/(∫ y, g y ∂μ)| ∂μ) ≤
      2*(∫ x, |f x-g x| ∂μ)/(∫ x, f x ∂μ) := by
  let Z := ∫ x, f x ∂μ
  let W := ∫ x, g x ∂μ
  let δ := ∫ x, |f x-g x| ∂μ
  have hpoint (x : S) : |f x/Z-g x/W| ≤ |f x-g x|/Z+g x*|W-Z|/(Z*W) := by
    have heq : f x/Z-g x/W = (f x-g x)/Z+g x*(W-Z)/(Z*W) := by
      field_simp [show Z ≠ 0 from hZ.ne', show W ≠ 0 from hW.ne']; ring
    rw [heq]
    calc
      _ ≤ |(f x-g x)/Z|+|g x*(W-Z)/(Z*W)| := abs_add_le _ _
      _ = _ := by rw [abs_div,abs_div,abs_mul,abs_mul,abs_of_pos hZ,abs_of_pos hW,abs_of_nonneg (hgp x)]
  have hd : Integrable (fun x => |f x-g x|) μ := (hf.sub hg).norm
  have hbd : |W-Z| ≤ δ := by
    rw [abs_sub_comm]
    change |(∫ x, f x ∂μ)-(∫ x,g x ∂μ)| ≤ _
    rw [←integral_sub hf hg]
    exact abs_integral_le_integral_abs
  calc
    (∫ x, |f x/Z-g x/W| ∂μ) ≤ ∫ x, |f x-g x|/Z+g x*|W-Z|/(Z*W) ∂μ :=
      integral_mono ((hf.div_const Z).sub (hg.div_const W)).norm
        ((hd.div_const Z).add ((hg.mul_const |W-Z|).div_const (Z*W))) hpoint
    _ = δ/Z+W*|W-Z|/(Z*W) := by
      rw [integral_add (hd.div_const Z) ((hg.mul_const |W-Z|).div_const (Z*W)),
        integral_div,integral_div,integral_mul_const]
    _ = (δ+|W-Z|)/Z := by field_simp [show Z ≠ 0 from hZ.ne', show W ≠ 0 from hW.ne']
    _ ≤ 2*δ/Z := by apply div_le_div_of_nonneg_right _ hZ.le; linarith

lemma replica_normalized_integral_eq
    {S : Type*} [MeasurableSpace S] (μ : Measure S) (f : S → ℝ)
    (r : ℕ) (B : (Fin r → S) → ℝ) (Z : ℝ) :
    (∫ xs, B xs * ∏ i, f (xs i) ∂Measure.pi (fun _ : Fin r => μ))/Z^r =
      ∫ xs, B xs * ∏ i, (f (xs i)/Z) ∂Measure.pi (fun _ : Fin r => μ) := by
  rw [←integral_div]
  congr 1
  ext xs
  simp only [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  ring

lemma replica_normalized_integral_difference
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {f g : S → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfp : ∀ x, 0 ≤ f x) (hgp : ∀ x, 0 ≤ g x)
    (hZ : 0 < ∫ x, f x ∂μ) (hW : 0 < ∫ x, g x ∂μ)
    (r : ℕ) {B : (Fin r → S) → ℝ} (hB : Measurable B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ x, |B x| ≤ K) :
    |(∫ xs, B xs * ∏ i, f (xs i) ∂Measure.pi (fun _ : Fin r => μ))/(∫ x,f x ∂μ)^r-
      (∫ xs, B xs * ∏ i, g (xs i) ∂Measure.pi (fun _ : Fin r => μ))/(∫ x,g x ∂μ)^r| ≤
      2*K*(r:ℝ)*(2:ℝ)^(r-1)*(∫ x, |f x-g x| ∂μ)/(∫ x,f x ∂μ) := by
  rw [replica_normalized_integral_eq,replica_normalized_integral_eq]
  have hf1 : (∫ x, f x/(∫ y,f y ∂μ) ∂μ)=1 := by rw [integral_div]; exact div_self hZ.ne'
  have hg1 : (∫ x, g x/(∫ y,g y ∂μ) ∂μ)=1 := by rw [integral_div]; exact div_self hW.ne'
  calc
    _ ≤ K*(r:ℝ)*(2:ℝ)^(r-1) *
      ∫ x, |f x/(∫ y,f y ∂μ)-g x/(∫ y,g y ∂μ)| ∂μ :=
      replica_product_integral_difference μ (hf.div_const _) (hg.div_const _)
        (fun x => div_nonneg (hfp x) hZ.le) (fun x => div_nonneg (hgp x) hW.le) hf1 hg1 r hB hK hb
    _ ≤ K*(r:ℝ)*(2:ℝ)^(r-1)*(2*(∫ x, |f x-g x| ∂μ)/(∫ x,f x ∂μ)) :=
      mul_le_mul_of_nonneg_left (replica_density_difference μ hf hg hgp hZ hW) (by positivity)
    _ = _ := by ring
end MicroscopicJamming

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma replicaClip_mem {L x : ℝ} (hL : 0 ≤ L) : replicaClip L x ∈ Set.Icc (-L) L := by
  constructor
  · exact le_max_left _ _
  · exact max_le (by linarith) (min_le_left _ _)

lemma replicaClip_abs_le {L x : ℝ} (hL : 0 ≤ L) : |replicaClip L x| ≤ |x| := by
  apply abs_le.mpr
  constructor
  · exact (le_min (by linarith [abs_nonneg x]) (neg_abs_le x)).trans (le_max_right _ _)
  · exact max_le (by linarith [abs_nonneg x]) ((min_le_right _ _).trans (le_abs_self x))

lemma replicaClip_eq_of_abs_le {L x : ℝ} (h : |x| ≤ L) : replicaClip L x = x := by
  rw [replicaClip,min_eq_right (abs_le.mp h).2,max_eq_right (abs_le.mp h).1]

lemma measurable_replicaClip (L : ℝ) : Measurable (replicaClip L) := by
  unfold replicaClip
  fun_prop

lemma continuous_replicaClip (L : ℝ) : Continuous (replicaClip L) := by
  unfold replicaClip
  fun_prop

lemma replica_exp_clip_difference {L x : ℝ} (hL : 0 ≤ L) :
    |Real.exp x-Real.exp (replicaClip L x)| ≤ 2*Real.exp (-L)*Real.exp (2*|x|) := by
  by_cases hclip : |x| ≤ L
  · rw [replicaClip_eq_of_abs_le hclip,sub_self,abs_zero]
    positivity
  · have htail : L ≤ |x| := (not_le.mp hclip).le
    have h1 : Real.exp x ≤ Real.exp |x| := Real.exp_le_exp.mpr (le_abs_self x)
    have h2 : Real.exp (replicaClip L x) ≤ Real.exp |x| :=
      Real.exp_le_exp.mpr ((le_abs_self _).trans (replicaClip_abs_le hL))
    have h3 : Real.exp |x| ≤ Real.exp (-L)*Real.exp (2*|x|) := by
      rw [←Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    calc
      _ ≤ |Real.exp x|+|Real.exp (replicaClip L x)| := abs_sub _ _
      _ ≤ 2*Real.exp |x| := by rw [abs_of_pos (Real.exp_pos _),abs_of_pos (Real.exp_pos _)]; linarith
      _ ≤ _ := by nlinarith

lemma replica_integrable_exp_abs_mono
    {S : Type*} [MeasurableSpace S] {μ : Measure S} {v : S → ℝ}
    (hv : Measurable v) {a b : ℝ} (hab : a ≤ b)
    (hb : Integrable (fun x => Real.exp (b*|v x|)) μ) :
    Integrable (fun x => Real.exp (a*|v x|)) μ := by
  apply hb.mono' (hv.abs.const_mul a).exp.aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hab (abs_nonneg _))

lemma replica_inverse_Z_bound
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {v : S → ℝ} (hv : Measurable v)
    (h1 : Integrable (fun x => Real.exp |v x|) μ) :
    0 < (∫ x, Real.exp (v x) ∂μ) ∧
    (∫ x, Real.exp (v x) ∂μ)⁻¹ ≤ ∫ x, Real.exp |v x| ∂μ := by
  have he : Integrable (fun x => Real.exp (v x)) μ := by
    apply h1.mono' hv.exp.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (le_abs_self _)
  have hp := integral_exp_pos he
  refine ⟨hp,?_⟩
  have ha : Integrable (fun x => |v x|) μ := by
    apply h1.mono' hv.abs.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_abs]
      linarith [Real.add_one_le_exp |v x|]
  have hen : Integrable (fun x => Real.exp (-|v x|)) μ := by
    apply (integrable_const (1:ℝ)).mono' hv.abs.neg.exp.aestronglyMeasurable
    exact Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (abs_nonneg _))
  have hjp := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) ha h1
  have hjn := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall fun _ => mem_univ _) ha.neg hen
  simp only [Pi.neg_apply,integral_neg] at hjn
  have hlo : Real.exp (-(∫ x, |v x| ∂μ)) ≤ ∫ x, Real.exp (v x) ∂μ :=
    hjn.trans (integral_mono hen he (fun x => Real.exp_le_exp.mpr (neg_abs_le _)))
  apply le_trans _ hjp
  apply (inv_le_iff_one_le_mul₀' hp).mpr
  calc
    1 = Real.exp (-(∫ x, |v x| ∂μ))*Real.exp (∫ x, |v x| ∂μ) := by rw [←Real.exp_add]; simp
    _ ≤ (∫ x, Real.exp (v x) ∂μ)*Real.exp (∫ x, |v x| ∂μ) :=
      mul_le_mul_of_nonneg_right hlo (Real.exp_pos _).le

lemma replica_moment_square_le
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {v : S → ℝ} (hv : Measurable v)
    (h4 : Integrable (fun x => Real.exp (4*|v x|)) μ) :
    (∫ x, Real.exp (2*|v x|) ∂μ)^2 ≤ ∫ x, Real.exp (4*|v x|) ∂μ := by
  have h2 := replica_integrable_exp_abs_mono hv (show (2:ℝ) ≤ 4 by norm_num) h4
  have hsq : Integrable (fun x => (Real.exp (2*|v x|))^2) μ := by
    convert h4 using 1
    ext x
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  have hj := (convexOn_pow (𝕜 := ℝ) 2).map_integral_le
    (continuous_pow 2).continuousOn isClosed_Ici
    (Eventually.of_forall fun x => (Real.exp_pos (2*|v x|)).le) h2 hsq
  convert hj using 1
  congr 1
  ext x
  rw [←Real.exp_nat_mul]
  congr 1
  norm_num
  ring

lemma replica_abs_log_bound {x : ℝ} (hx : 0 < x) : |Real.log x| ≤ x+x⁻¹ := by
  have h := Real.log_le_sub_one_of_pos hx
  have hi := Real.log_le_sub_one_of_pos (inv_pos.mpr hx)
  rw [Real.log_inv] at hi
  exact abs_le.mpr ⟨by linarith [hx,inv_pos.mpr hx],by linarith [inv_pos.mpr hx]⟩

lemma replica_abs_log_sub_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |Real.log a-Real.log b| ≤ |a-b| *(a⁻¹+b⁻¹) := by
  have hab := Real.log_le_sub_one_of_pos (div_pos ha hb)
  have hba := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div ha.ne' hb.ne'] at hab
  rw [Real.log_div hb.ne' ha.ne'] at hba
  have h := abs_nonneg (a-b)
  have hleft : a/b-1 ≤ |a-b|/b := by
    apply (le_div_iff₀ hb).mpr
    rw [sub_mul,div_mul_cancel₀ _ hb.ne',one_mul]
    exact le_abs_self (a-b)
  have hright : b/a-1 ≤ |a-b|/a := by
    apply (le_div_iff₀ ha).mpr
    rw [sub_mul,div_mul_cancel₀ _ ha.ne',one_mul]
    linarith [neg_abs_le (a-b)]
  apply abs_le.mpr
  constructor
  · have hx := hba.trans hright
    rw [div_eq_mul_inv] at hx
    have hn := mul_nonneg h (inv_pos.mpr hb).le
    nlinarith
  · have hx := hab.trans hleft
    rw [div_eq_mul_inv] at hx
    have hn := mul_nonneg h (inv_pos.mpr ha).le
    nlinarith
end MicroscopicJamming

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma replica_clip_exp_integrable
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsFiniteMeasure μ]
    {v : S → ℝ} (hv : Measurable v) {L : ℝ} (hL : 0 ≤ L) :
    Integrable (fun x => Real.exp (replicaClip L (v x))) μ := by
  apply replica_integrable_of_bound ((measurable_replicaClip L).comp hv).exp
  intro x
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (replicaClip_mem hL).2

lemma replica_clip_Z_bounds
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {v : S → ℝ} (hv : Measurable v) {L : ℝ} (hL : 0 ≤ L) :
    (∫ x, Real.exp (replicaClip L (v x)) ∂μ) ∈ Set.Icc (Real.exp (-L)) (Real.exp L) := by
  have hi := replica_clip_exp_integrable μ hv hL
  constructor
  · simpa using integral_mono (integrable_const (Real.exp (-L))) hi
      (fun x => Real.exp_le_exp.mpr (replicaClip_mem hL).1)
  · simpa using integral_mono hi (integrable_const (Real.exp L))
      (fun x => Real.exp_le_exp.mpr (replicaClip_mem hL).2)

lemma replica_weighted_product_bound
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {f : S → ℝ} (hf : Integrable f μ) (hfp : ∀ x, 0 ≤ f x)
    (r : ℕ) {B : (Fin r → S) → ℝ} (_hB : Measurable B)
    {K : ℝ} (_hK : 0 ≤ K) (hb : ∀ x, |B x| ≤ K) :
    |∫ xs, B xs * ∏ i, f (xs i) ∂Measure.pi (fun _ : Fin r => μ)| ≤
      K*(∫ x, f x ∂μ)^r := by
  have hi := Integrable.fintype_prod (fun _ : Fin r => hf)
  calc
    _ ≤ ∫ xs, K* ∏ i, f (xs i) ∂Measure.pi (fun _ : Fin r => μ) := by
      rw [←Real.norm_eq_abs]
      apply norm_integral_le_of_norm_le (hi.const_mul K)
      filter_upwards [] with xs
      simp only [Real.norm_eq_abs,abs_mul,abs_of_nonneg (Finset.prod_nonneg (fun i _ => hfp _))]
      exact mul_le_mul_of_nonneg_right (hb xs) (Finset.prod_nonneg (fun i _ => hfp _))
    _ = _ := by rw [integral_const_mul,integral_fintype_prod_eq_pow]; simp

lemma replica_fiber_log_estimates
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {v : S → ℝ} (hv : Measurable v)
    (h4 : Integrable (fun x => Real.exp (4*|v x|)) μ)
    {L : ℝ} (hL : 0 ≤ L) :
    let Z := ∫ x, Real.exp (v x) ∂μ
    let W := ∫ x, Real.exp (replicaClip L (v x)) ∂μ
    let A := ∫ x, Real.exp (4*|v x|) ∂μ
    0 < Z ∧ 0 < W ∧ |Real.log Z| ≤ 2*A ∧
      |Real.log Z-Real.log W| ≤ 4*Real.exp (-L)*A := by
  let A1 := ∫ x, Real.exp |v x| ∂μ
  let A2 := ∫ x, Real.exp (2*|v x|) ∂μ
  let A4 := ∫ x, Real.exp (4*|v x|) ∂μ
  have hi1 : Integrable (fun x => Real.exp |v x|) μ := by
    simpa using replica_integrable_exp_abs_mono hv (show (1:ℝ) ≤ 4 by norm_num) h4
  have hi2 := replica_integrable_exp_abs_mono hv (show (2:ℝ) ≤ 4 by norm_num) h4
  have hi : Integrable (fun x => Real.exp (v x)) μ := by
    apply hi1.mono' hv.exp.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (le_abs_self _))
  have hic := replica_clip_exp_integrable μ hv hL
  have hci : Integrable (fun x => Real.exp |replicaClip L (v x)|) μ := by
    apply hi1.mono' (((measurable_replicaClip L).comp hv).abs.exp.aestronglyMeasurable)
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (replicaClip_abs_le hL))
  have hZ := replica_inverse_Z_bound μ hv hi1
  have hW := replica_inverse_Z_bound μ ((measurable_replicaClip L).comp hv) hci
  simp only [Function.comp_apply] at hW
  have hc1 : (∫ x, Real.exp |replicaClip L (v x)| ∂μ) ≤ A1 :=
    integral_mono hci hi1 (fun x => Real.exp_le_exp.mpr (replicaClip_abs_le hL))
  have h12 : A1 ≤ A2 := integral_mono hi1 hi2 (fun x => Real.exp_le_exp.mpr (by linarith [abs_nonneg (v x)]))
  have h14 : A1 ≤ A4 := integral_mono hi1 h4 (fun x => Real.exp_le_exp.mpr (by linarith [abs_nonneg (v x)]))
  have h1n : 0 ≤ A1 := integral_nonneg (fun x => (Real.exp_pos _).le)
  have h2n : 0 ≤ A2 := integral_nonneg (fun x => (Real.exp_pos _).le)
  have hZ1 : (∫ x, Real.exp (v x) ∂μ) ≤ A1 :=
    integral_mono hi hi1 (fun x => Real.exp_le_exp.mpr (le_abs_self _))
  have hdiff : |(∫ x, Real.exp (v x) ∂μ)-(∫ x, Real.exp (replicaClip L (v x)) ∂μ)| ≤
      2*Real.exp (-L)*A2 := by
    rw [←integral_sub hi hic,←integral_const_mul]
    rw [←Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le (hi2.const_mul (2*Real.exp (-L))) (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using replica_exp_clip_difference (x := v x) hL)
  dsimp only
  refine ⟨hZ.1,hW.1,?_,?_⟩
  · exact (replica_abs_log_bound hZ.1).trans (by linarith [hZ.2])
  · calc
      _ ≤ |(∫ x, Real.exp (v x) ∂μ)-(∫ x, Real.exp (replicaClip L (v x)) ∂μ)| *
          ((∫ x, Real.exp (v x) ∂μ)⁻¹+(∫ x, Real.exp (replicaClip L (v x)) ∂μ)⁻¹) :=
        replica_abs_log_sub_bound hZ.1 hW.1
      _ ≤ (2*Real.exp (-L)*A2)*(2*A2) :=
        mul_le_mul hdiff (by linarith [hZ.2,hW.2]) (by positivity) (by positivity)
      _ = 4*Real.exp (-L)*A2^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (replica_moment_square_le μ hv h4) (by positivity)

lemma replica_fiber_tilt_estimates
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    {v : S → ℝ} (hv : Measurable v)
    (h4 : Integrable (fun x => Real.exp (4*|v x|)) μ)
    {L : ℝ} (hL : 0 ≤ L)
    (r : ℕ) {B : (Fin r → S) → ℝ} (hB : Measurable B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ x, |B x| ≤ K) :
    let Z := ∫ x, Real.exp (v x) ∂μ
    let W := ∫ x, Real.exp (replicaClip L (v x)) ∂μ
    let N := ∫ xs, B xs*∏ i, Real.exp (v (xs i)) ∂Measure.pi (fun _ : Fin r => μ)
    let M := ∫ xs, B xs*∏ i, Real.exp (replicaClip L (v (xs i))) ∂Measure.pi (fun _ : Fin r => μ)
    |N/Z^r| ≤ K ∧ |N/Z^r-M/W^r| ≤
      (4*K*(r:ℝ)*(2:ℝ)^(r-1))*Real.exp (-L)*(∫ x, Real.exp (4*|v x|) ∂μ) := by
  let A1 := ∫ x, Real.exp |v x| ∂μ
  let A2 := ∫ x, Real.exp (2*|v x|) ∂μ
  have hi1 : Integrable (fun x => Real.exp |v x|) μ := by
    simpa using replica_integrable_exp_abs_mono hv (show (1:ℝ) ≤ 4 by norm_num) h4
  have hi2 := replica_integrable_exp_abs_mono hv (show (2:ℝ) ≤ 4 by norm_num) h4
  have hi : Integrable (fun x => Real.exp (v x)) μ := by
    apply hi1.mono' hv.exp.aestronglyMeasurable
    exact Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]; exact Real.exp_le_exp.mpr (le_abs_self _))
  have hic := replica_clip_exp_integrable μ hv hL
  have hZ := replica_inverse_Z_bound μ hv hi1
  have hW : 0 < ∫ x, Real.exp (replicaClip L (v x)) ∂μ :=
    (Real.exp_pos (-L)).trans_le (replica_clip_Z_bounds μ hv hL).1
  have h12 : A1 ≤ A2 := integral_mono hi1 hi2 (fun x => Real.exp_le_exp.mpr (by linarith [abs_nonneg (v x)]))
  have h2n : 0 ≤ A2 := integral_nonneg (fun x => (Real.exp_pos _).le)
  have hdiff : (∫ x, |Real.exp (v x)-Real.exp (replicaClip L (v x))| ∂μ) ≤
      2*Real.exp (-L)*A2 := by
    rw [←integral_const_mul]
    exact integral_mono (hi.sub hic).norm (hi2.const_mul _) (fun x => replica_exp_clip_difference hL)
  dsimp only
  constructor
  · rw [abs_div,abs_of_pos (pow_pos hZ.1 r)]
    exact (div_le_iff₀ (pow_pos hZ.1 r)).mpr (replica_weighted_product_bound μ hi
      (fun x => (Real.exp_pos _).le) r hB hK hb)
  · calc
      _ ≤ 2*K*(r:ℝ)*(2:ℝ)^(r-1)*(∫ x, |Real.exp (v x)-Real.exp (replicaClip L (v x))| ∂μ)/
          (∫ x,Real.exp (v x) ∂μ) :=
        replica_normalized_integral_difference μ hi hic (fun x => (Real.exp_pos _).le)
          (fun x => (Real.exp_pos _).le) hZ.1 hW r hB hK hb
      _ = (2*K*(r:ℝ)*(2:ℝ)^(r-1)) *
          ((∫ x, |Real.exp (v x)-Real.exp (replicaClip L (v x))| ∂μ)*(∫ x,Real.exp (v x) ∂μ)⁻¹) := by ring
      _ ≤ (2*K*(r:ℝ)*(2:ℝ)^(r-1))*((2*Real.exp (-L)*A2)*A2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hdiff (hZ.2.trans h12) (by positivity) (by positivity)
      _ = (4*K*(r:ℝ)*(2:ℝ)^(r-1))*Real.exp (-L)*A2^2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (replica_moment_square_le μ hv h4) (by positivity)
end MicroscopicJamming

end

end OAI
