import Mathlib
import OAI.Probability.JammingConcavity.RowZeroRefinementClosure

namespace OAI

/-! Row Zero Refinement Closure Profile Distance Eq Zero Of Tests. -/

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
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma replica_ensemble_clipping_errors
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (G : Kernel Ω S) [IsMarkovKernel G]
    {V : Ω × S → ℝ} (hV : Measurable V)
    (h4 : Integrable (fun z => Real.exp (4*|V z|)) (ν ⊗ₘ G))
    {L : ℝ} (hL : 0 ≤ L) (r : ℕ)
    {B : Ω × (Fin r → S) → ℝ} (hB : Measurable B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ z, |B z| ≤ K) :
    |(∫ ω, Real.log (replicaZ G V ω) ∂ν)-
      (∫ ω, Real.log (replicaZ G (fun z => replicaClip L (V z)) ω) ∂ν)| ≤
        4*Real.exp (-L)*(∫ z, Real.exp (4*|V z|) ∂(ν ⊗ₘ G)) ∧
    |(∫ ω, replicaNum G V B ω/(replicaZ G V ω)^r ∂ν)-
      (∫ ω, replicaNum G (fun z => replicaClip L (V z)) B ω/
        (replicaZ G (fun z => replicaClip L (V z)) ω)^r ∂ν)| ≤
        (4*K*(r:ℝ)*(2:ℝ)^(r-1))*Real.exp (-L)*(∫ z, Real.exp (4*|V z|) ∂(ν ⊗ₘ G)) := by
  have hsplit := (Measure.integrable_compProd_iff h4.aestronglyMeasurable).mp h4
  have hAi : Integrable (fun ω => ∫ x, Real.exp (4*|V (ω,x)|) ∂G ω) ν := by
    simpa only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)] using hsplit.2
  have hlogms := Real.measurable_log.comp (measurable_replicaZ G hV)
  have hVC := (measurable_replicaClip L).comp hV
  have hlogcms := Real.measurable_log.comp (measurable_replicaZ G hVC)
  have htiltms := (measurable_replicaNum G hV hB).div ((measurable_replicaZ G hV).pow_const r)
  have htiltcms := (measurable_replicaNum G hVC hB).div ((measurable_replicaZ G hVC).pow_const r)
  have hlogbd : ∀ᵐ ω ∂ν, |Real.log (replicaZ G V ω)| ≤
      2*(∫ x, Real.exp (4*|V (ω,x)|) ∂G ω) := by
    filter_upwards [hsplit.1] with ω hω
    exact (replica_fiber_log_estimates (G ω) (hV.comp (measurable_const.prodMk measurable_id)) hω hL).2.2.1
  have hlogdiff : ∀ᵐ ω ∂ν, |Real.log (replicaZ G V ω)-Real.log (replicaZ G (fun z => replicaClip L (V z)) ω)| ≤
      4*Real.exp (-L)*(∫ x, Real.exp (4*|V (ω,x)|) ∂G ω) := by
    filter_upwards [hsplit.1] with ω hω
    exact (replica_fiber_log_estimates (G ω) (hV.comp (measurable_const.prodMk measurable_id)) hω hL).2.2.2
  have htiltbd : ∀ᵐ ω ∂ν, |replicaNum G V B ω/(replicaZ G V ω)^r| ≤ K := by
    filter_upwards [hsplit.1] with ω hω
    exact (replica_fiber_tilt_estimates (G ω) (hV.comp (measurable_const.prodMk measurable_id)) hω hL r
      (hB.comp (measurable_const.prodMk measurable_id)) hK (fun xs => hb (ω,xs))).1
  have htiltdiff : ∀ᵐ ω ∂ν,
      |replicaNum G V B ω/(replicaZ G V ω)^r-
        replicaNum G (fun z => replicaClip L (V z)) B ω/(replicaZ G (fun z => replicaClip L (V z)) ω)^r| ≤
       (4*K*(r:ℝ)*(2:ℝ)^(r-1))*Real.exp (-L)*(∫ x, Real.exp (4*|V (ω,x)|) ∂G ω) := by
    filter_upwards [hsplit.1] with ω hω
    exact (replica_fiber_tilt_estimates (G ω) (hV.comp (measurable_const.prodMk measurable_id)) hω hL r
      (hB.comp (measurable_const.prodMk measurable_id)) hK (fun xs => hb (ω,xs))).2
  have hlogi := (hAi.const_mul 2).mono' hlogms.aestronglyMeasurable (by simpa only [Real.norm_eq_abs, Function.comp_def, Pi.sub_apply, Pi.div_apply] using hlogbd)
  have hlogdi := (hAi.const_mul (4*Real.exp (-L))).mono' (hlogms.sub hlogcms).aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs, Function.comp_def, Pi.sub_apply, Pi.div_apply] using hlogdiff)
  have hlogci : Integrable (fun ω => Real.log (replicaZ G (fun z => replicaClip L (V z)) ω)) ν :=
    (hlogi.sub hlogdi).congr (Eventually.of_forall fun ω => by simp only [Function.comp_def, Pi.sub_apply]; ring)
  have htilti := (integrable_const K).mono' htiltms.aestronglyMeasurable (by simpa only [Real.norm_eq_abs, Function.comp_def, Pi.sub_apply, Pi.div_apply] using htiltbd)
  have htiltdi := (hAi.const_mul ((4*K*(r:ℝ)*(2:ℝ)^(r-1))*Real.exp (-L))).mono'
    (htiltms.sub htiltcms).aestronglyMeasurable (by simpa only [Real.norm_eq_abs, Function.comp_def, Pi.sub_apply, Pi.div_apply] using htiltdiff)
  have htiltci : Integrable (fun ω => replicaNum G (fun z => replicaClip L (V z)) B ω/
      (replicaZ G (fun z => replicaClip L (V z)) ω)^r) ν :=
    (htilti.sub htiltdi).congr (Eventually.of_forall fun ω => by simp only [Function.comp_def, Pi.sub_apply, Pi.div_apply]; ring)
  constructor
  · rw [←integral_sub (f := fun ω => Real.log (replicaZ G V ω)) (g := fun ω => Real.log (replicaZ G (fun z => replicaClip L (V z)) ω)) hlogi hlogci,Measure.integral_compProd h4,←integral_const_mul,←Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le (hAi.const_mul (4*Real.exp (-L)))
      (by simpa only [Real.norm_eq_abs, Function.comp_def, Pi.sub_apply, Pi.div_apply] using hlogdiff)
  · rw [←integral_sub (f := fun ω => replicaNum G V B ω/(replicaZ G V ω)^r) (g := fun ω => replicaNum G (fun z => replicaClip L (V z)) B ω/(replicaZ G (fun z => replicaClip L (V z)) ω)^r) htilti htiltci,Measure.integral_compProd h4,←integral_const_mul,←Real.norm_eq_abs]
    exact norm_integral_le_of_norm_le (hAi.const_mul ((4*K*(r:ℝ)*(2:ℝ)^(r-1))*Real.exp (-L)))
      (by simpa only [Real.norm_eq_abs, Function.comp_def, Pi.sub_apply, Pi.div_apply] using htiltdiff)

lemma replica_cauchy_clipped
    (Ω S : ℕ → Type*) [∀ n, MeasurableSpace (Ω n)] [∀ n, MeasurableSpace (S n)]
    (ν : ∀ n, Measure (Ω n)) [∀ n, IsProbabilityMeasure (ν n)]
    (G : ∀ n, Kernel (Ω n) (S n)) [∀ n, IsMarkovKernel (G n)]
    (V : ∀ n, Ω n × S n → ℝ) (hV : ∀ n, Measurable (V n))
    {L : ℝ} (hL : 0 ≤ L) (r : ℕ)
    (B : ∀ n, Ω n × (Fin r → S n) → ℝ) (hB : ∀ n, Measurable (B n))
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ n z, |B n z| ≤ K)
    (hZ : ∀ k : ℕ, CauchySeq (fun n => ∫ ω,
      (replicaZ (G n) (fun z => replicaClip L (V n z)) ω)^k ∂ν n))
    (hN : ∀ k : ℕ, CauchySeq (fun n => ∫ ω,
      replicaNum (G n) (fun z => replicaClip L (V n z)) (B n) ω *
        (replicaZ (G n) (fun z => replicaClip L (V n z)) ω)^k ∂ν n)) :
    CauchySeq (fun n => ∫ ω, Real.log (replicaZ (G n) (fun z => replicaClip L (V n z)) ω) ∂ν n) ∧
    CauchySeq (fun n => ∫ ω,
      replicaNum (G n) (fun z => replicaClip L (V n z)) (B n) ω/
        (replicaZ (G n) (fun z => replicaClip L (V n z)) ω)^r ∂ν n) := by
  let Z := fun n => replicaZ (G n) (fun z => replicaClip L (V n z))
  let N := fun n => replicaNum (G n) (fun z => replicaClip L (V n z)) (B n)
  have hVC n := (measurable_replicaClip L).comp (hV n)
  have hzI : ∀ n ω, Z n ω ∈ Set.Icc (Real.exp (-L)) (Real.exp L) := fun n ω =>
    replica_clip_Z_bounds (G n ω) ((hV n).comp (measurable_const.prodMk measurable_id)) hL
  have hzpos : ∀ n ω, 0 < Z n ω := fun n ω => (Real.exp_pos (-L)).trans_le (hzI n ω).1
  have hzb : ∀ n ω, |Z n ω| ≤ Real.exp L := fun n ω => by rw [abs_of_pos (hzpos n ω)]; exact (hzI n ω).2
  have hNb : ∀ n ω, |N n ω| ≤ K*(Real.exp L)^r := by
    intro n ω
    apply (replica_weighted_product_bound (G n ω)
      (replica_clip_exp_integrable (G n ω) ((hV n).comp (measurable_const.prodMk measurable_id)) hL)
      (fun x => (Real.exp_pos _).le) r ((hB n).comp (measurable_const.prodMk measurable_id)) hK
      (fun xs => hb n (ω,xs))).trans
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hzpos n ω).le (hzI n ω).2 r) hK
  constructor
  · have h := replica_cauchy_continuous_moments Ω ν Z (fun _ _ => 1)
      (fun n => measurable_replicaZ (G n) (hVC n)) (fun _ => measurable_const)
      (Real.exp_pos L).le (show (0:ℝ) ≤ 1 by norm_num) hzb (fun _ _ => by norm_num) hzI
      (by simpa only [one_mul] using hZ) Real.log Real.measurable_log
      (Real.continuousOn_log.mono (fun x hx => by
        simp only [mem_compl_iff,mem_singleton_iff]; exact ne_of_gt ((Real.exp_pos (-L)).trans_le hx.1)))
    simpa only [one_mul] using h
  · have h := replica_cauchy_continuous_moments Ω ν Z N
      (fun n => measurable_replicaZ (G n) (hVC n)) (fun n => measurable_replicaNum (G n) (hVC n) (hB n))
      (Real.exp_pos L).le (mul_nonneg hK (pow_nonneg (Real.exp_pos L).le r)) hzb hNb hzI hN
      (fun x => (x^r)⁻¹) ((measurable_id.pow_const r).inv)
      ((continuousOn_id.pow r).inv₀ (fun x hx => (pow_pos ((Real.exp_pos (-L)).trans_le hx.1) r).ne'))
    simpa only [div_eq_mul_inv] using h

lemma replica_small_exp_tail (C : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : ℕ, C*Real.exp (-((L:ℝ)+1)) ≤ ε := by
  have ht : Tendsto (fun L : ℕ => C*Real.exp (-((L:ℝ)+1))) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atBot.comp
      (tendsto_neg_atTop_atBot.comp (tendsto_atTop_add_const_right atTop (1:ℝ) tendsto_natCast_atTop_atTop))
    simpa using h.const_mul C
  exact (ht.eventually_le_const hε).exists

theorem replicaTruncation : ReplicaTruncationStatement := by
  intro Ω S mΩ mS ν G hν hG V hV hExp r B hB hBb hZm hNm
  let := mΩ
  let := mS
  let := hν
  let := hG
  obtain ⟨C,hC⟩ := hExp 4 (by norm_num)
  obtain ⟨K,hK⟩ := hBb
  let K' := max K 0
  have hK' : 0 ≤ K' := le_max_right _ _
  have hkb : ∀ n z, |B n z| ≤ K' := fun n z => (hK n z).trans (le_max_left _ _)
  have hci (L : ℕ) := replica_cauchy_clipped Ω S ν G V hV (show 0 ≤ ((L:ℝ)+1) by positivity) r B hB hK' hkb (hZm L) (hNm L)
  constructor
  · apply cauchySeq_tendsto_of_complete
    apply replica_cauchy_of_uniform_approx
    intro ε hε
    obtain ⟨L,hL⟩ := replica_small_exp_tail (4*max C 0) hε
    refine ⟨fun n => ∫ ω, Real.log (replicaZ (G n) (fun z => replicaClip ((L:ℝ)+1) (V n z)) ω) ∂ν n,
      (hci L).1,fun n => ?_⟩
    apply ((replica_ensemble_clipping_errors (ν n) (G n) (hV n) (hC n).1
      (show 0 ≤ ((L:ℝ)+1) by positivity) r (hB n) hK' (hkb n)).1).trans
    calc
      _ ≤ 4*Real.exp (-((L:ℝ)+1))*max C 0 :=
        mul_le_mul_of_nonneg_left ((hC n).2.trans (le_max_left _ _)) (by positivity)
      _ = (4*max C 0)*Real.exp (-((L:ℝ)+1)) := by ring
      _ ≤ ε := hL
  · apply cauchySeq_tendsto_of_complete
    apply replica_cauchy_of_uniform_approx
    intro ε hε
    obtain ⟨L,hL⟩ := replica_small_exp_tail ((4*K'*(r:ℝ)*(2:ℝ)^(r-1))*max C 0) hε
    refine ⟨fun n => ∫ ω,
      replicaNum (G n) (fun z => replicaClip ((L:ℝ)+1) (V n z)) (B n) ω/
        (replicaZ (G n) (fun z => replicaClip ((L:ℝ)+1) (V n z)) ω)^r ∂ν n,
      (hci L).2,fun n => ?_⟩
    apply ((replica_ensemble_clipping_errors (ν n) (G n) (hV n) (hC n).1
      (show 0 ≤ ((L:ℝ)+1) by positivity) r (hB n) hK' (hkb n)).2).trans
    calc
      _ ≤ (4*K'*(r:ℝ)*(2:ℝ)^(r-1))*Real.exp (-((L:ℝ)+1))*max C 0 :=
        mul_le_mul_of_nonneg_left ((hC n).2.trans (le_max_left _ _)) (by positivity)
      _ = ((4*K'*(r:ℝ)*(2:ℝ)^(r-1))*max C 0)*Real.exp (-((L:ℝ)+1)) := by ring
      _ ≤ ε := hL
end MicroscopicJamming

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma replica_integral_snoc
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (k : ℕ) (F : (Fin (k+1) → S) → ℝ) :
    (∫ xs, F xs ∂Measure.pi (fun _ : Fin (k+1) => μ)) =
      ∫ p : S × (Fin k → S), F (Fin.snoc p.2 p.1) ∂μ.prod (Measure.pi (fun _ : Fin k => μ)) := by
  have h := ((measurePreserving_piFinSuccAbove (fun _ : Fin (k+1) => μ) (Fin.last k)).symm).integral_comp' F
  simpa only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
    Equiv.coe_fn_mk, Fin.insertNth_last'] using h.symm

lemma replicaFirst_snoc {S : Type*} (r k : ℕ) (xs : Fin (r+k) → S) (x : S) :
    replicaFirst r (k+1) (Fin.snoc xs x) = replicaFirst r k xs := by
  ext i
  simp only [replicaFirst,←Fin.castSucc_castAdd,Fin.snoc_castSucc]

lemma replica_integral_split
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (r k : ℕ) (A : (Fin r → S) → ℝ) (f : S → ℝ) :
    (∫ xs, A (replicaFirst r k xs) * ∏ i : Fin k, f (xs (Fin.natAdd r i))
      ∂Measure.pi (fun _ : Fin (r+k) => μ)) =
        (∫ xs, A xs ∂Measure.pi (fun _ : Fin r => μ))*(∫ x, f x ∂μ)^k := by
  induction k with
  | zero =>
    have hz (xs : Fin r → S) : replicaFirst r 0 xs = xs := by ext i; rfl
    simp only [Finset.univ_eq_empty,Finset.prod_empty,mul_one,pow_zero]
    simp_rw [hz]
    rfl
  | succ k ih =>
    calc
      _ = ∫ p : S × (Fin (r+k) → S), A (replicaFirst r (k+1) (Fin.snoc p.2 p.1))*
          ∏ i : Fin (k+1),f ((Fin.snoc p.2 p.1 : Fin (r+(k+1)) → S) (Fin.natAdd r i))
          ∂μ.prod (Measure.pi (fun _ : Fin (r+k) => μ)) := replica_integral_snoc μ (r+k) _
      _ = _ := by
        have heq (p : S × (Fin (r+k) → S)) :
            A (replicaFirst r (k+1) (Fin.snoc p.2 p.1)) *
              ∏ i : Fin (k+1), f ((Fin.snoc p.2 p.1 : Fin (r+(k+1)) → S) (Fin.natAdd r i)) =
            f p.1*(A (replicaFirst r k p.2) * ∏ i : Fin k, f (p.2 (Fin.natAdd r i))) := by
          rw [replicaFirst_snoc,Fin.prod_univ_castSucc]
          simp only [Fin.natAdd_castSucc,Fin.natAdd_last,Fin.snoc_castSucc]
          rw [show (Fin.snoc p.2 p.1 : Fin (r+(k+1)) → S) (Fin.last (r+k)) = p.1 from Fin.snoc_last _ _]
          ring
        simp_rw [heq]
        rw [integral_prod_mul f (fun xs : Fin (r+k) → S => A (replicaFirst r k xs) *
          ∏ i : Fin k, f (xs (Fin.natAdd r i))),ih,pow_succ]
        ring

lemma replica_integral_all_products
    {S : Type*} [MeasurableSpace S] (μ : Measure S) [IsProbabilityMeasure μ]
    (r k : ℕ) (B : (Fin r → S) → ℝ) (f : S → ℝ) :
    (∫ xs, B (replicaFirst r k xs) * ∏ i : Fin (r+k), f (xs i)
      ∂Measure.pi (fun _ : Fin (r+k) => μ)) =
        (∫ xs, B xs*∏ i : Fin r,f (xs i) ∂Measure.pi (fun _ : Fin r => μ))*(∫ x, f x ∂μ)^k := by
  have heq (xs : Fin (r+k) → S) :
      B (replicaFirst r k xs) * ∏ i : Fin (r+k), f (xs i) =
      (B (replicaFirst r k xs) * ∏ i : Fin r, f (replicaFirst r k xs i))*
        ∏ i : Fin k, f (xs (Fin.natAdd r i)) := by
    rw [Fin.prod_univ_add]
    simp only [replicaFirst]
    ring
  simp_rw [heq]
  exact replica_integral_split μ r k (fun xs => B xs*∏ i,f (xs i)) f
end MicroscopicJamming

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

lemma measurable_replicaFieldView
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    {r : ℕ} {V : Ω × S → ℝ} (hV : Measurable V)
    {B : Ω × (Fin r → S) → ℝ} (hB : Measurable B) (k : ℕ) :
    Measurable (replicaFieldView V B k) := by
  have hfirst : Measurable (replicaFirst (S := S) r k) :=
    Measurable.of_eval (fun coordinate => measurable_pi_apply _)
  exact (hB.comp (measurable_fst.prodMk (hfirst.comp measurable_snd))).prodMk
    (Measurable.of_eval (fun i => hV.comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))))

lemma replica_exp_clip_product_bound {m : ℕ} (L : ℝ) (hL : 0 ≤ L) (v : Fin m → ℝ) :
    |∏ i, Real.exp (replicaClip L (v i))| ≤ (Real.exp L)^m := by
  rw [abs_of_nonneg (Finset.prod_nonneg (fun i _ => (Real.exp_pos _).le))]
  calc
    _ ≤ ∏ _i : Fin m, Real.exp L := Finset.prod_le_prod₀
      (fun i _ => (Real.exp_pos _).le) (fun i _ => Real.exp_le_exp.mpr (replicaClip_mem hL).2)
    _ = _ := by simp

noncomputable def replicaTailTest (r k : ℕ) (L : ℝ) (hL : 0 ≤ L) :
    BoundedContinuousFunction (ℝ × (Fin (r+k) → ℝ)) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => ∏ i : Fin k, Real.exp (replicaClip L (z.2 (Fin.natAdd r i))))
    (continuous_finsetProd _ (fun i _ => Real.continuous_exp.comp
      ((continuous_replicaClip L).comp ((continuous_apply _).comp continuous_snd))))
    ((Real.exp L)^k) (fun z => by
      simpa only [Real.norm_eq_abs] using replica_exp_clip_product_bound L hL (fun i => z.2 (Fin.natAdd r i)))

noncomputable def replicaFullTest (r k : ℕ) (K L : ℝ) (hK : 0 ≤ K) (hL : 0 ≤ L) :
    BoundedContinuousFunction (ℝ × (Fin (r+k) → ℝ)) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun z => replicaClip K z.1 * ∏ i : Fin (r+k), Real.exp (replicaClip L (z.2 i)))
    (((continuous_replicaClip K).comp continuous_fst).mul
      (continuous_finsetProd _ (fun i _ => Real.continuous_exp.comp
        ((continuous_replicaClip L).comp ((continuous_apply _).comp continuous_snd)))))
    (K*(Real.exp L)^(r+k)) (fun z => by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (abs_le.mpr (replicaClip_mem hK))
        (replica_exp_clip_product_bound L hL z.2) (abs_nonneg _) hK)

lemma replica_tail_law_moment
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (G : Kernel Ω S) [IsMarkovKernel G]
    {V : Ω × S → ℝ} (hV : Measurable V) {r : ℕ}
    {B : Ω × (Fin r → S) → ℝ} (hB : Measurable B)
    (k : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ z, replicaTailTest r k L hL z ∂replicaFieldLaw ν G V B k) =
      ∫ ω, (replicaZ G (fun z => replicaClip L (V z)) ω)^k ∂ν := by
  have ht := (replicaTailTest r k L hL).continuous.measurable
  have hm := measurable_replicaFieldView hV hB k
  have hi : Integrable (fun z => replicaTailTest r k L hL (replicaFieldView V B k z))
      (ν ⊗ₘ replicaKernel G (r+k)) := by
    apply replica_integrable_of_bound (C := (Real.exp L)^k) (ht.comp hm)
    intro z
    exact replica_exp_clip_product_bound L hL _
  rw [replicaFieldLaw,integral_map hm.aemeasurable ht.aestronglyMeasurable,Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [replicaKernel_apply]
  change (∫ xs, ∏ i : Fin k, Real.exp (replicaClip L (V (ω,xs (Fin.natAdd r i))))
      ∂Measure.pi (fun _ : Fin (r+k) => G ω)) = _
  have h := replica_integral_split (G ω) r k (fun _ => 1) (fun x => Real.exp (replicaClip L (V (ω,x))))
  simpa [replicaZ] using h

lemma replica_full_law_moment
    {Ω S : Type*} [MeasurableSpace Ω] [MeasurableSpace S]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (G : Kernel Ω S) [IsMarkovKernel G]
    {V : Ω × S → ℝ} (hV : Measurable V) {r : ℕ}
    {B : Ω × (Fin r → S) → ℝ} (hB : Measurable B)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ z, |B z| ≤ K)
    (k : ℕ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ z, replicaFullTest r k K L hK hL z ∂replicaFieldLaw ν G V B k) =
      ∫ ω, replicaNum G (fun z => replicaClip L (V z)) B ω *
        (replicaZ G (fun z => replicaClip L (V z)) ω)^k ∂ν := by
  have ht := (replicaFullTest r k K L hK hL).continuous.measurable
  have hm := measurable_replicaFieldView hV hB k
  have hi : Integrable (fun z => replicaFullTest r k K L hK hL (replicaFieldView V B k z))
      (ν ⊗ₘ replicaKernel G (r+k)) := by
    apply replica_integrable_of_bound (C := K*(Real.exp L)^(r+k)) (ht.comp hm)
    intro z
    change |replicaClip K _ * ∏ i : Fin (r+k), Real.exp (replicaClip L _)| ≤ _
    rw [abs_mul]
    exact mul_le_mul (abs_le.mpr (replicaClip_mem hK))
      (replica_exp_clip_product_bound L hL _) (abs_nonneg _) hK
  rw [replicaFieldLaw,integral_map hm.aemeasurable ht.aestronglyMeasurable,Measure.integral_compProd hi]
  apply integral_congr_ae
  filter_upwards [] with ω
  simp only [replicaKernel_apply]
  change (∫ xs, replicaClip K (B (ω,replicaFirst r k xs)) *
      ∏ i : Fin (r+k), Real.exp (replicaClip L (V (ω,xs i)))
      ∂Measure.pi (fun _ : Fin (r+k) => G ω)) = _
  simp_rw [replicaClip_eq_of_abs_le (hb _)]
  exact replica_integral_all_products (G ω) r k (fun xs => B (ω,xs))
    (fun x => Real.exp (replicaClip L (V (ω,x))))

theorem replicaLawContinuity : ReplicaLawContinuityStatement := by
  intro Ω S mΩ mS ν G hν hG V hV hExp r B hB hBb hLaw
  let := mΩ
  let := mS
  let := hν
  let := hG
  apply replicaTruncation Ω S mΩ mS ν G hν hG V hV hExp r B hB hBb
  · intro L k
    obtain ⟨ρ,ρ₀,hρ,ht⟩ := hLaw k
    have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ht
      (replicaTailTest r k ((L:ℝ)+1) (by positivity))).cauchySeq
    simp_rw [hρ,replica_tail_law_moment (ν _) (G _) (hV _) (hB _)] at h
    exact h
  · intro L k
    obtain ⟨K,hK⟩ := hBb
    let K' := max K 0
    have hK' : 0 ≤ K' := le_max_right _ _
    have hb : ∀ n z, |B n z| ≤ K' := fun n z => (hK n z).trans (le_max_left _ _)
    obtain ⟨ρ,ρ₀,hρ,ht⟩ := hLaw k
    have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp ht
      (replicaFullTest r k K' ((L:ℝ)+1) hK' (by positivity))).cauchySeq
    simp_rw [hρ,replica_full_law_moment (ν _) (G _) (hV _) (hB _) hK' (hb _)] at h
    exact h
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

def RowFiniteProfile.mesh {Q : ℝ} (P : RowFiniteProfile Q) (n : ℕ) : RowFiniteProfile Q where
  ranks := rowMeshRanks P.ranks (rankMesh n)
  ordered := rowMeshRanks_sorted _ _
  valid := rowMesh_valid _ _ P.valid (rankMesh_valid n)
  increment := rowMeshIncrement P.ranks (rankMesh n) P.increment
  root := P.root
  residual := P.residual
  diagonal := (congrArg (fun a : ℝ≥0 => (a:ℝ)) (rowMesh_diagonal P.ranks (rankMesh n) P.increment P.root P.residual P.ordered)).trans P.diagonal

lemma rowTestExtend_bound (φ : C(Set.Icc (0:ℝ) 1,ℝ)) (s : ℝ) :
    |rowTestExtend φ s| ≤ ‖φ‖ := by
  exact φ.norm_coe_le_norm _

lemma rowFullPair_mesh_bound {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    {Q : ℝ} (P : RowFiniteProfile Q) (φ : C(Set.Icc (0:ℝ) 1,ℝ)) (n : ℕ)
    (z : RowReplicaEnvironment (P.mesh n).ranks.length × (Fin 2 → RowReplicaSite (P.mesh n).ranks.length)) :
    |rowFullPair (P.mesh n).ranks u (rowMeshTest P.ranks φ n) z| ≤ ‖φ‖*L^2 := by
  unfold rowFullPair rowMeshTest
  rw [abs_mul,abs_mul]
  apply mul_le_mul (rowTestExtend_bound _ _) _ (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (norm_nonneg _)
  simpa only [sq] using mul_le_mul (hu.slope _) (hu.slope _) (abs_nonneg _) hu.L_nonneg

lemma measurable_rowFullPotential (ms : List ℝ) (u : ℝ → ℝ) (hu : Measurable u) :
    Measurable (rowFullPotential ms u) := hu.comp (measurable_rowReplicaSiteField _)

lemma measurable_rowFullPair (ms : List ℝ) (u : ℝ → ℝ) (hu : Measurable (deriv u)) (B : ℕ → ℝ) :
    Measurable (rowFullPair ms u B) := by
  let X := RowReplicaEnvironment ms.length × (Fin 2 → RowReplicaSite ms.length)
  have hp : Measurable (fun z : X => fun i : Fin 2 => (z.2 i).1) := by dsimp [X]; fun_prop
  have hB : Measurable (fun z : X => B (cascadeSharedEdges ms.length (z.2 0).1 (z.2 1).1)) :=
    ((measurable_of_countable (fun xs : Fin 2 → CascadePath ms.length =>
      B (cascadeSharedEdges ms.length (xs 0) (xs 1))))).comp hp
  have hf (i : Fin 2) : Measurable (fun z : X =>
      deriv u (rowReplicaSiteField ms.length (z.1,z.2 i))) := by
    exact hu.comp ((measurable_rowReplicaSiteField ms.length).comp (by dsimp [X]; fun_prop))
  exact hB.mul ((hf 0).mul (hf 1))

lemma rowMeshExpectation_converges
    (u : ℝ → ℝ) (L H : ℝ) (hu : ContDiff ℝ 2 u) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    (Q : ℝ) (P : ℕ → RowFiniteProfile Q) (q : SphericalProfile) (hq : q.val 1 ≤ Q)
    (hP : Tendsto (fun n => sphericalProfileDistance (P n).profile.val q.val) atTop (𝓝 0))
    (φ : C(Set.Icc (0:ℝ) 1,ℝ)) :
    ∃ b : ℝ, Tendsto (fun n => ∫ ω,
      replicaNum (rowReplicaKernel ((P n).mesh n).ranks ((P n).mesh n).residual)
        (rowFullPotential ((P n).mesh n).ranks u)
        (rowFullPair ((P n).mesh n).ranks u (rowMeshTest (P n).ranks φ n)) ω /
      (replicaZ (rowReplicaKernel ((P n).mesh n).ranks ((P n).mesh n).residual)
        (rowFullPotential ((P n).mesh n).ranks u) ω)^2
      ∂rowReplicaEnvironmentLaw ((P n).mesh n).ranks ((P n).mesh n).increment ((P n).mesh n).root)
      atTop (𝓝 b) := by
  have hud : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have ht : RowBoundedTerminal u L H := ⟨hu.differentiable (by norm_num),hud.differentiable (by norm_num),hL,hH,
    fun x => (hb x).1,fun x => (hb x).2⟩
  apply (replicaLawContinuity
    (fun n => RowReplicaEnvironment ((P n).mesh n).ranks.length)
    (fun n => RowReplicaSite ((P n).mesh n).ranks.length)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun n => rowReplicaEnvironmentLaw ((P n).mesh n).ranks ((P n).mesh n).increment ((P n).mesh n).root)
    (fun n => rowReplicaKernel ((P n).mesh n).ranks ((P n).mesh n).residual)
    (fun n => by unfold rowReplicaEnvironmentLaw; infer_instance) (fun _ => inferInstance)
    (fun n => rowFullPotential ((P n).mesh n).ranks u)
    (fun n => measurable_rowFullPotential _ _ hu.continuous.measurable)
    (rowUniformMoments ht Q (fun n => (P n).mesh n)) 2
    (fun n => rowFullPair ((P n).mesh n).ranks u (rowMeshTest (P n).ranks φ n))
    (fun n => measurable_rowFullPair _ _ hud.continuous.measurable _) ⟨‖φ‖*L^2,fun n z => rowFullPair_mesh_bound ht _ _ _ z⟩ ?_).2
  intro k
  obtain ⟨ρ,ρ₀,he,h₀,hlim⟩ := rowVariableMesh_fields_converge u L H hu hL hH hb Q P q hq hP φ k
  exact ⟨ρ,ρ₀,he,hlim⟩
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
lemma measurable_rankMeshValue (n : ℕ) : Measurable (rankMeshValue n) :=
  ((measurable_of_countable (fun k : ℕ => (k:ℝ))).comp (measurable_rpcStepLevel _)).div_const _

lemma RowFiniteProfile.test_fubini {Q : ℝ} (P : RowFiniteProfile Q)
    {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (B : ℝ → ℝ) (hB : Measurable B) {K : ℝ} (hb : ∀ s, |B s| ≤ K) :
    (∫ x, (∫ s in (0:ℝ)..1, B s *
      rowDerivativeDepthMoment (rowGaussianBlocks P.ranks P.increment)
        (gaussianRowOperator 1 P.residual u) (rpcStepLevel P.ranks s) x)
      ∂gaussianReal 0 P.root) =
    ∫ s in (0:ℝ)..1, B s * P.derivative u s := by
  have hv := rowBoundedOperator_terminal hu (by norm_num : (0:ℝ) ≤ 1) le_rfl (P.residual:ℝ)
  have hr := rowGaussianBlocks_valid P.ranks
    (fun m hm => ⟨(P.valid m hm).1.le,(P.valid m hm).2.le⟩) P.increment
  have hm := rowDepth_joint_measurable hv P.ranks
    (fun m hm => ⟨(P.valid m hm).1.le,(P.valid m hm).2.le⟩) P.increment
  have hi : Integrable (fun z : ℝ × ℝ => B z.2 *
      rowDerivativeDepthMoment (rowGaussianBlocks P.ranks P.increment)
        (gaussianRowOperator 1 P.residual u) (rpcStepLevel P.ranks z.2) z.1)
      ((gaussianReal 0 P.root).prod (volume.restrict (Set.Ioc (0:ℝ) 1))) := by
    apply Integrable.of_bound ((hB.comp measurable_snd).mul (hm.comp measurable_swap)).aestronglyMeasurable (K*L^2)
    apply Eventually.of_forall
    intro z
    dsimp only [Function.comp_apply,Pi.mul_apply,Prod.fst_swap,Prod.snd_swap]
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (rowDerivativeDepthMoment_bounds hv _ hr _ _).1]
    exact mul_le_mul (hb _) (rowDerivativeDepthMoment_bounds hv _ hr _ _).2
      (rowDerivativeDepthMoment_bounds hv _ hr _ _).1 ((abs_nonneg (B 0)).trans (hb 0))
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro s
  exact integral_const_mul _ _

lemma rowMeshExpectation_eq_test
    (u : ℝ → ℝ) (L H : ℝ) (hu : ContDiff ℝ 2 u) (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    {Q : ℝ} (P : RowFiniteProfile Q) (φ : C(Set.Icc (0:ℝ) 1,ℝ)) (n : ℕ) :
    (∫ ω, replicaNum (rowReplicaKernel (P.mesh n).ranks (P.mesh n).residual)
        (rowFullPotential (P.mesh n).ranks u)
        (rowFullPair (P.mesh n).ranks u (rowMeshTest P.ranks φ n)) ω /
      (replicaZ (rowReplicaKernel (P.mesh n).ranks (P.mesh n).residual)
        (rowFullPotential (P.mesh n).ranks u) ω)^2
      ∂rowReplicaEnvironmentLaw (P.mesh n).ranks (P.mesh n).increment (P.mesh n).root) =
    ∫ s in (0:ℝ)..1, rowTestExtend φ (rankMeshValue n s) * P.derivative u s := by
  have hud : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have ht : RowBoundedTerminal u L H := ⟨hu.differentiable (by norm_num),hud.differentiable (by norm_num),hL,hH,
    fun x => (hb x).1,fun x => (hb x).2⟩
  rw [rowResidualPair u L H hu hL hH hb _ (P.mesh n).ordered (P.mesh n).valid]
  simp only [RowFiniteProfile.mesh,rowMeshTest_transport,
    rowMesh_depth_invariant P.ranks (rankMesh n) P.ordered]
  exact P.test_fubini ht (fun s => rowTestExtend φ (rankMeshValue n s))
    ((rowTestExtend_continuous φ).measurable.comp (measurable_rankMeshValue n))
    (fun s => rowTestExtend_bound φ _)

lemma rowProfileTest_error_tendsto
    {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    {Q : ℝ} (P : ℕ → RowFiniteProfile Q) (φ : C(Set.Icc (0:ℝ) 1,ℝ)) :
    Tendsto (fun n => ∫ s in (0:ℝ)..1,
      (rowTestExtend φ s - rowTestExtend φ (rankMeshValue n s)) * (P n).derivative u s)
      atTop (𝓝 0) := by
  simp_rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  have hm (n : ℕ) : Measurable (fun s : ℝ =>
      (rowTestExtend φ s - rowTestExtend φ (rankMeshValue n s)) * (P n).derivative u s) :=
    ((rowTestExtend_continuous φ).measurable.sub
      ((rowTestExtend_continuous φ).measurable.comp (measurable_rankMeshValue n))).mul
      ((P n).derivative_measurable hu)
  have hb (n : ℕ) (s : ℝ) :
      ‖(rowTestExtend φ s-rowTestExtend φ (rankMeshValue n s)) * (P n).derivative u s‖ ≤ 2*‖φ‖*L^2 := by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((P n).derivative_bounds hu s).1]
    apply mul_le_mul _ ((P n).derivative_bounds hu s).2 ((P n).derivative_bounds hu s).1 (by positivity)
    calc
      _ ≤ |rowTestExtend φ s| + |rowTestExtend φ (rankMeshValue n s)| := abs_sub _ _
      _ ≤ _ := by linarith [rowTestExtend_bound φ s,rowTestExtend_bound φ (rankMeshValue n s)]
  have hl : ∀ᵐ s ∂volume.restrict (Set.Ioc (0:ℝ) 1),
      Tendsto (fun n => (rowTestExtend φ s-rowTestExtend φ (rankMeshValue n s)) * (P n).derivative u s)
        atTop (𝓝 0) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    have he := ((rowTestExtend_continuous φ).tendsto s).comp (rankMeshValue_tendsto ⟨hs.1.le,hs.2⟩)
    have hzero : Tendsto (fun n => |rowTestExtend φ s-rowTestExtend φ (rankMeshValue n s)| * L^2)
        atTop (𝓝 0) := by simpa using (((tendsto_const_nhds (x := rowTestExtend φ s)).sub he).abs.mul_const (L^2))
    apply squeeze_zero_norm (fun n => ?_) hzero
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg ((P n).derivative_bounds hu s).1]
    exact mul_le_mul_of_nonneg_left ((P n).derivative_bounds hu s).2 (abs_nonneg _)
  simpa using tendsto_integral_of_dominated_convergence (fun _ => 2*‖φ‖*L^2)
    (fun n => (hm n).aestronglyMeasurable) (integrable_const _) (fun n => Eventually.of_forall (hb n)) hl

lemma rowProfileTest_integrable {Q : ℝ} (P : RowFiniteProfile Q)
    {u : ℝ → ℝ} {L H : ℝ} (hu : RowBoundedTerminal u L H)
    (B : ℝ → ℝ) (hB : Measurable B) {K : ℝ} (hb : ∀ s, |B s| ≤ K) :
    IntervalIntegrable (fun s => B s*P.derivative u s) volume 0 1 := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (0:ℝ) ≤ 1)]
  apply Integrable.of_bound (hB.mul (P.derivative_measurable hu)).aestronglyMeasurable (K*L^2)
  apply Eventually.of_forall
  intro s
  dsimp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (P.derivative_bounds hu s).1]
  exact mul_le_mul (hb _) (P.derivative_bounds hu s).2 (P.derivative_bounds hu s).1
    ((abs_nonneg (B 0)).trans (hb 0))

theorem rowProfileTestConvergence : RowProfileTestConvergenceStatement := by
  intro u L H hu hL hH hb Q P q hq hP φ
  obtain ⟨b,hl⟩ := rowMeshExpectation_converges u L H hu hL hH hb Q P q hq hP φ
  simp_rw [rowMeshExpectation_eq_test u L H hu hL hH hb] at hl
  have hud : ContDiff ℝ 1 (deriv u) := hu.deriv'
  have ht : RowBoundedTerminal u L H := ⟨hu.differentiable (by norm_num),hud.differentiable (by norm_num),hL,hH,
    fun x => (hb x).1,fun x => (hb x).2⟩
  have he := rowProfileTest_error_tendsto ht P φ
  have hid (n : ℕ) : (∫ s in (0:ℝ)..1,
      (rowTestExtend φ s-rowTestExtend φ (rankMeshValue n s)) * (P n).derivative u s) =
      (∫ s in (0:ℝ)..1, rowTestExtend φ s*(P n).derivative u s) -
      (∫ s in (0:ℝ)..1, rowTestExtend φ (rankMeshValue n s)*(P n).derivative u s) := by
    simp_rw [sub_mul]
    apply intervalIntegral.integral_sub
    · exact rowProfileTest_integrable _ ht _ (rowTestExtend_continuous φ).measurable (rowTestExtend_bound φ)
    · exact rowProfileTest_integrable _ ht _ ((rowTestExtend_continuous φ).measurable.comp (measurable_rankMeshValue n))
        (fun s => rowTestExtend_bound φ _)
  simp_rw [hid] at he
  refine ⟨b,?_⟩
  convert he.add hl using 1 <;> simp
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming

lemma profileTest_lipschitz (p q : SphericalProfile) (φ : C(Set.Icc (0:ℝ) 1,ℝ)) :
    |(∫ s in (0:ℝ)..1, rowTestExtend φ s*p.val s) -
      (∫ s in (0:ℝ)..1, rowTestExtend φ s*q.val s)| ≤
      ‖φ‖ * sphericalProfileDistance p.val q.val := by
  have hp : IntervalIntegrable (fun s => rowTestExtend φ s*p.val s) volume 0 1 :=
    p.integrable.continuousOn_mul (rowTestExtend_continuous φ).continuousOn
  have hq : IntervalIntegrable (fun s => rowTestExtend φ s*q.val s) volume 0 1 :=
    q.integrable.continuousOn_mul (rowTestExtend_continuous φ).continuousOn
  rw [←intervalIntegral.integral_sub hp hq]
  calc
    _ ≤ ∫ s in (0:ℝ)..1, |rowTestExtend φ s*p.val s-rowTestExtend φ s*q.val s| :=
      intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ s in (0:ℝ)..1, ‖φ‖*|p.val s-q.val s| := by
      apply intervalIntegral.integral_mono_on (by norm_num) (hp.sub hq).abs ((p.integrable.sub q.integrable).abs.const_mul _)
      intro s hs
      rw [←mul_sub,abs_mul]
      exact mul_le_mul_of_nonneg_right (rowTestExtend_bound φ s) (abs_nonneg _)
    _ = _ := intervalIntegral.integral_const_mul _ _

lemma profileTest_tendsto_of_L1 {ι : Type*} {l : Filter ι}
    (pn : ι → SphericalProfile) (p : SphericalProfile) (φ : C(Set.Icc (0:ℝ) 1,ℝ))
    (hh : Tendsto (fun i => sphericalProfileDistance (pn i).val p.val) l (𝓝 0)) :
    Tendsto (fun i => ∫ s in (0:ℝ)..1, rowTestExtend φ s*(pn i).val s) l
      (𝓝 (∫ s in (0:ℝ)..1, rowTestExtend φ s*p.val s)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  simp only [Real.dist_eq]
  exact squeeze_zero (fun _ => abs_nonneg _) (fun i => profileTest_lipschitz (pn i) p φ)
    (by simpa using hh.const_mul ‖φ‖)

lemma profileTest_closed (p : SphericalProfile) (φ : C(Set.Icc (0:ℝ) 1,ℝ)) :
    (∫ s in (0:ℝ)..1, rowTestExtend φ s*p.val s) =
      ∫ s in Set.Icc (0:ℝ) 1, rowTestExtend φ s*rowClosedProfile p s := by
  rw [intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  dsimp only
  rw [rowClosedProfile_eq p hs]

lemma profile_ae_eq_of_tests (p q : SphericalProfile)
    (h : ∀ φ : C(Set.Icc (0:ℝ) 1,ℝ),
      (∫ s in (0:ℝ)..1, rowTestExtend φ s*p.val s) =
      ∫ s in (0:ℝ)..1, rowTestExtend φ s*q.val s) :
    rowClosedProfile p =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)] rowClosedProfile q := by
  let μ := volume.restrict (Set.Icc (0:ℝ) 1)
  have hm (p : SphericalProfile) : Measurable (fun s => ENNReal.ofReal (rowClosedProfile p s)) :=
    (measurable_rowClosedProfile p).ennreal_ofReal
  have hfinite (p : SphericalProfile) : ∫⁻ s, ENNReal.ofReal (rowClosedProfile p s) ∂μ ≠ ⊤ :=
    (lintegral_ofReal_ne_top_iff_integrable (measurable_rowClosedProfile p).aestronglyMeasurable
      (Eventually.of_forall fun s => (rowClosedProfile_bound p s).1)).mpr (rowClosedProfile_integrable p)
  let := isFiniteMeasure_withDensity (hfinite p)
  let := isFiniteMeasure_withDensity (hfinite q)
  have hμ : μ.withDensity (fun s => ENNReal.ofReal (rowClosedProfile p s)) =
      μ.withDensity (fun s => ENNReal.ofReal (rowClosedProfile q s)) := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_withDensity_eq_integral_toReal_smul (hm p) (Eventually.of_forall fun s => ENNReal.ofReal_lt_top) f,
      integral_withDensity_eq_integral_toReal_smul (hm q) (Eventually.of_forall fun s => ENNReal.ofReal_lt_top) f]
    simp only [ENNReal.toReal_ofReal (rowClosedProfile_bound _ _).1,smul_eq_mul]
    let φ : C(Set.Icc (0:ℝ) 1,ℝ) := f.toContinuousMap.comp ⟨Subtype.val,continuous_subtype_val⟩
    have he (p : SphericalProfile) : (∫ s, rowClosedProfile p s*f s ∂μ) =
        ∫ s in (0:ℝ)..1, rowTestExtend φ s*p.val s := by
      rw [profileTest_closed]
      apply setIntegral_congr_fun measurableSet_Icc
      intro s hs
      dsimp only
      rw [show rowTestExtend φ s = f s by exact rowTestExtend_eq φ ⟨s,hs⟩]
      exact mul_comm _ _
    rw [he p,he q,h φ]
  have he := (withDensity_eq_iff (hm p).aemeasurable (hm q).aemeasurable (hfinite p)).mp hμ
  filter_upwards [he] with s hs
  simpa only [ENNReal.toReal_ofReal (rowClosedProfile_bound _ _).1] using congrArg ENNReal.toReal hs

lemma profileDistance_eq_zero_of_tests (p q : SphericalProfile)
    (h : ∀ φ : C(Set.Icc (0:ℝ) 1,ℝ),
      (∫ s in (0:ℝ)..1, rowTestExtend φ s*p.val s) =
      ∫ s in (0:ℝ)..1, rowTestExtend φ s*q.val s) :
    sphericalProfileDistance p.val q.val = 0 := by
  rw [sphericalProfileDistance,intervalIntegral.integral_of_le zero_le_one,←integral_Icc_eq_integral_Ioc]
  have he := profile_ae_eq_of_tests p q h
  have hz : (fun s => |p.val s-q.val s|) =ᵐ[volume.restrict (Set.Icc (0:ℝ) 1)] 0 := by
    filter_upwards [he,ae_restrict_mem measurableSet_Icc] with s hs hsm
    rw [rowClosedProfile_eq p hsm,rowClosedProfile_eq q hsm] at hs
    simp [hs]
  rw [integral_congr_ae hz]
  simp
end MicroscopicJamming

end

end OAI
