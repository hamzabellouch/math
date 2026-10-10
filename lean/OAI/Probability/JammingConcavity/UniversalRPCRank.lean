import Mathlib
import OAI.Probability.JammingConcavity.SpherePressure

namespace OAI

/-! Universal R P C Rank. -/

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
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace MicroscopicJamming

lemma realizedRankLaw_reindex (p : Equiv.Perm ℕ) :
    realizedRankLaw.map (rankReindex p)=realizedRankLaw := by
  let : IsProbabilityMeasure (realizedRankLaw.map (rankReindex p)) := inferInstance
  have hb : ∀ᵐ U ∂realizedRankLaw, ∀ i j, 0≤U i j ∧ U i j≤1 :=
    realizedRankLaw_constraints.mono fun U hU => hU.2.2.1
  have hd : ∀ᵐ U ∂realizedRankLaw, ∀ i, U i i=1 :=
    realizedRankLaw_constraints.mono fun U hU => hU.1
  have hb' : ∀ᵐ U ∂realizedRankLaw.map (rankReindex p), ∀ i j, 0≤U i j ∧ U i j≤1 := by
    apply (ae_map_iff (measurable_rankReindex p).aemeasurable ?_).mpr
    · exact hb.mono fun U hU i j => hU (p i) (p j)
    · simp only [ofPred_forall,ofPred_and]
      exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
        (measurableSet_le measurable_const (by fun_prop)).inter
          (measurableSet_le (by fun_prop) measurable_const)
  have hd' : ∀ᵐ U ∂realizedRankLaw.map (rankReindex p), ∀ i, U i i=1 := by
    apply (ae_map_iff (measurable_rankReindex p).aemeasurable ?_).mpr
    · exact hd.mono fun U hU i => hU (p i)
    · simp only [ofPred_forall]
      exact MeasurableSet.iInter fun i => measurableSet_eq_fun (by fun_prop) measurable_const
  exact rpcRankLaw_unique _ _ hb' hb hd' hd
    (hasRPCFiniteRankLaws_reindex realizedRankLaw_rpc p) realizedRankLaw_rpc

lemma realizedRankLaw_positive (q : ℝ → ℝ) (Q : ℝ) (hq : Monotone q)
    (hq0 : 0≤q 0) (hQ : q 1≤Q) :
    ∀ᵐ U ∂realizedRankLaw, ∀ n (a : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, a i*a j*(if i=j then Q else q (U i j)) := by
  filter_upwards [realizedRankLaw_constraints] with U hU
  intro n a
  exact rpcRankPositive n (fun i j => U i j)
    ⟨fun i => hU.1 i,fun i j => hU.2.1 i j,
      fun i j => hU.2.2.1 i j,fun i j k => hU.2.2.2 i j k⟩ q Q hq hq0 hQ a

 

theorem universalRPCRank : UniversalRPCRankStatement := by
  refine ⟨⟨realizedRankLaw,inferInstance,realizedRankLaw_constraints,?_,
    realizedRankLaw_uniform,realizedRankLaw_rpc,realizedRankLaw_positive⟩,?_⟩
  · exact realizedRankLaw_reindex
  · intro μ ν hμ hν hbμ hbν hdμ hdν hrμ hrν
    let := hμ
    let := hν
    exact rpcRankLaw_unique μ ν hbμ hbν hdμ hdν hrμ hrν
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators Matrix MatrixOrder

open Classical
namespace MicroscopicJamming

lemma rowClosedProfile_eq (p : SphericalProfile) {s : ℝ} (hs : s ∈ Set.Icc (0:ℝ) 1) :
    rowClosedProfile p s = p.val s := by
  simp [rowClosedProfile,max_eq_right hs.1,min_eq_right hs.2]
lemma rowClosedProfile_monotone (p : SphericalProfile) : Monotone (rowClosedProfile p) := by
  intro s t hst
  apply p.mono
  · exact ⟨le_min zero_le_one (le_max_left _ _),min_le_left _ _⟩
  · exact ⟨le_min zero_le_one (le_max_left _ _),min_le_left _ _⟩
  · exact min_le_min_left _ (max_le_max_left _ hst)
lemma measurable_rowClosedProfile (p : SphericalProfile) : Measurable (rowClosedProfile p) :=
  (rowClosedProfile_monotone p).measurable
lemma rowClosedProfile_bound (p : SphericalProfile) (s : ℝ) :
    0 ≤ rowClosedProfile p s ∧ rowClosedProfile p s ≤ p.val 1 :=
  p.bound _ ⟨le_min zero_le_one (le_max_left _ _),min_le_left _ _⟩

lemma rank_pair_permutation (i j : ℕ) (hij : i ≠ j) :
    ∃ e : Equiv.Perm ℕ, e 0=i ∧ e 1=j := by
  let a := Equiv.swap 0 i
  have hi : i ≠ a 1 := by
    rw [← show a 0=i from Equiv.swap_apply_left _ _]
    exact fun h => by have := a.injective h; omega
  let b := Equiv.swap (a 1) j
  refine ⟨a.trans b,?_,?_⟩
  · change b (a 0)=i
    rw [show a 0=i from Equiv.swap_apply_left _ _]
    exact Equiv.swap_apply_of_ne_of_ne hi hij
  · exact Equiv.swap_apply_left _ _

lemma realizedRankLaw_pair_uniform (i j : ℕ) (hij : i ≠ j) :
    realizedRankLaw.map (fun U => U i j) = volume.restrict (Set.Icc (0:ℝ) 1) := by
  obtain ⟨e,he0,he1⟩ := rank_pair_permutation i j hij
  calc
    _ = (realizedRankLaw.map (rankReindex e)).map (fun U => U 0 1) := by
      rw [Measure.map_map (by fun_prop) (measurable_rankReindex e)]
      congr 1
      funext U
      simp [rankReindex,he0,he1]
    _ = _ := by rw [realizedRankLaw_reindex,realizedRankLaw_uniform]

lemma measurable_rowFullRankCovariance (r : ℕ) (Q : ℝ) (p : SphericalProfile) :
    Measurable (rowFullRankCovariance r Q p) := by
  change @Measurable RankArray (Fin r → Fin r → ℝ) _ (borel _) _
  rw [← (Pi.borelSpace (X := fun _ : Fin r => Fin r → ℝ)).measurable_eq]
  apply Measurable.of_eval; intro i
  apply Measurable.of_eval; intro j
  by_cases h : i=j
  · simp [rowFullRankCovariance,h]
  · simpa [rowFullRankCovariance,h,Function.comp_def] using (measurable_rowClosedProfile p).comp
      (show Measurable (fun U : RankArray => U i.val j.val) from by fun_prop)

lemma rowFullRankCovariance_psd (r : ℕ) (Q : ℝ) (p : SphericalProfile) (hQ : p.val 1 ≤ Q) :
    ∀ᵐ U ∂realizedRankLaw, (rowFullRankCovariance r Q p U).PosSemidef := by
  have hq0 : 0 ≤ rowClosedProfile p 0 := (rowClosedProfile_bound p 0).1
  have hq1 : rowClosedProfile p 1 ≤ Q := (rowClosedProfile_bound p 1).2.trans hQ
  filter_upwards [realizedRankLaw_constraints,
    realizedRankLaw_positive _ Q (rowClosedProfile_monotone p) hq0 hq1] with U hU hP
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  refine ⟨?_,fun a => ?_⟩
  · apply Matrix.IsHermitian.ext
    intro i j
    simp [rowFullRankCovariance,eq_comm,hU.2.1]
  · have h := hP r a
    simpa only [dotProduct,Matrix.mulVec,star_trivial,Pi.star_apply,
      rowFullRankCovariance,Finset.mul_sum,mul_assoc,mul_comm,mul_left_comm] using h
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

lemma pi_prod_pair_map {I A B : Type*} [Fintype I] [MeasurableSpace A] [MeasurableSpace B]
    (μ : I → Measure A) (ν : I → Measure B) [∀ i, IsProbabilityMeasure (μ i)]
    [∀ i, IsProbabilityMeasure (ν i)] :
    ((Measure.pi μ).prod (Measure.pi ν)).map (fun z i => (z.1 i,z.2 i)) =
      Measure.pi (fun i => (μ i).prod (ν i)) := by
  symm
  apply Measure.pi_eq_generateFrom (fun _ => generateFrom_prod) (fun _ => isPiSystem_prod)
    (fun i => (μ i).toFiniteSpanningSetsIn.prod (ν i).toFiniteSpanningSetsIn)
  intro s hs
  choose a ha b hb hab using hs
  rw [← funext hab]
  rw [Measure.map_apply (by fun_prop) (MeasurableSet.univ_pi (fun i => (ha i).prod (hb i)))]
  have he : (fun z : (I → A) × (I → B) => fun i => (z.1 i,z.2 i)) ⁻¹'
      univ.pi (fun i => a i ×ˢ b i) = (univ.pi a) ×ˢ (univ.pi b) := by
    ext z
    simp only [Set.mem_preimage, mem_univ_pi, mem_prod]
    exact forall_and
  rw [he, Measure.prod_prod, Measure.pi_pi, Measure.pi_pi, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  exact (Measure.prod_prod _ _).symm
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

lemma lintegral_cascadeFiniteReplicaLaw (ms : List ℝ) (r : ℕ)
    (f : (Fin r → CascadePath ms.length) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ xs, f xs ∂cascadeFiniteReplicaLaw ms r) =
      ∫⁻ ω, ∫⁻ xs, f xs ∂Measure.pi (fun _ : Fin r => cascadeLeafLaw ms ω) ∂cascadeLaw ms := by
  have hp : Measurable (fun x : ℕ → CascadePath ms.length => fun i : Fin r => x i.val) := by fun_prop
  rw [cascadeFiniteReplicaLaw, lintegral_map hf hp]
  rw [cascadeReplicaLaw, Measure.lintegral_bind (m := cascadeLaw ms)
    (f := fun a : ℕ → CascadePath ms.length => f (fun i : Fin r => a i.val))
    (measurable_cascadeReplicaKernel ms).aemeasurable (by exact (hf.comp hp).aemeasurable)]
  apply lintegral_congr
  intro ω
  let := cascadeLeafLaw_probability ms ω
  rw [← iid_prefix_map (cascadeLeafLaw ms ω) r, lintegral_map hf hp]

lemma measurable_rootPathField_pair (k : ℕ) :
    Measurable (fun z : CascadePath k × (Option (CascadeMarkIndex k) → ℝ) => rootPathField k z.2 z.1) := by
  apply measurable_from_prod_countable_right
  intro ℓ
  change Measurable (fun z : Option (CascadeMarkIndex k) → ℝ =>
    z none + ∑ j : Fin k, z (some (cascadePathIndex k ℓ j)))
  exact (measurable_pi_apply none).add (Finset.measurable_sum _ fun j _ => measurable_pi_apply _)

lemma measurable_rowReplicaSiteField (k : ℕ) : Measurable (rowReplicaSiteField k) := by
  unfold rowReplicaSiteField
  exact ((measurable_rootPathField_pair k).comp
    ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_fst))).add
      (measurable_snd.comp measurable_snd)

lemma measurable_rowReplicaKernelView (k r : ℕ) : Measurable (rowReplicaKernelView k r) := by
  unfold rowReplicaKernelView
  apply Measurable.prodMk
  · exact (measurable_of_countable (cascadeGenealogySignature k r)).comp (by fun_prop)
  · apply (WithLp.measurable_toLp 2 _).comp
    apply Measurable.of_eval
    intro i
    exact (measurable_rowReplicaSiteField k).comp
      (measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd))
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

def rowReplicaRearrange (k r : ℕ) (z : RowReplicaEnvironment k × (Fin r → RowReplicaSite k)) :
    (Fin r → CascadePath k) × ((Option (CascadeMarkIndex k) → ℝ) × (Fin r → ℝ)) :=
  (fun i => (z.2 i).1, z.1.2, fun i => (z.2 i).2)

lemma measurable_rowReplicaRearrange (k r : ℕ) : Measurable (rowReplicaRearrange k r) := by
  unfold rowReplicaRearrange
  fun_prop

lemma rowReplicaRearrangement_law (ms : List ℝ) (r : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) :
    ((rowReplicaEnvironmentLaw ms d p₀) ⊗ₘ replicaKernel (rowReplicaKernel ms Δ) r).map
      (rowReplicaRearrange ms.length r) =
      (cascadeFiniteReplicaLaw ms r).prod
        ((Measure.infinitePi (fun a => gaussianReal 0 (rootCoordinateVariance ms.length d p₀ a))).prod
          (Measure.pi (fun _ : Fin r => gaussianReal 0 Δ))) := by
  let Z := Option (CascadeMarkIndex ms.length) → ℝ
  let ν : Measure Z := Measure.infinitePi (fun a => gaussianReal 0 (rootCoordinateVariance ms.length d p₀ a))
  let ρ := Measure.pi (fun _ : Fin r => gaussianReal 0 Δ)
  have : IsProbabilityMeasure (rowReplicaEnvironmentLaw ms d p₀) := by
    unfold rowReplicaEnvironmentLaw
    infer_instance
  apply Measure.ext_of_lintegral
  intro f hf
  have hT := measurable_rowReplicaRearrange ms.length r
  have hft : Measurable (fun z => f (rowReplicaRearrange ms.length r z)) := hf.comp hT
  rw [lintegral_map hf hT, Measure.lintegral_compProd hft]
  change (∫⁻ z, ∫⁻ xs, f (rowReplicaRearrange ms.length r (z,xs))
    ∂replicaKernel (rowReplicaKernel ms Δ) r z ∂(cascadeLaw ms).prod ν) = _
  rw [lintegral_prod _ hft.lintegral_kernel_prod_right'.aemeasurable]
  have hi (ω : CascadeTree ms.length) (z : Z) :
      (∫⁻ xs, f (rowReplicaRearrange ms.length r ((ω,z),xs))
        ∂replicaKernel (rowReplicaKernel ms Δ) r (ω,z)) =
      ∫⁻ xs, ∫⁻ y, f (xs,z,y) ∂ρ ∂Measure.pi (fun _ : Fin r => cascadeLeafLaw ms ω) := by
    let := cascadeLeafLaw_probability ms ω
    rw [replicaKernel_apply]
    change (∫⁻ xs, f (rowReplicaRearrange ms.length r ((ω,z),xs))
      ∂Measure.pi (fun _ : Fin r => (cascadeLeafLaw ms ω).prod (gaussianReal 0 Δ))) = _
    rw [← pi_prod_pair_map (fun _ : Fin r => cascadeLeafLaw ms ω) (fun _ : Fin r => gaussianReal 0 Δ)]
    rw [lintegral_map (show Measurable (fun xs : Fin r → CascadePath ms.length × ℝ =>
      f (rowReplicaRearrange ms.length r ((ω,z),xs))) from hft.comp measurable_prodMk_left)
      (show Measurable (fun t : (Fin r → CascadePath ms.length) × (Fin r → ℝ) =>
        fun i => (t.1 i,t.2 i)) from by fun_prop)]
    change (∫⁻ xy, f (xy.1,z,xy.2) ∂(Measure.pi (fun _ : Fin r => cascadeLeafLaw ms ω)).prod ρ) = _
    exact lintegral_prod _ (by exact (hf.comp (by fun_prop)).aemeasurable)
  simp_rw [hi]
  rw [lintegral_prod _ hf.aemeasurable]
  have hinner : Measurable (fun xs : Fin r → CascadePath ms.length => ∫⁻ zy, f (xs,zy) ∂ν.prod ρ) :=
    hf.lintegral_prod_right'
  rw [lintegral_cascadeFiniteReplicaLaw ms r _ hinner]
  apply lintegral_congr
  intro ω
  let := cascadeLeafLaw_probability ms ω
  have hs : Measurable (fun zx : Z × (Fin r → CascadePath ms.length) => ∫⁻ y, f (zx.2,zx.1,y) ∂ρ) :=
    (hf.comp (by fun_prop : Measurable (fun w : (Z × (Fin r → CascadePath ms.length)) × (Fin r → ℝ) =>
      (w.1.2,w.1.1,w.2)))).lintegral_prod_right'
  rw [lintegral_lintegral_swap hs.aemeasurable]
  apply lintegral_congr
  intro xs
  exact (lintegral_prod _ (hf.comp measurable_prodMk_left).aemeasurable).symm
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

lemma rowPathAgree_iff_shared (k j : ℕ) (a b : CascadePath k) (hj : j ≤ k) :
    pathAgree k j a b ↔ j ≤ cascadeSharedEdges k a b := by
  induction k generalizing j with
  | zero => have e : j=0 := by omega
            subst j
            simp [pathAgree,cascadeSharedEdges]
  | succ k ih =>
    cases j with
    | zero => simp [pathAgree]
    | succ j =>
      have h : j≤k := by omega
      by_cases he : a.1=b.1
      · simp only [pathAgree,cascadeSharedEdges,he,ite_true,true_and]
        rw [ih j a.2 b.2 h]
        omega
      · simp [pathAgree,cascadeSharedEdges,he]

lemma rowReplicaResidualCovariance_signature (k r : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0)
    (xs : Fin r → CascadePath k) :
    rowReplicaResidualCovariance k r d p₀ Δ xs =
      rowSignatureCovariance k r d p₀ Δ (cascadeGenealogySignature k r xs) := by
  ext i j
  simp only [rowReplicaResidualCovariance,Matrix.add_apply,Matrix.diagonal_apply,
    rowReplicaCovariance,rowSignatureCovariance,cascadeGenealogySignature]
  congr 2
  apply Finset.sum_congr rfl
  intro a _
  rw [rowPathAgree_iff_shared k (a.val+1) (xs i) (xs j) (by omega)]
  split_ifs with h <;> simp only [h, ite_true, ite_false]

lemma measurable_rankGenealogySignature (ms : List ℝ) (r : ℕ) :
    Measurable (rankGenealogySignature ms r) := by
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  unfold rankGenealogySignature
  split_ifs
  · exact measurable_const
  · exact (measurable_rpcStepLevel ms).comp ((measurable_pi_apply j.val).comp (measurable_pi_apply i.val))

lemma rowRankSignature_law (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) (r : ℕ) :
    realizedRankLaw.map (rankGenealogySignature ms r) =
      (cascadeFiniteReplicaLaw ms r).map (cascadeGenealogySignature ms.length r) := by
  let decode : RankArray → RowRankSignature r :=
    fun U i j => if i=j then ms.length else ⌊U i.val j.val⌋₊
  have hd : Measurable decode := by
    apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    unfold decode
    split_ifs
    · exact measurable_const
    · fun_prop
  have h := realizedRankLaw_rpc ms hms h01 (fun j => (j:ℝ)) (ms.length+1)
    (by norm_num) (by intro i j hij hj; exact_mod_cast hij) (by norm_num)
  have hm := congrArg (Measure.map decode) h
  rw [Measure.map_map hd (measurable_rankCovarianceArray _ _ _),
    Measure.map_map hd (measurable_cascadeCovarianceArray _ _ _)] at hm
  have hr : decode ∘ rankCovarianceArray ms (fun j => (j:ℝ)) (ms.length+1) =
      rankGenealogySignature ms r := by
    funext U i j
    by_cases hij : i=j
    · simp [decode,rankGenealogySignature,hij]
    · have hne : i.val ≠ j.val := fun e => hij (Fin.ext e)
      simp [decode,rankCovarianceArray,rankGenealogySignature,hij,hne]
  have hc : decode ∘ cascadeCovarianceArray ms (fun j => (j:ℝ)) (ms.length+1) =
      cascadeGenealogySignature ms.length r ∘ (fun x i => x i.val) := by
    funext xs i j
    by_cases hij : i=j
    · simp [decode,cascadeGenealogySignature,hij,cascadeSharedEdges_self]
    · have hne : i.val ≠ j.val := fun e => hij (Fin.ext e)
      simp [decode,cascadeCovarianceArray,cascadeGenealogySignature,hij,hne]
  rw [hr,hc] at hm
  rw [cascadeFiniteReplicaLaw,Measure.map_map (measurable_of_countable _) (by fun_prop)]
  exact hm
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators RealInnerProductSpace

open Classical
namespace MicroscopicJamming

lemma gaussianLinear_law {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (B : Matrix I A ℝ) :
    (Measure.pi (fun _ : A => gaussianReal 0 1)).map
      (fun z => WithLp.toLp 2 (B.mulVec z)) =
      multivariateGaussian 0 (B * B.transpose) := by
  classical
  have hB : (B * B.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_self_mul_conjTranspose B
  have hm : Measurable (fun z : A → ℝ => WithLp.toLp 2 (B.mulVec z)) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  let : IsProbabilityMeasure ((Measure.pi (fun _ : A => gaussianReal 0 1)).map
      (fun z => WithLp.toLp 2 (B.mulVec z))) := inferInstance
  apply Measure.ext_of_charFun
  funext t
  have he (z : A → ℝ) :
      inner ℝ (WithLp.toLp 2 (B.mulVec z)) t =
      inner ℝ (WithLp.toLp 2 z) (WithLp.toLp 2 (B.transpose.mulVec t)) := by
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have hc : charFun ((Measure.pi (fun _ : A => gaussianReal 0 1)).map
      (fun z => WithLp.toLp 2 (B.mulVec z))) t =
      charFun (stdGaussian (EuclideanSpace ℝ A)) (WithLp.toLp 2 (B.transpose.mulVec t)) := by
    rw [← map_pi_eq_stdGaussian]
    simp only [charFun_apply]
    rw [integral_map hm.aemeasurable (by fun_prop), integral_map (by fun_prop) (by fun_prop)]
    simp_rw [he]
  have hn : ‖WithLp.toLp 2 (B.transpose.mulVec t)‖ ^ 2 =
      t.ofLp ⬝ᵥ (B * B.transpose).mulVec t.ofLp := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
    rw [← Matrix.mulVec_mulVec]
    rw [Matrix.dotProduct_mulVec t.ofLp B (B.transpose.mulVec t.ofLp)]
    rw [Matrix.mulVec_transpose]
  rw [hc, charFun_stdGaussian, charFun_multivariateGaussian hB, ← Complex.ofReal_pow, hn]
  simp only [inner_zero_right, Complex.ofReal_zero, zero_mul, zero_sub]
  norm_cast
  ring_nf
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal Topology BigOperators

namespace MicroscopicJamming
lemma pi_gaussian_scale {A : Type*} [Fintype A] (v : A → ℝ≥0) :
    (Measure.pi (fun _ : A => gaussianReal 0 1)).map (fun z i => Real.sqrt (v i:ℝ)*z i) =
      Measure.pi (fun i => gaussianReal 0 (v i)) := by
  rw [Measure.pi_map_pi (fun i => by fun_prop)]
  congr 1
  funext i
  rw [gaussianReal_map_const_mul, mul_zero, mul_one]
  have hs : (NNReal.mk (Real.sqrt (v i:ℝ)^2) (sq_nonneg _) : ℝ≥0) = v i :=
    Subtype.ext (Real.sq_sqrt (v i).coe_nonneg)
  rw [hs]

lemma pi_map_curry {A B : Type*} [Fintype A] [Fintype B] (μ : A → B → Measure ℝ)
    [∀ a b, IsProbabilityMeasure (μ a b)] :
    (Measure.pi (fun p : A × B => μ p.1 p.2)).map
      (MeasurableEquiv.curry A B ℝ) = Measure.pi (fun a => Measure.pi (μ a)) := by
  simpa only [Measure.infinitePi_eq_pi] using Measure.infinitePi_map_curry μ

def gaussianCoordinateRealization {A : Type*} [Fintype A] (N : ℕ)
    (e : Fin (Fintype.card (A × Fin N)) ≃ A × Fin N) (v : A → ℝ≥0)
    (z : Fin (Fintype.card (A × Fin N)) → ℝ) : A → Fin N → ℝ :=
  fun a j => Real.sqrt (v a:ℝ)*z (e.symm (a,j))

lemma measurable_gaussianCoordinateRealization {A : Type*} [Fintype A] (N : ℕ)
    (e : Fin (Fintype.card (A × Fin N)) ≃ A × Fin N) (v : A → ℝ≥0) :
    Measurable (gaussianCoordinateRealization N e v) := by
  unfold gaussianCoordinateRealization
  fun_prop

lemma gaussianCoordinateRealization_law {A : Type*} [Fintype A] (N : ℕ)
    (e : Fin (Fintype.card (A × Fin N)) ≃ A × Fin N) (v : A → ℝ≥0) :
    (Measure.pi (fun _ : Fin (Fintype.card (A × Fin N)) => gaussianReal 0 1)).map
      (gaussianCoordinateRealization N e v) =
      Measure.pi (fun a => Measure.pi (fun _ : Fin N => gaussianReal 0 (v a))) := by
  have he : gaussianCoordinateRealization N e v =
      (MeasurableEquiv.curry A (Fin N) ℝ) ∘
        (MeasurableEquiv.piCongrLeft (fun _ : A × Fin N => ℝ) e) ∘
          (fun z i => Real.sqrt (v (e i).1:ℝ)*z i) := by
    ext z a j
    simp [gaussianCoordinateRealization, MeasurableEquiv.curry, MeasurableEquiv.piCongrLeft,
      Equiv.piCongrLeft]
  rw [he, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_map (by fun_prop) (by fun_prop), pi_gaussian_scale,
    Measure.pi_map_piCongrLeft e (fun p : A × Fin N => gaussianReal 0 (v p.1)), pi_map_curry (fun a (_ : Fin N) => gaussianReal 0 (v a))]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators RealInnerProductSpace

open Classical
namespace MicroscopicJamming

def weightedGaussianMatrix {A I : Type*} (B : Matrix I A ℝ) (v : A → ℝ≥0) : Matrix I A ℝ :=
  fun i a => B i a * Real.sqrt (v a:ℝ)

lemma gaussianWeightedLinear_law {A I : Type*} [Fintype A] [Fintype I] [DecidableEq I]
    (B : Matrix I A ℝ) (v : A → ℝ≥0) :
    (Measure.pi (fun a => gaussianReal 0 (v a))).map
      (fun z => WithLp.toLp 2 (B.mulVec z)) =
      multivariateGaussian 0 (weightedGaussianMatrix B v * (weightedGaussianMatrix B v).transpose) := by
  have hm : Measurable (fun z : A → ℝ => WithLp.toLp 2 (B.mulVec z)) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  rw [← pi_gaussian_scale v, Measure.map_map hm (by fun_prop)]
  have he : (fun z : A → ℝ => WithLp.toLp 2 (B.mulVec z)) ∘
      (fun z a => Real.sqrt (v a:ℝ)*z a) =
      (fun z => WithLp.toLp 2 ((weightedGaussianMatrix B v).mulVec z)) := by
    funext z
    change WithLp.toLp 2 (B.mulVec (fun a => Real.sqrt (v a:ℝ)*z a)) = _
    apply congrArg (WithLp.toLp 2)
    funext i
    simp only [Matrix.mulVec,dotProduct,weightedGaussianMatrix,mul_assoc]
  rw [he,gaussianLinear_law]

lemma weightedGaussianMatrix_gram {A I : Type*} [Fintype A]
    (B : Matrix I A ℝ) (v : A → ℝ≥0) (i j : I) :
    (weightedGaussianMatrix B v * (weightedGaussianMatrix B v).transpose) i j =
      ∑ a, (v a:ℝ)*B i a*B j a := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,weightedGaussianMatrix]
  apply Finset.sum_congr rfl
  intro a _
  calc
    _ = (Real.sqrt (v a:ℝ)*Real.sqrt (v a:ℝ))*B i a*B j a := by ring
    _ = _ := by rw [Real.mul_self_sqrt (v a).coe_nonneg]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

def rowReplicaSupport (k r : ℕ) (xs : Fin r → CascadePath k) : Finset (CascadePath k) :=
  Finset.univ.image xs

def rowReplicaLeaf (k r : ℕ) (xs : Fin r → CascadePath k) (i : Fin r) : rowReplicaSupport k r xs :=
  ⟨xs i, Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩⟩

def rowReplicaMatrix (k r : ℕ) (xs : Fin r → CascadePath k) :
    Matrix (Fin r) (cascadeCoordinateSet k (rowReplicaSupport k r xs)) ℝ :=
  fun i a => ∑ b : Fin (k+1), if finiteRootPathIndex k (rowReplicaSupport k r xs)
    (rowReplicaLeaf k r xs i) b = a then 1 else 0

lemma rowReplicaMatrix_mulVec (k r : ℕ) (xs : Fin r → CascadePath k)
    (z : cascadeCoordinateSet k (rowReplicaSupport k r xs) → ℝ) (i : Fin r) :
    (rowReplicaMatrix k r xs).mulVec z i =
      finiteRootPathField k (rowReplicaSupport k r xs) z (rowReplicaLeaf k r xs i) := by
  simp only [rowReplicaMatrix,Matrix.mulVec,dotProduct,finiteRootPathField,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp

lemma rowReplicaMatrix_gram (k r : ℕ) (xs : Fin r → CascadePath k)
    (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) :
    let v := fun a : cascadeCoordinateSet k (rowReplicaSupport k r xs) =>
      rootCoordinateVariance k d p₀ a.val
    weightedGaussianMatrix (rowReplicaMatrix k r xs) v *
      (weightedGaussianMatrix (rowReplicaMatrix k r xs) v).transpose =
      rowReplicaCovariance k r d p₀ xs := by
  intro v
  ext i j
  rw [weightedGaussianMatrix_gram]
  have h := finiteRoot_incidence_covariance k (rowReplicaSupport k r xs) d (fun _ => 0) p₀ 0
    (rowReplicaLeaf k r xs i) (rowReplicaLeaf k r xs j)
  have hz (a : Option (CascadeMarkIndex k)) : rootCoordinateVariance k (fun _ => 0) 0 a = 0 := by
    cases a <;> rfl
  simp only [hz,NNReal.coe_zero,sub_zero] at h
  simpa only [rowReplicaMatrix,v,pathCovarianceDifference,NNReal.coe_zero,sub_zero,
    rowReplicaCovariance,rowReplicaLeaf] using h

lemma rowReplicaGaussian_finite (k r : ℕ) (xs : Fin r → CascadePath k)
    (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) :
    (rowReplicaCovariance k r d p₀ xs).PosSemidef ∧
    (Measure.pi (fun a : cascadeCoordinateSet k (rowReplicaSupport k r xs) =>
      gaussianReal 0 (rootCoordinateVariance k d p₀ a.val))).map
      (fun z => WithLp.toLp 2 (fun i => finiteRootPathField k (rowReplicaSupport k r xs)
        z (rowReplicaLeaf k r xs i))) =
      multivariateGaussian 0 (rowReplicaCovariance k r d p₀ xs) := by
  let v := fun a : cascadeCoordinateSet k (rowReplicaSupport k r xs) =>
    rootCoordinateVariance k d p₀ a.val
  have hgram := rowReplicaMatrix_gram k r xs d p₀
  have he : (fun z => WithLp.toLp 2 (fun i => finiteRootPathField k (rowReplicaSupport k r xs)
        z (rowReplicaLeaf k r xs i))) =
      (fun z => WithLp.toLp 2 ((rowReplicaMatrix k r xs).mulVec z)) := by
    funext z
    congr 1
    funext i
    exact (rowReplicaMatrix_mulVec k r xs z i).symm
  constructor
  · rw [← hgram]
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (weightedGaussianMatrix (rowReplicaMatrix k r xs) v)
  · rw [he,gaussianWeightedLinear_law,hgram]
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

theorem rowReplicaGaussian : RowReplicaGaussianStatement := by
  intro k r d p₀ xs
  refine ⟨(rowReplicaGaussian_finite k r xs d p₀).1,?_⟩
  let S := rowReplicaSupport k r xs
  let C := cascadeCoordinateSet k S
  let F := fun z : C → ℝ => WithLp.toLp 2
    (fun i => finiteRootPathField k S z (rowReplicaLeaf k r xs i))
  have hF : Measurable F := by
    unfold F finiteRootPathField
    fun_prop
  have hR : Measurable (C.restrict : (Option (CascadeMarkIndex k) → ℝ) → (C → ℝ)) :=
    Measurable.of_eval fun coordinate => measurable_pi_apply coordinate.val
  have he : rowReplicaGaussianField k r xs = F ∘ C.restrict := by
    funext z
    apply congrArg (WithLp.toLp 2)
    funext i
    exact rootPathField_finite k S z (rowReplicaLeaf k r xs i)
  rw [he,← Measure.map_map hF hR,Measure.infinitePi_map_restrict]
  exact (rowReplicaGaussian_finite k r xs d p₀).2
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped NNReal BigOperators RealInnerProductSpace

open Classical
namespace MicroscopicJamming

lemma multivariateGaussian_zero_conv {I : Type*} [Fintype I] [DecidableEq I]
    {C D : Matrix I I ℝ} (hC : C.PosSemidef) (hD : D.PosSemidef) :
    (multivariateGaussian 0 C).conv (multivariateGaussian 0 D) =
      multivariateGaussian 0 (C+D) := by
  apply Measure.ext_of_charFun
  funext t
  rw [charFun_conv,charFun_multivariateGaussian hC,charFun_multivariateGaussian hD,
    charFun_multivariateGaussian (hC.add hD),← Complex.exp_add]
  congr 1
  simp only [inner_zero_right,Complex.ofReal_zero,zero_mul,zero_sub,
    Matrix.add_mulVec,dotProduct_add,Complex.ofReal_add]
  ring

lemma gaussianDiagonal_law {I : Type*} [Fintype I] [DecidableEq I] (v : I → ℝ≥0) :
    (Measure.pi (fun i => gaussianReal 0 (v i))).map (WithLp.toLp 2) =
      multivariateGaussian 0 (Matrix.diagonal (fun i => (v i:ℝ))) := by
  have hg : weightedGaussianMatrix (1 : Matrix I I ℝ) v *
      (weightedGaussianMatrix (1 : Matrix I I ℝ) v).transpose =
      Matrix.diagonal (fun i => (v i:ℝ)) := by
    ext i j
    rw [weightedGaussianMatrix_gram]
    by_cases e : i=j
    · subst j
      simp [Matrix.one_apply]
    · simp [Matrix.one_apply,e]
  simpa only [Matrix.one_mulVec,hg] using gaussianWeightedLinear_law (1 : Matrix I I ℝ) v
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

open Classical
namespace MicroscopicJamming

lemma measurable_rowReplicaGaussianField (k r : ℕ) (xs : Fin r → CascadePath k) :
    Measurable (rowReplicaGaussianField k r xs) := by
  unfold rowReplicaGaussianField rootPathField
  fun_prop

theorem rowReplicaResidual : RowReplicaResidualStatement := by
  intro k r d p₀ Δ xs
  have hD : (Matrix.diagonal (fun _ : Fin r => (Δ:ℝ))).PosSemidef :=
    Matrix.PosSemidef.diagonal (fun _ => Δ.coe_nonneg)
  have hC := rowReplicaGaussian k r d p₀ xs
  refine ⟨hC.1.add hD,?_⟩
  let μ := Measure.infinitePi (fun a => gaussianReal 0 (rootCoordinateVariance k d p₀ a))
  let ν := Measure.pi (fun _ : Fin r => gaussianReal 0 Δ)
  have hF := measurable_rowReplicaGaussianField k r xs
  have hG : Measurable (WithLp.toLp 2 : (Fin r → ℝ) → EuclideanSpace ℝ (Fin r)) := by fun_prop
  have he : rowReplicaResidualField k r xs =
      (fun w : EuclideanSpace ℝ (Fin r) × EuclideanSpace ℝ (Fin r) => w.1+w.2) ∘
        Prod.map (rowReplicaGaussianField k r xs) (WithLp.toLp 2) := rfl
  rw [he,← Measure.map_map (by fun_prop) (hF.prodMap hG),
    ← Measure.map_prod_map μ ν hF hG]
  change (μ.map (rowReplicaGaussianField k r xs)).conv (ν.map (WithLp.toLp 2)) = _
  rw [hC.2,gaussianDiagonal_law]
  exact multivariateGaussian_zero_conv hC.1 hD
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators MatrixOrder

open Classical
namespace MicroscopicJamming

lemma gaussianJointLaw_of_fibers {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [Countable A] [MeasurableSingletonClass A] (r : ℕ)
    (μ : Measure A) (ν : Measure B) [SFinite ν]
    (C : A → Matrix (Fin r) (Fin r) ℝ)
    (F : A × B → EuclideanSpace ℝ (Fin r)) (hF : Measurable F)
    (hL : ∀ x, ν.map (fun y => F (x,y)) = multivariateGaussian 0 (C x)) :
    (μ.prod ν).map (fun w => (w.1,F w)) = gaussianAdjunctionMeasure r C μ := by
  have hJ : Measurable (fun w : A × B => (w.1,F w)) := measurable_fst.prodMk hF
  have hK : Measurable (gaussianAdjunctionMap r C) := by
    apply measurable_from_prod_countable_right
    intro x
    change Measurable (fun y : EuclideanSpace ℝ (Fin r) =>
      (x,Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C x)) y))
    exact measurable_const.prodMk (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C x))).continuous.measurable
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hJ]
  unfold gaussianAdjunctionMeasure
  rw [lintegral_map hf hK]
  rw [lintegral_prod (fun w => f (w.1,F w)) (by simpa only [Function.comp_def] using (hf.comp hJ).aemeasurable),
    lintegral_prod (fun w => f (gaussianAdjunctionMap r C w)) (by simpa only [Function.comp_def] using (hf.comp hK).aemeasurable)]
  apply lintegral_congr
  intro x
  have hx : Measurable (fun y : B => F (x,y)) := hF.comp measurable_prodMk_left
  have hf' : Measurable (fun z : EuclideanSpace ℝ (Fin r) => f (x,z)) :=
    hf.comp measurable_prodMk_left
  rw [← lintegral_map hf' hx,hL x]
  unfold multivariateGaussian
  simp only [zero_add]
  exact lintegral_map hf' (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C x))).continuous.measurable
end MicroscopicJamming

end

end OAI
