import Mathlib
import OAI.Probability.JammingConcavity.GaussianDerivativeMartingaleRowRefinementCovariance

namespace OAI

/-! Row Refinement Covariance. -/

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MicroscopicJamming
 
def rowMeshRanks (ms ts : List ℝ) : List ℝ :=
  (ms.toFinset ∪ ts.toFinset).sort (· ≤ ·)

def rowMeshWeight (ms : List ℝ) (d : ℕ → ℝ≥0) (a : ℝ) : ℝ≥0 :=
  if a ∈ ms then d (ms.idxOf a) else 0

def rowMeshIncrement (ms ts : List ℝ) (d : ℕ → ℝ≥0) (j : ℕ) : ℝ≥0 :=
  rowMeshWeight ms d ((rowMeshRanks ms ts).getD j 0)

def rowMeshTransport (ts ns : List ℝ) (j : ℕ) : ℕ :=
  ((ns.take j).filter (fun a => a ∈ ts)).length

lemma rowMeshRanks_sorted (ms ts : List ℝ) :
    (rowMeshRanks ms ts).Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise

@[simp] lemma rowMeshRanks_mem (ms ts : List ℝ) (a : ℝ) :
    a ∈ rowMeshRanks ms ts ↔ a ∈ ms ∨ a ∈ ts := by
  simp [rowMeshRanks]

lemma rowGaussianBlocks_congr (ms : List ℝ) (d e : ℕ → ℝ≥0)
    (h : ∀ j, j < ms.length → d j = e j) :
    rowGaussianBlocks ms d = rowGaussianBlocks ms e := by
  induction ms generalizing d e with
  | nil => rfl
  | cons m ms ih =>
    simp only [rowGaussianBlocks]
    have h0 := h 0 (by simp)
    rw [h0]
    congr 1
    exact ih _ _ (fun j hj => h (j+1) (by simpa using Nat.succ_lt_succ hj))

lemma rowGaussianBlocks_getD (ms : List ℝ) (w : ℝ → ℝ≥0) :
    rowGaussianBlocks ms (fun j => w (ms.getD j 0)) =
    ms.map (fun a => (a,(w a:ℝ))) := by
  induction ms with
  | nil => rfl
  | cons m ms ih =>
    simpa only [rowGaussianBlocks,List.getD_cons_zero,List.getD_cons_succ,
      List.map_cons] using congrArg (List.cons (m,(w m:ℝ))) ih

lemma rowGaussianBlocks_meshWeight (ms : List ℝ) (d : ℕ → ℝ≥0)
    (hm : ms.Nodup) :
    rowGaussianBlocks ms d = ms.map (fun a => (a,(rowMeshWeight ms d a:ℝ))) := by
  rw [←rowGaussianBlocks_getD]
  apply rowGaussianBlocks_congr
  intro j hj
  rw [List.getD_eq_getElem _ _ hj]
  simp only [rowMeshWeight,ite_eq_left (List.getElem_mem hj),hm.idxOf_getElem j hj]

lemma rowMeshBlocks_filter (ms ts : List ℝ) (d : ℕ → ℝ≥0)
    (hm : ms.Pairwise (· < ·)) :
    (rowGaussianBlocks (rowMeshRanks ms ts) (rowMeshIncrement ms ts d)).filter
        (fun r => r.2 != 0) =
      (rowGaussianBlocks ms d).filter (fun r => r.2 != 0) := by
  rw [rowGaussianBlocks_meshWeight ms d hm.nodup]
  change (rowGaussianBlocks (rowMeshRanks ms ts)
    (fun j => rowMeshWeight ms d ((rowMeshRanks ms ts).getD j 0))).filter _ = _
  rw [rowGaussianBlocks_getD,List.filter_map,List.filter_map]
  congr 1
  apply List.Pairwise.eq_of_mem_iff
    ((rowMeshRanks_sorted ms ts).filter _) (hm.filter _)
  intro a
  simp only [List.mem_filter,Function.comp_apply,rowMeshRanks_mem]
  constructor
  · rintro ⟨ha,hz⟩
    refine ⟨?_,hz⟩
    by_contra h
    simp [rowMeshWeight,h] at hz
  · rintro ⟨ha,hz⟩
    exact ⟨Or.inl ha,hz⟩

lemma rowGaussianBlocks_sum (ms : List ℝ) (d : ℕ → ℝ≥0) :
    ((rowGaussianBlocks ms d).map Prod.snd).sum = ∑ j : Fin ms.length, (d j:ℝ) := by
  induction ms generalizing d with
  | nil => simp [rowGaussianBlocks]
  | cons m ms ih =>
    simp only [rowGaussianBlocks,List.map_cons,List.sum_cons,List.length_cons,
      Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ]
    rw [ih]

lemma rowBlocks_sum_filter (rs : List (ℝ × ℝ)) :
    ((rs.filter (fun r => r.2 != 0)).map Prod.snd).sum = (rs.map Prod.snd).sum := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    by_cases h : r.2 = 0
    · simp [h,ih]
    · simp [h,ih]

lemma rowMesh_diagonal (ms ts : List ℝ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0)
    (hm : ms.Pairwise (· < ·)) :
    rowReplicaDiagonal (rowMeshRanks ms ts).length (rowMeshIncrement ms ts d) p₀ Δ =
      rowReplicaDiagonal ms.length d p₀ Δ := by
  have h := congrArg (fun rs : List (ℝ × ℝ) => (rs.map Prod.snd).sum)
    (rowMeshBlocks_filter ms ts d hm)
  rw [rowBlocks_sum_filter,rowBlocks_sum_filter,rowGaussianBlocks_sum,
    rowGaussianBlocks_sum] at h
  apply NNReal.coe_injective
  simp only [rowReplicaDiagonal,NNReal.coe_add,NNReal.coe_sum]
  rw [h]

lemma rowSorted_take_stepLevel (ns : List ℝ) (hn : ns.Pairwise (· < ·)) (s : ℝ) :
    ns.take (rpcStepLevel ns s) = ns.filter (fun a => a ≤ s) := by
  induction ns with
  | nil => rfl
  | cons a ns ih =>
    have ht := (List.pairwise_cons.mp hn).2
    by_cases ha : a ≤ s
    · simpa [rpcStepLevel,List.filter_cons,ha] using congrArg (List.cons a) (ih ht)
    · have he : ns.filter (fun a => a ≤ s) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        have hab := (List.pairwise_cons.mp hn).1 b hb
        simpa only [decide_eq_true_eq] using not_le.mpr ((lt_of_not_ge ha).trans hab)
      simp [rpcStepLevel,ha,he]

lemma rowMesh_transport (ts ns : List ℝ) (ht : ts.Pairwise (· < ·))
    (hn : ns.Pairwise (· < ·)) (hsub : ts ⊆ ns) (s : ℝ) :
    rpcStepLevel ts s = rowMeshTransport ts ns (rpcStepLevel ns s) := by
  rw [rowMeshTransport,rowSorted_take_stepLevel ns hn]
  unfold rpcStepLevel
  congr 1
  apply List.Pairwise.eq_of_mem_iff (ht.filter _) ((hn.filter _).filter _)
  intro a
  simp only [List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨ha,has⟩
    exact ⟨⟨hsub ha,has⟩,ha⟩
  · rintro ⟨⟨_,has⟩,ha⟩
    exact ⟨ha,has⟩

end MicroscopicJamming

 

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MicroscopicJamming

def rowTestExtend (φ : C(Set.Icc (0:ℝ) 1, ℝ)) (s : ℝ) : ℝ :=
  φ ⟨min 1 (max 0 s), le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

def rowMeshTest (ms : List ℝ) (φ : C(Set.Icc (0:ℝ) 1, ℝ))
    (n j : ℕ) : ℝ :=
  rowTestExtend φ ((rowMeshTransport (rankMesh n)
    (rowMeshRanks ms (rankMesh n)) j : ℝ) / ((n:ℝ)+1))

def rowFullRankView (u : ℝ → ℝ) (φ : C(Set.Icc (0:ℝ) 1, ℝ)) (k : ℕ)
    (z : RankArray × EuclideanSpace ℝ (Fin (2+k))) : ℝ × (Fin (2+k) → ℝ) :=
  (rowTestExtend φ (z.1 0 1) *
    (deriv u (z.2 (Fin.castAdd k (0:Fin 2))) *
      deriv u (z.2 (Fin.castAdd k (1:Fin 2)))), fun i => u (z.2 i))

def RowAllRankTestLawStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) (φ : C(Set.Icc (0:ℝ) 1,ℝ)) (k : ℕ),
    ∃ (ρ : ℕ → ProbabilityMeasure (ℝ × (Fin (2+k) → ℝ)))
      (ρ₀ : ProbabilityMeasure (ℝ × (Fin (2+k) → ℝ))),
      (∀ n, (ρ n : Measure _) =
        replicaFieldLaw
          (rowReplicaEnvironmentLaw (rowMeshRanks ms (rankMesh n))
            (rowMeshIncrement ms (rankMesh n) d) p₀)
          (rowReplicaKernel (rowMeshRanks ms (rankMesh n)) Δ)
          (rowFullPotential (rowMeshRanks ms (rankMesh n)) u)
          (rowFullPair (rowMeshRanks ms (rankMesh n)) u (rowMeshTest ms φ n)) k) ∧
      (ρ₀ : Measure _) =
        (gaussianAdjunctionMeasure (2+k)
          (rowFullRankCovariance (2+k) (rowReplicaDiagonal ms.length d p₀ Δ)
            (rowCascadeProfile ms d p₀)) realizedRankLaw).map (rowFullRankView u φ k) ∧
      Tendsto ρ atTop (𝓝 ρ₀)
end MicroscopicJamming

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace MicroscopicJamming

lemma probabilityMap_tendsto_of_ae {A B : Type*} [MeasurableSpace A]
    [TopologicalSpace B] [MeasurableSpace B] [BorelSpace B] [OpensMeasurableSpace B]
    (μ : Measure A) [IsProbabilityMeasure μ]
    (f : ℕ → A → B) (g : A → B)
    (hf : ∀ n, AEMeasurable (f n) μ) (hg : AEMeasurable g μ)
    (hlim : ∀ᵐ a ∂μ, Tendsto (fun n => f n a) atTop (𝓝 (g a))) :
    Tendsto (fun n => (⟨μ.map (f n), inferInstance⟩ : ProbabilityMeasure B))
      atTop (@nhds (ProbabilityMeasure B) inferInstance (⟨μ.map g, inferInstance⟩ : ProbabilityMeasure B)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro F
  change Tendsto (fun n => ∫ b, F b ∂μ.map (f n)) atTop (𝓝 (∫ b, F b ∂μ.map g))
  simp_rw [integral_map (hf _) F.continuous.aestronglyMeasurable,
    integral_map hg F.continuous.aestronglyMeasurable]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖F‖)
  · intro n
    exact (F.continuous.measurable.comp_aemeasurable (hf n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Filter.Eventually.of_forall (fun a => F.norm_coe_le_norm (f n a))
  · filter_upwards [hlim] with a ha
    exact F.continuous.continuousAt.tendsto.comp ha

end MicroscopicJamming

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MicroscopicJamming

lemma rowTestExtend_continuous (φ : C(Set.Icc (0:ℝ) 1, ℝ)) :
    Continuous (rowTestExtend φ) := by
  apply φ.continuous.comp
  apply Continuous.subtype_mk
  fun_prop

lemma rowTestExtend_eq (φ : C(Set.Icc (0:ℝ) 1, ℝ)) (s : Set.Icc (0:ℝ) 1) :
    rowTestExtend φ s = φ s := by
  simp only [rowTestExtend, max_eq_right s.property.1, min_eq_right s.property.2]

lemma rowMesh_valid (ms ts : List ℝ)
    (hm : ∀ m ∈ ms, 0 < m ∧ m < 1) (ht : ∀ t ∈ ts, 0 < t ∧ t < 1) :
    ∀ a ∈ rowMeshRanks ms ts, 0 < a ∧ a < 1 := by
  intro a ha
  exact ((rowMeshRanks_mem ms ts a).mp ha).elim (hm a) (ht a)

lemma rowMeshTest_transport (ms : List ℝ) (φ : C(Set.Icc (0:ℝ) 1, ℝ))
    (n : ℕ) (s : ℝ) :
    rowMeshTest ms φ n (rpcStepLevel (rowMeshRanks ms (rankMesh n)) s) =
      rowTestExtend φ (rankMeshValue n s) := by
  unfold rowMeshTest rankMeshValue
  rw [←rowMesh_transport (rankMesh n) (rowMeshRanks ms (rankMesh n))
    (rankMesh_increasing n) (rowMeshRanks_sorted _ _)
    (fun _ ha => (rowMeshRanks_mem _ _ _).mpr (Or.inr ha)) s]

lemma measurable_gaussianAdjunction_countable {A B : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [Countable B] [MeasurableSingletonClass B]
    (r : ℕ) (C : B → Matrix (Fin r) (Fin r) ℝ) (g : A → B) (hg : Measurable g) :
    Measurable (gaussianAdjunctionMap r (C ∘ g)) := by
  have hC : Measurable (gaussianAdjunctionMap r C) := by
    apply measurable_from_prod_countable_right
    intro x
    exact measurable_const.prodMk
      (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C x))).continuous.measurable
  exact measurable_fst.prodMk ((hC.comp (hg.prodMap measurable_id)).snd)

lemma rowGaussianAdjunction_aemeasurable (ms : List ℝ) (r : ℕ)
    (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) :
    AEMeasurable (gaussianAdjunctionMap r
      (rowFullRankCovariance r (rowReplicaDiagonal ms.length d p₀ Δ)
        (rowCascadeProfile ms d p₀)))
      (realizedRankLaw.prod (stdGaussian (EuclideanSpace ℝ (Fin r)))) := by
  apply (measurable_gaussianAdjunction_countable r (rowSignatureCovariance ms.length r d p₀ Δ)
    (rankGenealogySignature ms r) (measurable_rankGenealogySignature ms r)).aemeasurable.congr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (rowCascadeCovariance_ae (r := r) ms d p₀ Δ)] with z hz
  simp only [gaussianAdjunctionMap,hz]

lemma rowGaussianAdjunction_probability (ms : List ℝ) (r : ℕ)
    (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) :
    IsProbabilityMeasure (gaussianAdjunctionMeasure r
      (rowFullRankCovariance r (rowReplicaDiagonal ms.length d p₀ Δ)
        (rowCascadeProfile ms d p₀)) realizedRankLaw) := by
  unfold gaussianAdjunctionMeasure
  infer_instance

lemma rowGaussianAdjunction_rank_mem (ms : List ℝ) (r : ℕ)
    (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) :
    ∀ᵐ z ∂gaussianAdjunctionMeasure r
      (rowFullRankCovariance r (rowReplicaDiagonal ms.length d p₀ Δ)
        (rowCascadeProfile ms d p₀)) realizedRankLaw,
        z.1 0 1 ∈ Set.Icc (0:ℝ) 1 := by
  apply (ae_map_iff (rowGaussianAdjunction_aemeasurable ms r d p₀ Δ)
    (by measurability)).mpr
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae realizedRankLaw_constraints] with z hz
  exact hz.2.2.1 0 1

def rowMeshRankView (u : ℝ → ℝ) (φ : C(Set.Icc (0:ℝ) 1, ℝ)) (k n : ℕ)
    (z : RankArray × EuclideanSpace ℝ (Fin (2+k))) : ℝ × (Fin (2+k) → ℝ) :=
  (rowTestExtend φ (rankMeshValue n (z.1 0 1)) *
    (deriv u (z.2 (Fin.castAdd k (0:Fin 2))) *
      deriv u (z.2 (Fin.castAdd k (1:Fin 2)))), fun i => u (z.2 i))

lemma measurable_rowFullRankView (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u)
    (φ : C(Set.Icc (0:ℝ) 1, ℝ)) (k : ℕ) : Measurable (rowFullRankView u φ k) := by
  have huM : Measurable u := hu.continuous.measurable
  have hdu : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
  have hφ := (rowTestExtend_continuous φ).measurable
  unfold rowFullRankView
  fun_prop

lemma measurable_rowMeshRankView (u : ℝ → ℝ) (hu : ContDiff ℝ 2 u)
    (φ : C(Set.Icc (0:ℝ) 1, ℝ)) (k n : ℕ) : Measurable (rowMeshRankView u φ k n) := by
  have huM : Measurable u := hu.continuous.measurable
  have hdu : Continuous (deriv u) := hu.continuous_deriv (by norm_num)
  have hφ := (rowTestExtend_continuous φ).measurable
  have hmesh : Measurable (rankMeshValue n) := by
    unfold rankMeshValue
    exact ((show Measurable (fun a : ℕ => (a:ℝ)) from measurable_of_countable _).comp
      (measurable_rpcStepLevel _)).div_const _
  unfold rowMeshRankView
  fun_prop

lemma rowMesh_fields_exact (u : ℝ → ℝ) (L H : ℝ) (hu : ContDiff ℝ 2 u)
    (hL : 0 ≤ L) (hH : 0 ≤ H)
    (hb : ∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H)
    (ms : List ℝ) (hms : ms.Pairwise (· < ·)) (hm : ∀ m ∈ ms, 0 < m ∧ m < 1)
    (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) (φ : C(Set.Icc (0:ℝ) 1,ℝ)) (k n : ℕ) :
    replicaFieldLaw
      (rowReplicaEnvironmentLaw (rowMeshRanks ms (rankMesh n))
        (rowMeshIncrement ms (rankMesh n) d) p₀)
      (rowReplicaKernel (rowMeshRanks ms (rankMesh n)) Δ)
      (rowFullPotential (rowMeshRanks ms (rankMesh n)) u)
      (rowFullPair (rowMeshRanks ms (rankMesh n)) u (rowMeshTest ms φ n)) k =
    (gaussianAdjunctionMeasure (2+k)
      (rowFullRankCovariance (2+k) (rowReplicaDiagonal ms.length d p₀ Δ)
        (rowCascadeProfile ms d p₀)) realizedRankLaw).map (rowMeshRankView u φ k n) := by
  rw [rowRetainedRankLaw u L H hu hL hH hb _ (rowMeshRanks_sorted _ _)
    (rowMesh_valid _ _ hm (rankMesh_valid n))]
  rw [rowMesh_diagonal ms (rankMesh n) d p₀ Δ hms]
  rw [(rowRefinementCovariance _ _ (rowMeshRanks_sorted _ _) hms
    (rowMesh_valid _ _ hm (rankMesh_valid n)) hm _ d p₀
    (rowMeshBlocks_filter ms (rankMesh n) d hms)).2]
  congr 1
  funext z
  simp only [rowMeshRankView,rowMeshTest_transport]

theorem rowAllRankTestLaw : RowAllRankTestLawStatement := by
  intro u L H hu hL hH hb ms hms hm d p₀ Δ φ k
  let μ := gaussianAdjunctionMeasure (2+k)
    (rowFullRankCovariance (2+k) (rowReplicaDiagonal ms.length d p₀ Δ)
      (rowCascadeProfile ms d p₀)) realizedRankLaw
  have : IsProbabilityMeasure μ := rowGaussianAdjunction_probability ms (2+k) d p₀ Δ
  let ρ : ℕ → ProbabilityMeasure (ℝ × (Fin (2+k) → ℝ)) := fun n =>
    ⟨μ.map (rowMeshRankView u φ k n), inferInstance⟩
  let ρ₀ : ProbabilityMeasure (ℝ × (Fin (2+k) → ℝ)) :=
    ⟨μ.map (rowFullRankView u φ k), inferInstance⟩
  refine ⟨ρ,ρ₀,?_,rfl,?_⟩
  · intro n
    exact (rowMesh_fields_exact u L H hu hL hH hb ms hms hm d p₀ Δ φ k n).symm
  · apply probabilityMap_tendsto_of_ae μ _ _
      (fun n => (measurable_rowMeshRankView u hu φ k n).aemeasurable)
      (measurable_rowFullRankView u hu φ k).aemeasurable
    filter_upwards [rowGaussianAdjunction_rank_mem ms (2+k) d p₀ Δ] with z hz
    have hφ := (rowTestExtend_continuous φ).continuousAt.tendsto.comp
      (rankMeshValue_tendsto hz)
    exact (hφ.mul tendsto_const_nhds).prodMk_nhds tendsto_const_nhds

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix.Norms.L2Operator MatrixOrder Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
local instance (r : ℕ) : MeasurableSpace (Matrix (Fin r) (Fin r) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (Matrix (Fin r) (Fin r) ℝ) := ⟨rfl⟩
lemma isClosed_matrix_nonneg (r : ℕ) : IsClosed {a : Matrix (Fin r) (Fin r) ℝ | 0 ≤ a} := by
  simp only [Matrix.nonneg_iff_posSemidef, Matrix.posSemidef_iff_dotProduct_mulVec]
  apply IsClosed.inter
  · change IsClosed {a : Matrix (Fin r) (Fin r) ℝ | a.conjTranspose = a}
    apply isClosed_eq <;> fun_prop
  · change IsClosed {a : Matrix (Fin r) (Fin r) ℝ | ∀ x : Fin r → ℝ, 0 ≤ star x ⬝ᵥ a.mulVec x}
    have he : {a : Matrix (Fin r) (Fin r) ℝ | ∀ x : Fin r → ℝ, 0 ≤ star x ⬝ᵥ a.mulVec x} =
        ⋂ x : Fin r → ℝ, {a : Matrix (Fin r) (Fin r) ℝ | 0 ≤ star x ⬝ᵥ a.mulVec x} := by ext; simp
    rw [he]
    apply isClosed_iInter
    intro x
    apply isClosed_le continuous_const
    fun_prop

lemma measurable_matrix_sqrt (r : ℕ) :
    Measurable (CFC.sqrt : Matrix (Fin r) (Fin r) ℝ → _) := by
  classical
  have h := (CFC.continuousOn_sqrt (A := Matrix (Fin r) (Fin r) ℝ)).measurable_piecewise
    (continuous_const.continuousOn (f := fun _ : Matrix (Fin r) (Fin r) ℝ => (0 : Matrix (Fin r) (Fin r) ℝ)))
    ((isClosed_matrix_nonneg r).measurableSet : MeasurableSet {a : Matrix (Fin r) (Fin r) ℝ | 0 ≤ a})
  convert h using 1
  funext a
  by_cases ha : 0 ≤ a
  · simp only [Set.piecewise,Set.mem_ofPred_eq,ha,ite_true]
  · simp only [Set.piecewise,Set.mem_ofPred_eq,ha,ite_false,CFC.sqrt_of_not_nonneg ha]

lemma continuous_matrix_clm (r : ℕ) :
    Continuous (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin r)) := by
  exact (Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin r)).toAlgEquiv.toLinearMap.continuous_of_finiteDimensional

lemma measurable_matrix_gaussian_map {A : Type*} [MeasurableSpace A]
    (r : ℕ) (C : A → Matrix (Fin r) (Fin r) ℝ) (hC : Measurable C) :
    Measurable (fun z : A × EuclideanSpace ℝ (Fin r) =>
      (z.1, Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (C z.1)) z.2)) := by
  apply measurable_fst.prodMk
  have heval : Continuous (fun z : (EuclideanSpace ℝ (Fin r) →L[ℝ] EuclideanSpace ℝ (Fin r)) ×
      EuclideanSpace ℝ (Fin r) => z.1 z.2) := continuous_fst.clm_apply continuous_snd
  exact heval.measurable.comp (((continuous_matrix_clm r).measurable.comp
    ((measurable_matrix_sqrt r).comp (hC.comp measurable_fst))).prodMk measurable_snd)

lemma matrix_gaussian_map_tendsto
    (r : ℕ) (Cn : ℕ → Matrix (Fin r) (Fin r) ℝ) (C : Matrix (Fin r) (Fin r) ℝ)
    (hCn : ∀ n, (Cn n).PosSemidef) (hC : C.PosSemidef)
    (hlim : Tendsto Cn atTop (𝓝 C)) (x : EuclideanSpace ℝ (Fin r)) :
    Tendsto (fun n => Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt (Cn n)) x)
      atTop (𝓝 (Matrix.toEuclideanCLM (𝕜 := ℝ) (CFC.sqrt C) x)) := by
  have hs := CFC.continuousOn_sqrt (A := Matrix (Fin r) (Fin r) ℝ) C hC.nonneg
  have hh := hs.tendsto.comp (tendsto_nhdsWithin_iff.mpr
    ⟨hlim,Eventually.of_forall (fun n => (hCn n).nonneg)⟩)
  exact ((continuous_matrix_clm r).clm_apply (continuous_const (y := x))).continuousAt.tendsto.comp hh

end MicroscopicJamming

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal

namespace MicroscopicJamming
local instance (r : ℕ) : MeasurableSpace (Matrix (Fin r) (Fin r) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (Matrix (Fin r) (Fin r) ℝ) := ⟨rfl⟩

lemma rowClosedProfile_integrable (p : SphericalProfile) :
    Integrable (rowClosedProfile p) (volume.restrict (Set.Icc (0:ℝ) 1)) := by
  refine ⟨(measurable_rowClosedProfile p).aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := p.val 1) ?_⟩
  exact Eventually.of_forall fun s => by
    rw [Real.norm_eq_abs, abs_of_nonneg (rowClosedProfile_bound p s).1]
    exact (rowClosedProfile_bound p s).2

lemma rowClosedProfile_eLpNorm_eq (p q : SphericalProfile) :
    eLpNorm (rowClosedProfile p - rowClosedProfile q) 1 (volume.restrict (Set.Icc (0:ℝ) 1)) =
      ENNReal.ofReal (sphericalProfileDistance p.val q.val) := by
  rw [eLpNorm_one_eq_lintegral_enorm
    ((rowClosedProfile_integrable p).sub (rowClosedProfile_integrable q)).aestronglyMeasurable,
    ← ofReal_integral_norm_eq_lintegral_enorm
    ((rowClosedProfile_integrable p).sub (rowClosedProfile_integrable q))]
  congr 1
  rw [sphericalProfileDistance, intervalIntegral.integral_of_le zero_le_one,
    ←integral_Icc_eq_integral_Ioc]
  apply setIntegral_congr_fun measurableSet_Icc
  intro s hs
  simp only [Pi.sub_apply,Real.norm_eq_abs,rowClosedProfile_eq p hs,rowClosedProfile_eq q hs]

lemma rowClosedProfile_tendstoInMeasure (pn : ℕ → SphericalProfile) (p : SphericalProfile)
    (hp : Tendsto (fun n => sphericalProfileDistance (pn n).val p.val) atTop (𝓝 0)) :
    TendstoInMeasure (volume.restrict (Set.Icc (0:ℝ) 1))
      (fun n => rowClosedProfile (pn n)) atTop (rowClosedProfile p) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (p := 1) one_ne_zero
  simp_rw [rowClosedProfile_eLpNorm_eq]
  simpa only [Function.comp_def, ENNReal.ofReal_zero] using
    ((ENNReal.continuous_ofReal.tendsto (0:ℝ)).comp hp)

end MicroscopicJamming

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal NNReal BigOperators MatrixOrder Matrix.Norms.L2Operator

namespace MicroscopicJamming
local instance (r : ℕ) : MeasurableSpace (Matrix (Fin r) (Fin r) ℝ) := borel _
local instance (r : ℕ) : BorelSpace (Matrix (Fin r) (Fin r) ℝ) := ⟨rfl⟩

lemma rowRankCovariance_tendsto_ae_of_profile_ae
    (Q : ℝ) (pn : ℕ → SphericalProfile) (p : SphericalProfile) (r : ℕ)
    (h : ∀ᵐ s ∂volume.restrict (Set.Icc (0:ℝ) 1),
      Tendsto (fun n => rowClosedProfile (pn n) s) atTop (𝓝 (rowClosedProfile p s))) :
    ∀ᵐ U ∂realizedRankLaw, Tendsto (fun n => rowFullRankCovariance r Q (pn n) U)
      atTop (𝓝 (rowFullRankCovariance r Q p U)) := by
  have hentry (i j : Fin r) : ∀ᵐ U ∂realizedRankLaw,
      Tendsto (fun n => rowFullRankCovariance r Q (pn n) U i j)
        atTop (𝓝 (rowFullRankCovariance r Q p U i j)) := by
    by_cases hij : i=j
    · exact Eventually.of_forall (fun U => by simp only [rowFullRankCovariance,hij,ite_true]; exact tendsto_const_nhds)
    · have h' := h
      rw [←realizedRankLaw_pair_uniform i.val j.val (fun hv => hij (Fin.ext hv))] at h'
      have hh := ae_of_ae_map (show Measurable (fun U : RankArray => U i.val j.val) from by fun_prop).aemeasurable h'
      simpa only [rowFullRankCovariance,ite_eq_right hij] using hh
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (fun j => hentry i j))] with U hU
  exact tendsto_pi_nhds.mpr (fun i => tendsto_pi_nhds.mpr (fun j => hU i j))

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology NNReal ENNReal BigOperators

namespace MicroscopicJamming
 

def finiteSpinProfile (ms : List ℝ) (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) (s : ℝ) : ℝ :=
  (p₀:ℝ)+∑ j ∈ Finset.range ms.length, if ms[j]! ≤ s then (d j:ℝ) else 0

structure SphericalStepProfile where
  ranks : List ℝ
  variance : ℕ → ℝ≥0
  initial : ℝ≥0
  ordered : ranks.Pairwise (· < ·)
  ranks_mem : ∀ m ∈ ranks, 0 < m ∧ m < 1

def SphericalStepProfile.val (P : SphericalStepProfile) : ℝ → ℝ :=
  finiteSpinProfile P.ranks P.variance P.initial

def boundedSphericalProfiles (B : ℝ) : Set SphericalProfile :=
  {p | ∀ s ∈ Set.Icc 0 1, p.val s ≤ B}

lemma finiteSpinProfile_monotone (ms : List ℝ) (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) :
    Monotone (finiteSpinProfile ms d p₀) := by
  intro s t hst
  unfold finiteSpinProfile
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro j hj
  split_ifs with hs ht
  · rfl
  · exact False.elim (ht (hs.trans hst))
  · exact (d j).coe_nonneg
  · rfl

lemma finiteSpinProfile_nonneg (ms : List ℝ) (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) (s : ℝ) :
    0 ≤ finiteSpinProfile ms d p₀ s := by
  unfold finiteSpinProfile
  positivity

def SphericalStepProfile.toProfile (P : SphericalStepProfile) : SphericalProfile where
  val := P.val
  mono := (finiteSpinProfile_monotone P.ranks P.variance P.initial).monotoneOn _
  nonneg := fun s _ => finiteSpinProfile_nonneg P.ranks P.variance P.initial s

lemma SphericalProfile.integrable (p : SphericalProfile) :
    IntervalIntegrable p.val volume 0 1 := by
  apply MonotoneOn.intervalIntegrable
  simpa using p.mono

lemma SphericalStepProfile.integrable (P : SphericalStepProfile) :
    IntervalIntegrable P.val volume 0 1 := P.toProfile.integrable

lemma sphericalProfileDistance_nonneg (p q : SphericalProfile) :
    0 ≤ sphericalProfileDistance p.val q.val := by
  apply intervalIntegral.integral_nonneg (by norm_num)
  intro s hs
  exact abs_nonneg _

lemma sphericalProfileDistance_self (p : SphericalProfile) :
    sphericalProfileDistance p.val p.val = 0 := by simp [sphericalProfileDistance]

lemma sphericalProfileDistance_comm (p q : SphericalProfile) :
    sphericalProfileDistance p.val q.val = sphericalProfileDistance q.val p.val := by
  unfold sphericalProfileDistance
  simp_rw [abs_sub_comm]

lemma sphericalProfileDistance_triangle (p q r : SphericalProfile) :
    sphericalProfileDistance p.val r.val ≤
      sphericalProfileDistance p.val q.val+sphericalProfileDistance q.val r.val := by
  unfold sphericalProfileDistance
  rw [← intervalIntegral.integral_add (p.integrable.sub q.integrable).abs
    (q.integrable.sub r.integrable).abs]
  apply intervalIntegral.integral_mono_on (by norm_num) (p.integrable.sub r.integrable).abs
    ((p.integrable.sub q.integrable).abs.add (q.integrable.sub r.integrable).abs)
  intro s hs
  exact abs_sub_le (p.val s) (q.val s) (r.val s)

end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

def spinGridPoint (n k : ℕ) : ℝ := (k:ℝ)/((n:ℝ)+1)
def spinGridRanks (n : ℕ) : List ℝ := List.ofFn (fun j : Fin n => spinGridPoint n (j+1))

lemma spinGridPoint_pos_denom (n : ℕ) : (0:ℝ) < (n:ℝ)+1 := by positivity
lemma spinGridPoint_mono (n : ℕ) : Monotone (spinGridPoint n) := by
  intro i j h
  exact div_le_div_of_nonneg_right (by exact_mod_cast h) (spinGridPoint_pos_denom n).le
lemma spinGridPoint_mem (n k : ℕ) (hk : k ≤ n+1) : spinGridPoint n k ∈ Set.Icc 0 1 := by
  constructor
  · unfold spinGridPoint; positivity
  · rw [spinGridPoint, div_le_one (spinGridPoint_pos_denom n)]
    exact_mod_cast hk
lemma spinGridPoint_zero (n : ℕ) : spinGridPoint n 0 = 0 := by simp [spinGridPoint]
lemma spinGridPoint_last (n : ℕ) : spinGridPoint n (n+1) = 1 := by
  simp [spinGridPoint, ne_of_gt (spinGridPoint_pos_denom n)]
lemma spinGridRanks_length (n : ℕ) : (spinGridRanks n).length = n := by simp [spinGridRanks]
lemma spinGridRanks_get (n j : ℕ) (hj : j < n) : (spinGridRanks n)[j]! = spinGridPoint n (j+1) := by
  rw [getElem!_pos (spinGridRanks n) j (by simpa [spinGridRanks_length] using hj)]
  simp [spinGridRanks]
lemma spinGridRanks_ordered (n : ℕ) : (spinGridRanks n).Pairwise (· < ·) := by
  apply List.pairwise_ofFn.mpr
  intro i j hij
  unfold spinGridPoint
  apply (div_lt_div_iff_of_pos_right (spinGridPoint_pos_denom n)).2
  have hh : (i:ℝ) < (j:ℝ) := by exact_mod_cast hij
  simpa only [Nat.cast_add,Nat.cast_one,add_comm] using add_lt_add_right hh 1
lemma spinGridRanks_mem (n : ℕ) : ∀ a ∈ spinGridRanks n, 0 < a ∧ a < 1 := by
  intro a ha
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
  constructor
  · unfold spinGridPoint; positivity
  · rw [spinGridPoint,div_lt_one (spinGridPoint_pos_denom n)]
    have hh : (j:ℝ) < (n:ℝ) := by exact_mod_cast j.isLt
    simpa only [Nat.cast_add,Nat.cast_one,add_comm] using add_lt_add_right hh 1

def SphericalProfile.gridStep (p : SphericalProfile) (n : ℕ) : SphericalStepProfile where
  ranks := spinGridRanks n
  variance := fun j => Real.toNNReal (p.val (spinGridPoint n (j+1))-p.val (spinGridPoint n j))
  initial := Real.toNNReal (p.val 0)
  ordered := spinGridRanks_ordered n
  ranks_mem := spinGridRanks_mem n

lemma gridStep_initial (p : SphericalProfile) (n : ℕ) :
    ((p.gridStep n).initial:ℝ) = p.val 0 := Real.coe_toNNReal _ (p.nonneg 0 (by norm_num))
lemma gridStep_variance (p : SphericalProfile) (n j : ℕ) (hj : j < n) :
    ((p.gridStep n).variance j:ℝ) = p.val (spinGridPoint n (j+1))-p.val (spinGridPoint n j) := by
  apply Real.coe_toNNReal
  exact sub_nonneg.mpr (p.mono (spinGridPoint_mem n j (by omega))
    (spinGridPoint_mem n (j+1) (by omega)) (spinGridPoint_mono n (by omega)))

lemma sum_range_ite_lt_real (f : ℕ → ℝ) (n k : ℕ) (hk : k ≤ n) :
    (∑ j ∈ Finset.range n, if j < k then f j else 0) = ∑ j ∈ Finset.range k, f j := by
  symm
  calc
    _ = ∑ j ∈ Finset.range k, if j < k then f j else 0 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [ite_eq_left (Finset.mem_range.mp hj)]
    _ = _ := Finset.sum_subset (Finset.range_mono hk) (by
      intro j hj hnot
      rw [ite_eq_right (by simpa using hnot)])

lemma gridStep_val_cell (p : SphericalProfile) (n k : ℕ) (hk : k ≤ n)
    (s : ℝ) (hs : s ∈ Set.Ioo (spinGridPoint n k) (spinGridPoint n (k+1))) :
    (p.gridStep n).val s = p.val (spinGridPoint n k) := by
  change ((p.gridStep n).initial:ℝ) + ∑ j ∈ Finset.range (spinGridRanks n).length,
    (if (spinGridRanks n)[j]! ≤ s then ((p.gridStep n).variance j:ℝ) else 0) = _
  rw [gridStep_initial,spinGridRanks_length]
  have he : (∑ j ∈ Finset.range n, if (spinGridRanks n)[j]! ≤ s then
      ((p.gridStep n).variance j:ℝ) else 0) =
      ∑ j ∈ Finset.range n, if j < k then
        p.val (spinGridPoint n (j+1))-p.val (spinGridPoint n j) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjn := Finset.mem_range.mp hj
    rw [spinGridRanks_get n j hjn,gridStep_variance p n j hjn]
    by_cases hjk : j < k
    · rw [ite_eq_left hjk,ite_eq_left ((spinGridPoint_mono n (by omega)).trans hs.1.le)]
    · rw [ite_eq_right hjk,ite_eq_right (not_le.mpr (hs.2.trans_le (spinGridPoint_mono n (by omega))))]
  rw [he,sum_range_ite_lt_real _ n k hk,Finset.sum_range_sub (fun j => p.val (spinGridPoint n j)) k,spinGridPoint_zero]
  ring
end MicroscopicJamming

end

end OAI
