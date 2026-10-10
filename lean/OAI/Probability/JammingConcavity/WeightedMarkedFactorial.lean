import Mathlib
import OAI.Probability.JammingConcavity.RPCLabelBridge

namespace OAI

/-! Weighted Marked Factorial. -/

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
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
lemma weightedMarked_factorial_comparison {A : Type} [MeasurableSpace A] [MeasurableEq A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m t : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {X : A → ℝ} (hX : Measurable X) (hi : Integrable (fun a => Real.exp (m*X a)) ν)
    (ht : 0 < t) (bs : List (ℕ × (A → ℝ≥0∞))) (hbs : ∀ b ∈ bs, 0 < b.1 ∧ Measurable b.2) :
    (∫⁻ ω, ENNReal.ofReal (Real.exp (-t*(expMarkedTotal m X ω).toReal)) *
      distinctCloudIntegral (bs.map (fun b => weightedMarkedBlock m X b.1 b.2)) (pointCloudMeasure ω) []
      ∂pointCloudLaw ν) =
    (bs.map (fun b => weightedChildMean ν m X b.2)).prod *
    (∫⁻ ω, ENNReal.ofReal (Real.exp (-t*(stableTotal m (∫ a, Real.exp (m*X a) ∂ν) ω).toReal)) *
      distinctCloudIntegral ((bs.map Prod.fst).map (fun n z => stableJump m (∫ a, Real.exp (m*X a) ∂ν) z^n))
        (pointCloudMeasure ω) [] ∂pointCloudLaw (Measure.dirac ())) := by
  let c := ∫ a, Real.exp (m*X a) ∂ν
  have hc : 0 < c := integral_exp_pos hi
  have hf : ∀ f ∈ bs.map (fun b => weightedMarkedBlock m X b.1 b.2), Measurable f := by
    intro f hf
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hf
    exact measurable_weightedMarkedBlock m hX b.1 (hbs b hb).2
  have hf' : ∀ f ∈ (bs.map Prod.fst).map (fun n z => stableJump m c z^n), Measurable f := by
    intro f hf
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hf
    exact (measurable_stableJump m c).pow_const n
  rw [expMarked_factorial_laplace ν hm hm1 hX hi ht.le _ hf,
    stable_factorial_laplace hm hm1 hc ht.le _ hf']
  have hprod : ((bs.map (fun b => weightedMarkedBlock m X b.1 b.2)).map
      (fun f => ∫⁻ z, f z*ENNReal.ofReal (expNeg (ENNReal.ofReal t*expMarkedJump m X z))
        ∂(volume.restrict (Set.Ioi 0)).prod ν)).prod =
      (bs.map (fun b => weightedChildMean ν m X b.2)).prod *
      (((bs.map Prod.fst).map (fun n z => stableJump m c z^n)).map
        (fun f => ∫⁻ z, f z*ENNReal.ofReal (expNeg (ENNReal.ofReal t*stableJump m c z))
          ∂(volume.restrict (Set.Ioi 0)).prod (Measure.dirac ()))).prod := by
    clear hf hf'
    simp only [List.map_map, Function.comp_def]
    induction bs with
    | nil => simp
    | cons b bs ih =>
      have hb := hbs b (by simp)
      have hb' : m < (b.1:ℝ) := by
        have : (1:ℝ) ≤ b.1 := by exact_mod_cast hb.1
        linarith
      have htail : ∀ b ∈ bs, 0 < b.1 ∧ Measurable b.2 := fun b hb => hbs b (by simp [hb])
      simp only [List.map_cons, List.prod_cons]
      rw [selected_exp_weighted_block ν hm ht hX hi b.1 hb' hb.2,
        selected_jump_gamma hm hc ht b.1 hb', ih htail]
      dsimp [c]
      ac_rfl
  rw [hprod]
  dsimp [c]
  ac_rfl
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma weighted_partition_comparison {A : Type} [MeasurableSpace A] [MeasurableEq A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m η : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {X : A → ℝ} (hX : Measurable X) (hi : Integrable (fun a => Real.exp (m*X a)) ν)
    (bs : List (ℕ × (A → ℝ≥0∞))) (hbs : ∀ b ∈ bs, 0 < b.1 ∧ Measurable b.2)
    (hfin : ∀ b ∈ bs, weightedChildMean ν m X b.2 ≠ ∞)
    (ha : 0 < ((bs.map Prod.fst).sum:ℝ)-η) :
    (∫⁻ ω, weightedMarkedPartitionNumerator m η X bs ω ∂pointCloudLaw ν) =
    (bs.map (fun b => weightedChildMean ν m X b.2)).prod *
    (∫⁻ ω, poissonPartitionNumerator m (∫ a, Real.exp (m*X a) ∂ν) η (bs.map Prod.fst) ω
      ∂pointCloudLaw (Measure.dirac ())) := by
  let c := ∫ a, Real.exp (m*X a) ∂ν
  have hc : 0 < c := integral_exp_pos hi
  have hf : ∀ f ∈ bs.map (fun b => weightedMarkedBlock m X b.1 b.2), Measurable f := by
    intro f hf
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hf
    exact measurable_weightedMarkedBlock m hX b.1 (hbs b hb).2
  have hf' : ∀ f ∈ (bs.map Prod.fst).map (fun n z => stableJump m c z^n), Measurable f := by
    intro f hf
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hf
    exact (measurable_stableJump m c).pow_const n
  have hC : (bs.map (fun b => weightedChildMean ν m X b.2)).prod ≠ ∞ := by
    clear hf hf' ha hbs
    induction bs with
    | nil => simp
    | cons b bs ih =>
      simp only [List.map_cons, List.prod_cons]
      exact ENNReal.mul_ne_top (hfin b (by simp)) (ih (fun b hb => hfin b (by simp [hb])))
  have h := weighted_mellin_comparison (pointCloudLaw ν) (pointCloudLaw (Measure.dirac ()))
    (measurable_expMarkedTotal m hX) (aemeasurable_distinct_cloud _ _ hf [])
    (measurable_stableTotal m c) (aemeasurable_distinct_cloud _ _ hf' [])
    (expMarkedTotal_properties ν hm hm1 hX hi).1 (stableTotal_properties hm hm1 hc).1
    ha hC (fun t ht => weightedMarked_factorial_comparison ν hm hm1 hX hi ht bs hbs)
  simpa only [weightedMarkedPartitionNumerator, poissonPartitionNumerator, neg_sub] using h

theorem weightedEPPF {A : Type} [MeasurableSpace A] [MeasurableEq A]
    (ν : Measure A) [IsProbabilityMeasure ν] (m η : ℝ)
    (hm : 0 < m) (hm1 : m < 1) (hη : 0 ≤ η) (hηm : η < m)
    (X : A → ℝ) (hX : Measurable X) (hi : Integrable (fun a => Real.exp (m*X a)) ν)
    (bs : List (ℕ × (A → ℝ≥0∞))) (hne : bs ≠ [])
    (hbs : ∀ b ∈ bs, 0 < b.1 ∧ Measurable b.2)
    (hfin : ∀ b ∈ bs, weightedChildMean ν m X b.2 ≠ ∞) :
    (∫⁻ ω, weightedMarkedPartitionNumerator m η X bs ω ∂pointCloudLaw ν) /
      ENNReal.ofReal (∫ ω, (expMarkedTotal m X ω).toReal^η ∂pointCloudLaw ν) =
      ENNReal.ofReal (partitionProduct m η (bs.map Prod.fst)) *
        (bs.map (fun b => weightedChildMean ν m X b.2)).prod := by
  have hns : ∀ n ∈ bs.map Prod.fst, 0 < n := by
    intro n hn
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hn
    exact (hbs b hb).1
  have hnsne : bs.map Prod.fst ≠ [] := by simpa using hne
  have hsum := (partition_natural_bounds (bs.map Prod.fst) hnsne hns).2
  have ha : 0 < ((bs.map Prod.fst).sum:ℝ)-η := by
    have : (1:ℝ) ≤ (bs.map Prod.fst).sum := by exact_mod_cast hsum
    linarith
  rw [weighted_partition_comparison ν hm hm1 hX hi bs hbs hfin ha,
    expMarkedTotal_moment_eq ν hm hm1 hX hi hη hηm, mul_div_assoc,
    cascadeEPPF m _ η hm hm1 (integral_exp_pos hi) hη hηm (bs.map Prod.fst) hnsne hns]
  exact mul_comm _ _
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def rpcWeightedBlocks (ms : List ℝ) (bs : List (ReplicaPattern ms.length)) :
    List (ℕ × (CascadeTree ms.length → ℝ≥0∞)) :=
  bs.map (fun b => (replicaPatternSize ms.length b, rpcPatternWeight ms b))

lemma weightedChildMean_cascade (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) (m : ℝ) (b : ReplicaPattern ms.length) :
    weightedChildMean (cascadeLaw ms) m (fun ω => Real.log (cascadeTotal ms ω).toReal)
      (rpcPatternWeight ms b) =
      (∫⁻ ω, ENNReal.ofReal ((cascadeTotal ms ω).toReal^m)*rpcPatternWeight ms b ω ∂cascadeLaw ms) /
        ENNReal.ofReal (∫ ω, (cascadeTotal ms ω).toReal^m ∂cascadeLaw ms) := by
  have he := exp_mul_log_cascadeTotal_ae ms hms h01 m
  unfold weightedChildMean
  rw [integral_congr_ae he]
  congr 1
  apply lintegral_congr_ae
  filter_upwards [he] with ω hω
  rw [hω, mul_comm]

lemma rpcPattern_numerator_ae (ms : List ℝ) (m η : ℝ) (hms : (m::ms).Pairwise (· < ·))
    (h01 : ∀ x ∈ m::ms, 0 < x ∧ x < 1) (bs : List (ReplicaPattern ms.length)) :
    (fun ω => ENNReal.ofReal ((cascadeTotal (m::ms) ω).toReal^η)*rpcPatternWeight (m::ms) bs ω)
    =ᵐ[cascadeLaw (m::ms)]
    weightedMarkedPartitionNumerator m η (fun ω => Real.log (cascadeTotal ms ω).toReal)
      (rpcWeightedBlocks ms bs) := by
  have htms := (List.pairwise_cons.mp hms).2
  have ht01 : ∀ x ∈ ms, 0 < x ∧ x < 1 := fun x hx => h01 x (by simp [hx])
  have hmarks := ae_pointCloud_marks (cascadeLaw ms) (exp_log_cascadeTotal_ae ms htms ht01)
  filter_upwards [(cascadeTotal_properties (m::ms) hms h01).1,
    cascadeTotal_expMarked_ae (m := m) htms ht01, hmarks] with ω hp he hω
  have hm := ae_cloud_measure_marks (ω := (ω : PointCloud (CascadeTree ms.length)))
    (p := fun a => ENNReal.ofReal (Real.exp (Real.log (cascadeTotal ms a).toReal)) = cascadeTotal ms a) hω
  have hfactor : distinctCloudIntegral
      (bs.map (fun b (z : ℝ × CascadeTree ms.length) =>
        (ENNReal.ofReal (z.1^(-1/m))*cascadeTotal ms z.2)^(replicaPatternSize ms.length b)*rpcPatternWeight ms b z.2))
      (pointCloudMeasure ω) [] =
      distinctCloudIntegral ((rpcWeightedBlocks ms bs).map
        (fun b => weightedMarkedBlock m (fun ω => Real.log (cascadeTotal ms ω).toReal) b.1 b.2))
        (pointCloudMeasure ω) [] := by
    simp only [rpcWeightedBlocks, List.map_map, Function.comp_def]
    apply distinctCloudIntegral_congr_ae
    intro b hb
    filter_upwards [hm] with z hz
    simp only [weightedMarkedBlock, expMarkedJump, hz]
  have hpow : ENNReal.ofReal ((cascadeTotal (m::ms) ω).toReal^η) *
      ENNReal.ofReal ((cascadeTotal (m::ms) ω).toReal^(-(replicaPatternSize (ms.length+1) bs:ℝ))) =
      ENNReal.ofReal ((expMarkedTotal m (fun ω => Real.log (cascadeTotal ms ω).toReal) ω).toReal^
        (η-(((rpcWeightedBlocks ms bs).map Prod.fst).sum:ℝ))) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _),
      ← Real.rpow_add (ENNReal.toReal_pos hp.1.ne' hp.2.ne), he]
    congr 1
    simp only [replicaPatternSize, rpcWeightedBlocks, List.map_map, Function.comp_def, sub_eq_add_neg]
  change ENNReal.ofReal ((cascadeTotal (m::ms) ω).toReal^η) *
    (ENNReal.ofReal ((cascadeTotal (m::ms) ω).toReal^(-(replicaPatternSize (ms.length+1) bs:ℝ))) * _) = _
  rw [← mul_assoc, hpow, hfactor]
  rfl
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
lemma partitionProduct_nonneg {m η : ℝ} (hm : 0 ≤ m) (hm1 : m < 1) (hηm : η < m)
    (ns : List ℕ) : 0 ≤ partitionProduct m η ns := by
  unfold partitionProduct
  apply mul_nonneg
  · apply div_nonneg
    · apply Finset.prod_nonneg
      intro a ha
      have h1 : (1:ℝ) ≤ a := by exact_mod_cast (Finset.mem_Ico.mp ha).1
      nlinarith
    · apply Finset.prod_nonneg
      intro a ha
      have h1 : (1:ℝ) ≤ a := by exact_mod_cast (Finset.mem_Ico.mp ha).1
      linarith
  · apply List.prod_nonneg
    intro x hx
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hx
    apply Finset.prod_nonneg
    intro a ha
    have h1 : (1:ℝ) ≤ a := by exact_mod_cast (Finset.mem_Ico.mp ha).1
    linarith

lemma rpcPatternProduct_nonneg (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) (η : ℝ) (hηm : ∀ m ∈ ms, η < m)
    (b : ReplicaPattern ms.length) : 0 ≤ rpcPatternProduct ms η b := by
  induction ms generalizing η with
  | nil => norm_num [rpcPatternProduct]
  | cons m ms ih =>
    change 0 ≤ partitionProduct m η (b.map (replicaPatternSize ms.length)) *
      (b.map (rpcPatternProduct ms m)).prod
    have hm := h01 m (by simp)
    apply mul_nonneg (partitionProduct_nonneg hm.1.le hm.2 (hηm m (by simp)) _)
    apply List.prod_nonneg
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact ih (List.pairwise_cons.mp hms).2 (fun x hx => h01 x (by simp [hx])) m
      (List.pairwise_cons.mp hms).1 a

lemma ofReal_list_prod {xs : List ℝ} (h : ∀ x ∈ xs, 0 ≤ x) :
    ENNReal.ofReal xs.prod = (xs.map ENNReal.ofReal).prod := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.prod_cons, List.map_cons]
    rw [ENNReal.ofReal_mul (h x (by simp)), ih (fun x hx => h x (by simp [hx]))]
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

theorem rpcPartition : RPCPartitionStatement := by
  intro ms
  induction ms with
  | nil =>
    intro hms h01 η hη hηm b hb
    simp only [cascadeTotal, rpcPatternWeight, rpcPatternProduct, cascadeLaw,
      ENNReal.toReal_one, Real.one_rpow, ENNReal.ofReal_one, mul_one, lintegral_one,
      integral_const, measureReal_def, smul_eq_mul]
    have hu : (Measure.dirac (():Unit)) univ = 1 := Measure.dirac_apply_of_mem (mem_univ ())
    change (Measure.dirac (():Unit)) univ / ENNReal.ofReal ((Measure.dirac (():Unit)) univ).toReal = 1
    rw [hu]
    norm_num
  | cons m ms ih =>
    intro hms h01 η hη hηm bs hbs
    have hm := h01 m (by simp)
    have hηm' := hηm m (by simp)
    have htail := (List.pairwise_cons.mp hms).2
    have hmchild := (List.pairwise_cons.mp hms).1
    have ht01 : ∀ x ∈ ms, 0 < x ∧ x < 1 := fun x hx => h01 x (by simp [hx])
    change bs ≠ (List.nil : List (ReplicaPattern ms.length)) ∧
      (∀ b, List.Mem b bs → ValidReplicaPattern ms.length b) at hbs
    let X : CascadeTree ms.length → ℝ := fun ω => Real.log (cascadeTotal ms ω).toReal
    have hX : Measurable X := (measurable_cascadeTotal ms).ennreal_toReal.log
    have hexp := exp_mul_log_cascadeTotal_ae ms htail ht01 m
    have hi : Integrable (fun ω => Real.exp (m*X ω)) (cascadeLaw ms) :=
      ((cascadeTotal_properties ms htail ht01).2.1 m hm.1 hmchild).congr hexp.symm
    have hmean (b : ReplicaPattern ms.length) (hb : List.Mem b bs) :
        weightedChildMean (cascadeLaw ms) m X (rpcPatternWeight ms b) =
          ENNReal.ofReal (rpcPatternProduct ms m b) := by
      rw [weightedChildMean_cascade ms htail ht01]
      exact ih htail ht01 m hm.1.le hmchild b (hbs.2 b hb)
    have hblocks : ∀ b ∈ rpcWeightedBlocks ms bs, 0 < b.1 ∧ Measurable b.2 := by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      exact ⟨replicaPatternSize_pos _ _ (hbs.2 a ha), measurable_rpcPatternWeight ms a⟩
    have hfin : ∀ b ∈ rpcWeightedBlocks ms bs, weightedChildMean (cascadeLaw ms) m X b.2 ≠ ∞ := by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      rw [hmean a ha]
      exact ENNReal.ofReal_ne_top
    have hne : rpcWeightedBlocks ms bs ≠ [] := by
      intro he
      exact hbs.1 (List.map_eq_nil_iff.mp he)
    have hw := weightedEPPF (cascadeLaw ms) m η hm.1 hm.2 hη hηm' X hX hi
      (rpcWeightedBlocks ms bs) hne hblocks hfin
    have he := cascadeTotal_expMarked_ae (m := m) htail ht01
    have hden : (∫ ω, (cascadeTotal (m::ms) ω).toReal^η ∂cascadeLaw (m::ms)) =
        ∫ ω, (expMarkedTotal m X ω).toReal^η ∂pointCloudLaw (cascadeLaw ms) :=
      integral_congr_ae (he.mono fun _ h => congrArg (fun x : ℝ≥0∞ => x.toReal^η) h)
    rw [lintegral_congr_ae (rpcPattern_numerator_ae ms m η hms h01 bs), hden]
    change (∫⁻ ω, weightedMarkedPartitionNumerator m η X (rpcWeightedBlocks ms bs) ω
      ∂pointCloudLaw (cascadeLaw ms)) / _ = _
    rw [hw]
    have hmeans : ((rpcWeightedBlocks ms bs).map (fun b => weightedChildMean (cascadeLaw ms) m X b.2)) =
        bs.map (fun b => ENNReal.ofReal (rpcPatternProduct ms m b)) := by
      exact (List.map_map (l := bs)).trans (List.map_congr_left hmean)
    have hsizes : (rpcWeightedBlocks ms bs).map Prod.fst =
        bs.map (replicaPatternSize ms.length) := List.map_map (l := bs)
    rw [hmeans, hsizes]
    change ENNReal.ofReal (partitionProduct m η (bs.map (replicaPatternSize ms.length))) *
      (bs.map (fun b => ENNReal.ofReal (rpcPatternProduct ms m b))).prod =
      ENNReal.ofReal (partitionProduct m η (bs.map (replicaPatternSize ms.length)) *
        (bs.map (rpcPatternProduct ms m)).prod)
    rw [ENNReal.ofReal_mul (partitionProduct_nonneg hm.1.le hm.2 hηm' _),
      ofReal_list_prod (by
        intro x hx
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
        exact rpcPatternProduct_nonneg ms htail ht01 m hmchild b)]
    exact congrArg (fun xs : List ℝ≥0∞ =>
      ENNReal.ofReal (partitionProduct m η (bs.map (replicaPatternSize ms.length))) * xs.prod)
      (List.map_map (l := bs) (f := rpcPatternProduct ms m) (g := ENNReal.ofReal)).symm
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma tsum_cascadePathWeight (ms : List ℝ) (ω : CascadeTree ms.length) :
    (∑' ℓ : CascadePath ms.length, cascadePathWeight ms ω ℓ) = cascadeTotal ms ω := by
  induction ms with
  | nil => simp [cascadePathWeight, cascadeTotal, CascadePath]
  | cons m ms ih =>
    change PointCloud (CascadeTree ms.length) at ω
    change (∑' ℓ : (ℕ × ℕ) × CascadePath ms.length,
      if ℓ.1.2 < (ω ℓ.1.1).1 then
        ENNReal.ofReal (((ℓ.1.1:ℝ)+((ω ℓ.1.1).2 ℓ.1.2).1)^(-1/m)) *
          cascadePathWeight ms ((ω ℓ.1.1).2 ℓ.1.2).2 ℓ.2 else 0) = _
    rw [ENNReal.tsum_prod']
    have he (i : ℕ × ℕ) : (∑' ℓ : CascadePath ms.length,
        cascadePathWeight (m::ms) ω (i,ℓ)) =
        if i.2 < (ω i.1).1 then
          ENNReal.ofReal (((i.1:ℝ)+((ω i.1).2 i.2).1)^(-1/m)) *
            cascadeTotal ms ((ω i.1).2 i.2).2 else 0 := by
      by_cases hi : i.2 < (ω i.1).1
      · simp only [cascadePathWeight, ite_eq_left hi]
        rw [ENNReal.tsum_mul_left, ih]
      · simp [cascadePathWeight,hi]
    change (∑' i : ℕ × ℕ, ∑' ℓ : CascadePath ms.length,
      cascadePathWeight (m::ms) ω (i,ℓ)) = _
    simp_rw [he]
    rw [ENNReal.tsum_prod']
    simp only [cascadeTotal, pointCloudFunctional, poissonBinSum]
    apply tsum_congr
    intro n
    rw [tsum_eq_sum (s := Finset.range (ω n).1) (fun j hj => by
      simp only [Finset.mem_range, not_lt] at hj
      simp [not_lt.mpr hj])]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [Finset.mem_range.mp hj, ite_true]

lemma cascadePathWeights_sum_one (ms : List ℝ) (ω : CascadeTree ms.length)
    (hp : 0 < cascadeTotal ms ω) (hf : cascadeTotal ms ω < ∞) :
    (∑' ℓ : CascadePath ms.length, cascadePathWeight ms ω ℓ / cascadeTotal ms ω) = 1 := by
  simp only [div_eq_mul_inv, ENNReal.tsum_mul_right, tsum_cascadePathWeight]
  exact ENNReal.mul_inv_cancel hp.ne' hf.ne

theorem rpcLabelSampling : RPCLabelSamplingStatement := by
  intro ms hms h01
  refine ⟨?_, ?_⟩
  · exact (cascadeNormalization ms hms h01).1.mono fun ω hω =>
      cascadePathWeights_sum_one ms ω hω.1 hω.2
  · intro η hη hηms b hb
    have he := rpcLabelPatternWeight_eq_ae ms
    have hi : (fun ω => ENNReal.ofReal ((cascadeTotal ms ω).toReal^η)*rpcLabelPatternWeight ms b ω) =ᵐ[cascadeLaw ms]
        (fun ω => ENNReal.ofReal ((cascadeTotal ms ω).toReal^η)*rpcPatternWeight ms b ω) :=
      he.mono fun ω hω => by dsimp only; rw [hω b]
    rw [lintegral_congr_ae hi]
    exact rpcPartition ms hms h01 η hη hηms b hb
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators Classical

namespace MicroscopicJamming

lemma measurable_cascadePathWeight (ms : List ℝ) (ℓ : CascadePath ms.length) :
    Measurable (fun ω => cascadePathWeight ms ω ℓ) := by
  induction ms with
  | nil => exact measurable_const
  | cons m ms ih =>
    change (ℕ × ℕ) × CascadePath ms.length at ℓ
    change Measurable (fun ω : PointCloud (CascadeTree ms.length) =>
      if ℓ.1.2 < (ω ℓ.1.1).1 then
        ENNReal.ofReal (((ℓ.1.1:ℝ)+((ω ℓ.1.1).2 ℓ.1.2).1)^(-1/m)) *
          cascadePathWeight ms ((ω ℓ.1.1).2 ℓ.1.2).2 ℓ.2 else 0)
    apply Measurable.ite
    · exact measurableSet_lt measurable_const ((measurable_pi_apply _).fst)
    · exact (by fun_prop : Measurable (fun ω : PointCloud (CascadeTree ms.length) =>
        ENNReal.ofReal (((ℓ.1.1:ℝ)+((ω ℓ.1.1).2 ℓ.1.2).1)^(-1/m)))).mul
        ((ih ℓ.2).comp (by fun_prop))
    · exact measurable_const

lemma cascadeLeafLaw_apply_good (ms : List ℝ) (ω : CascadeTree ms.length)
    (hω : 0 < cascadeTotal ms ω ∧ cascadeTotal ms ω < ∞) (A : Set (CascadePath ms.length)) :
    cascadeLeafLaw ms ω A = ∑' ℓ, if ℓ ∈ A then
      cascadePathWeight ms ω ℓ / cascadeTotal ms ω else 0 := by
  classical
  simp only [cascadeLeafLaw, ite_eq_left hω, Measure.sum_apply _ (show MeasurableSet A from trivial),
    Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (show MeasurableSet A from trivial)]
  apply tsum_congr
  intro ℓ
  by_cases hℓ : ℓ ∈ A <;> simp [hℓ]

lemma cascadeLeafLaw_probability (ms : List ℝ) (ω : CascadeTree ms.length) :
    IsProbabilityMeasure (cascadeLeafLaw ms ω) := by
  classical
  by_cases hω : 0 < cascadeTotal ms ω ∧ cascadeTotal ms ω < ∞
  · constructor
    simpa only [cascadeLeafLaw_apply_good ms ω hω, mem_univ, ite_true]
      using cascadePathWeights_sum_one ms ω hω.1 hω.2
  · simp only [cascadeLeafLaw, ite_eq_right hω]
    infer_instance

lemma measurable_cascadeLeafLaw (ms : List ℝ) : Measurable (cascadeLeafLaw ms) := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro A hA
  have hu : Measurable (fun ω : CascadeTree ms.length =>
      ∑' ℓ, if ℓ ∈ A then cascadePathWeight ms ω ℓ / cascadeTotal ms ω else 0) := by
    apply Measurable.tsum
    intro ℓ
    by_cases hℓ : ℓ ∈ A
    · simpa only [ite_eq_left hℓ, Pi.div_def] using
        (measurable_cascadePathWeight ms ℓ).div (measurable_cascadeTotal ms)
    · simp only [ite_eq_right hℓ]; exact measurable_const
  have hg : MeasurableSet {ω | 0 < cascadeTotal ms ω ∧ cascadeTotal ms ω < ∞} :=
    (measurableSet_lt measurable_const (measurable_cascadeTotal ms)).inter
      (measurableSet_lt (measurable_cascadeTotal ms) measurable_const)
  have he : (fun ω => cascadeLeafLaw ms ω A) =
      (fun ω => if 0 < cascadeTotal ms ω ∧ cascadeTotal ms ω < ∞ then
        ∑' ℓ, if ℓ ∈ A then cascadePathWeight ms ω ℓ / cascadeTotal ms ω else 0
      else Measure.dirac (cascadeZeroPath ms.length) A) := by
    funext ω
    by_cases hω : 0 < cascadeTotal ms ω ∧ cascadeTotal ms ω < ∞
    · simp only [ite_eq_left hω, cascadeLeafLaw_apply_good ms ω hω]
    · simp only [cascadeLeafLaw, ite_eq_right hω]
  rw [he]
  exact hu.ite hg measurable_const

 
lemma measurable_infinitePi_kernel {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    (G : Ω → Measure A) (hG : Measurable G) [∀ ω, IsProbabilityMeasure (G ω)] :
    Measurable (fun ω => Measure.infinitePi (fun _ : ℕ => G ω)) := by
  apply Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
    generateFrom_squareCylinders.symm
    (isPiSystem_squareCylinders (fun _ => MeasurableSpace.isPiSystem_measurableSet) (by simp))
  rintro S ⟨I,A,hA,rfl⟩
  have ht (i : ℕ) : MeasurableSet (A i) := hA i (mem_univ i)
  simp_rw [Measure.infinitePi_pi _ (fun i _ => ht i)]
  exact Finset.measurable_fun_prod I (fun i _ => (Measure.measurable_coe (ht i)).comp hG)

lemma cascadeLeafLaw_singleton_good (ms : List ℝ) (ω : CascadeTree ms.length)
    (hω : 0 < cascadeTotal ms ω ∧ cascadeTotal ms ω < ∞) (ℓ : CascadePath ms.length) :
    cascadeLeafLaw ms ω {ℓ} = cascadePathWeight ms ω ℓ / cascadeTotal ms ω := by
  classical
  rw [cascadeLeafLaw_apply_good ms ω hω]
  simp only [mem_singleton_iff, tsum_ite_eq]

lemma measurable_cascadeReplicaKernel (ms : List ℝ) :
    Measurable (fun ω => Measure.infinitePi (fun _ : ℕ => cascadeLeafLaw ms ω)) := by
  let := cascadeLeafLaw_probability ms
  exact measurable_infinitePi_kernel _ (measurable_cascadeLeafLaw ms)

lemma cascadeReplicaLaw_probability (ms : List ℝ) : IsProbabilityMeasure (cascadeReplicaLaw ms) := by
  let := cascadeLeafLaw_probability ms
  constructor
  rw [cascadeReplicaLaw, Measure.bind_apply MeasurableSet.univ
    (measurable_cascadeReplicaKernel ms).aemeasurable]
  simp

lemma cascadeReplicaLaw_cylinder (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) (I : Finset ℕ)
    (ℓ : ℕ → CascadePath ms.length) :
    cascadeReplicaLaw ms {x | ∀ i ∈ I, x i = ℓ i} =
      ∫⁻ ω, ∏ i ∈ I, cascadePathWeight ms ω (ℓ i) / cascadeTotal ms ω ∂cascadeLaw ms := by
  let := cascadeLeafLaw_probability ms
  have hset : {x : ℕ → CascadePath ms.length | ∀ i ∈ I, x i = ℓ i} =
      (I : Set ℕ).pi (fun i => {ℓ i}) := by ext x; simp
  rw [hset, cascadeReplicaLaw, Measure.bind_apply (MeasurableSet.pi I.countable_toSet (fun i _ => measurableSet_singleton (ℓ i)))
    (measurable_cascadeReplicaKernel ms).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [(cascadeNormalization ms hms h01).1] with ω hω
  rw [Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton (ℓ i))]
  apply Finset.prod_congr rfl
  intro i hi
  exact cascadeLeafLaw_singleton_good ms ω hω (ℓ i)

theorem rpcLeafKernel : RPCLeafKernelStatement := by
  constructor
  · intro ms
    exact ⟨measurable_cascadeLeafLaw ms, cascadeLeafLaw_probability ms,
      measurable_cascadeReplicaKernel ms, cascadeReplicaLaw_probability ms⟩
  · intro ms hms h01
    exact ⟨((cascadeNormalization ms hms h01).1).mono (fun ω hω ℓ =>
      cascadeLeafLaw_singleton_good ms ω hω ℓ), cascadeReplicaLaw_cylinder ms hms h01⟩
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

abbrev RowReplicaEnvironment (k : ℕ) := CascadeTree k × (Option (CascadeMarkIndex k) → ℝ)
abbrev RowReplicaSite (k : ℕ) := CascadePath k × ℝ

def rowReplicaEnvironmentLaw (ms : List ℝ) (d : ℕ → ℝ≥0) (p₀ : ℝ≥0) :
    Measure (RowReplicaEnvironment ms.length) :=
  (cascadeLaw ms).prod (Measure.infinitePi (fun a => gaussianReal 0 (rootCoordinateVariance ms.length d p₀ a)))

def rowReplicaKernel (ms : List ℝ) (Δ : ℝ≥0) : Kernel (RowReplicaEnvironment ms.length) (RowReplicaSite ms.length) where
  toFun ω := (cascadeLeafLaw ms ω.1).prod (gaussianReal 0 Δ)
  measurable' := by
    let K : Kernel (RowReplicaEnvironment ms.length) (CascadePath ms.length) :=
      ⟨fun ω => cascadeLeafLaw ms ω.1, (measurable_cascadeLeafLaw ms).comp measurable_fst⟩
    have : IsMarkovKernel K := ⟨fun ω => cascadeLeafLaw_probability ms ω.1⟩
    have h : Measurable (fun ω =>
        (K.prod (Kernel.const (RowReplicaEnvironment ms.length) (gaussianReal 0 Δ))) ω) :=
      (K.prod (Kernel.const (RowReplicaEnvironment ms.length) (gaussianReal 0 Δ))).measurable
    simpa only [Kernel.prod_apply, Kernel.const_apply, K, Kernel.coe_mk] using h

instance rowReplicaKernel_markov (ms : List ℝ) (Δ : ℝ≥0) : IsMarkovKernel (rowReplicaKernel ms Δ) :=
  ⟨fun ω => by
    change IsProbabilityMeasure ((cascadeLeafLaw ms ω.1).prod (gaussianReal 0 Δ))
    let := cascadeLeafLaw_probability ms ω.1
    infer_instance⟩

def rowReplicaSiteField (k : ℕ) (z : RowReplicaEnvironment k × RowReplicaSite k) : ℝ :=
  rootPathField k z.1.2 z.2.1 + z.2.2

def rowReplicaKernelView (k r : ℕ) (z : RowReplicaEnvironment k × (Fin r → RowReplicaSite k)) :
    RowRankSignature r × EuclideanSpace ℝ (Fin r) :=
  (cascadeGenealogySignature k r (fun i => (z.2 i).1),WithLp.toLp 2 (fun i => rowReplicaSiteField k (z.1,z.2 i)))

def RowReplicaKernelStatement : Prop :=
  ∀ (ms : List ℝ), ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (r : ℕ) (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0),
    ((rowReplicaEnvironmentLaw ms d p₀) ⊗ₘ replicaKernel (rowReplicaKernel ms Δ) r).map
      (rowReplicaKernelView ms.length r) =
      gaussianAdjunctionMeasure r (rowSignatureCovariance ms.length r d p₀ Δ)
        (realizedRankLaw.map (rankGenealogySignature ms r))
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
 

def rowCoordinateLeafKernel (ms : List ℝ) :
    Kernel (RowReplicaEnvironment ms.length) (CascadePath ms.length) :=
  ⟨fun ω => cascadeLeafLaw ms ω.1, (measurable_cascadeLeafLaw ms).comp measurable_fst⟩
instance (ms : List ℝ) : IsMarkovKernel (rowCoordinateLeafKernel ms) :=
  ⟨fun ω => cascadeLeafLaw_probability ms ω.1⟩
def rowCoordinatePotential (ms : List ℝ) (v : ℝ → ℝ)
    (z : RowReplicaEnvironment ms.length × CascadePath ms.length) : ℝ :=
  v (rootPathField ms.length z.1.2 z.2)
def rowCoordinatePair (ms : List ℝ) (v : ℝ → ℝ) (B : ℕ → ℝ)
    (z : RowReplicaEnvironment ms.length × (Fin 2 → CascadePath ms.length)) : ℝ :=
  B (cascadeSharedEdges ms.length (z.2 0) (z.2 1)) *
    (deriv v (rootPathField ms.length z.1.2 (z.2 0)) *
      deriv v (rootPathField ms.length z.1.2 (z.2 1)))
def RowDirectingPairStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) (B : ℕ → ℝ),
    let v := gaussianRowOperator 1 Δ u
    (∫ ω, replicaNum (rowCoordinateLeafKernel ms) (rowCoordinatePotential ms v)
        (rowCoordinatePair ms v B) ω /
      (replicaZ (rowCoordinateLeafKernel ms) (rowCoordinatePotential ms v) ω)^2
        ∂rowReplicaEnvironmentLaw ms d p₀) =
    ∫ x, (∫ s in (0:ℝ)..1, B (rpcStepLevel ms s) *
      rowDerivativeDepthMoment (rowGaussianBlocks ms d) v (rpcStepLevel ms s) x)
        ∂gaussianReal 0 p₀
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
def rowFullPotential (ms : List ℝ) (u : ℝ → ℝ)
    (z : RowReplicaEnvironment ms.length × RowReplicaSite ms.length) : ℝ :=
  u (rowReplicaSiteField ms.length z)
def rowFullPair (ms : List ℝ) (u : ℝ → ℝ) (B : ℕ → ℝ)
    (z : RowReplicaEnvironment ms.length × (Fin 2 → RowReplicaSite ms.length)) : ℝ :=
  B (cascadeSharedEdges ms.length (z.2 0).1 (z.2 1).1) *
    (deriv u (rowReplicaSiteField ms.length (z.1,z.2 0)) *
      deriv u (rowReplicaSiteField ms.length (z.1,z.2 1)))
 

def RowResidualPairStatement : Prop :=
  ∀ (u : ℝ → ℝ) (L H : ℝ), ContDiff ℝ 2 u → 0 ≤ L → 0 ≤ H →
    (∀ x, |deriv u x| ≤ L ∧ |deriv (deriv u) x| ≤ H) →
  ∀ ms : List ℝ, ms.Pairwise (· < ·) → (∀ m ∈ ms, 0 < m ∧ m < 1) →
  ∀ (d : ℕ → ℝ≥0) (p₀ Δ : ℝ≥0) (B : ℕ → ℝ),
    let v := gaussianRowOperator 1 Δ u
    (∫ ω, replicaNum (rowReplicaKernel ms Δ) (rowFullPotential ms u)
        (rowFullPair ms u B) ω /
      (replicaZ (rowReplicaKernel ms Δ) (rowFullPotential ms u) ω)^2
        ∂rowReplicaEnvironmentLaw ms d p₀) =
    ∫ x, (∫ s in (0:ℝ)..1, B (rpcStepLevel ms s) *
      rowDerivativeDepthMoment (rowGaussianBlocks ms d) v (rpcStepLevel ms s) x)
        ∂gaussianReal 0 p₀
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators MatrixOrder

namespace MicroscopicJamming

instance gaussianMatrixMeasurable (d : ℕ) : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
  borel _
instance gaussianMatrixBorel (d : ℕ) : BorelSpace (Matrix (Fin d) (Fin d) ℝ) := ⟨rfl⟩

def gaussianObservableKernel {A : Type*} (d : ℕ)
    (C : A → Matrix (Fin d) (Fin d) ℝ)
    (F : A × EuclideanSpace ℝ (Fin d) → ℝ) (x : A) : ℝ :=
  ∫ z, F (gaussianAdjunctionMap d C (x,z)) ∂stdGaussian (EuclideanSpace ℝ (Fin d))

def GaussianConditionalL1Statement : Prop :=
  ∀ (A : Type) (mA : MeasurableSpace A) (μ : Measure A), IsProbabilityMeasure μ →
  ∀ (d : ℕ) (C : ℕ → A → Matrix (Fin d) (Fin d) ℝ)
    (C₀ : A → Matrix (Fin d) (Fin d) ℝ),
    (∀ n, Measurable (C n)) → Measurable C₀ →
    (∀ n x, (C n x).PosSemidef) → (∀ x, (C₀ x).PosSemidef) →
    (∃ B : ℝ, (∀ n x i j, |C n x i j| ≤ B) ∧ (∀ x i j, |C₀ x i j| ≤ B)) →
    (∀ᵐ x ∂μ, Tendsto (fun n => C n x) atTop (𝓝 (C₀ x))) →
  ∀ (F : A × EuclideanSpace ℝ (Fin d) → ℝ), Measurable F →
    (∀ x, Continuous (fun z => F (x,z))) → (∃ K : ℝ, ∀ z, |F z| ≤ K) →
    Tendsto (fun n => ∫ x, |gaussianObservableKernel d (C n) F x -
      gaussianObservableKernel d C₀ F x| ∂μ) atTop (𝓝 0) ∧
    ∀ (m : MeasurableSpace A), m ≤ mA →
      Tendsto (fun n => ∫ x,
        |μ[gaussianObservableKernel d (C n) F | m] x -
          μ[gaussianObservableKernel d C₀ F | m] x| ∂μ) atTop (𝓝 0)
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators

namespace MicroscopicJamming

structure SphericalProfile where
  val : ℝ → ℝ
  mono : MonotoneOn val (Set.Icc 0 1)
  nonneg : ∀ s ∈ Set.Icc 0 1, 0 ≤ val s

def sphericalProfileDistance (p q : ℝ → ℝ) : ℝ := ∫ s in (0:ℝ)..1, |p s-q s|

lemma SphericalProfile.bound (p : SphericalProfile) (s : ℝ) (hs : s ∈ Set.Icc 0 1) :
    0 ≤ p.val s ∧ p.val s ≤ p.val 1 :=
  ⟨p.nonneg s hs, p.mono hs (by norm_num) hs.2⟩
end MicroscopicJamming

end

end OAI
