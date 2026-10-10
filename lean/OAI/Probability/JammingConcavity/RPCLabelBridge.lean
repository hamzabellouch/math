import Mathlib
import OAI.Probability.JammingConcavity.RowReplicaMixture

namespace OAI

/-! R P C Label Bridge. -/

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

lemma lintegral_pointCloudMeasure_labels {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] (ω : PointCloud A) (f : ℝ × A → ℝ≥0∞) :
    (∫⁻ z, f z ∂pointCloudMeasure ω) =
      ∑' i : CloudLabel, if i.2 < (ω i.1).1 then f (cloudLabelPoint ω i) else 0 := by
  classical
  rw [ENNReal.tsum_prod']
  simp only [pointCloudMeasure, lintegral_sum_measure]
  apply tsum_congr
  intro n
  apply tsum_congr
  intro j
  split_ifs <;> simp [lintegral_dirac, cloudLabelPoint]

lemma labelCloudIntegral_points {A : Type*} [MeasurableSpace A]
    [MeasurableSingletonClass A] (ω : PointCloud A)
    (hinj : Function.Injective (cloudLabelPoint ω))
    (fs : List ((ℝ × A) → ℝ≥0∞)) (xs : List CloudLabel) :
    labelCloudIntegral (fs.map (fun f => f ∘ cloudLabelPoint ω)) ω xs =
      distinctCloudIntegral fs (pointCloudMeasure ω) (xs.map (cloudLabelPoint ω)) := by
  classical
  induction fs generalizing xs with
  | nil => rfl
  | cons f fs ih =>
    rw [List.map_cons, labelCloudIntegral, distinctCloudIntegral,
      lintegral_pointCloudMeasure_labels]
    apply tsum_congr
    intro i
    have hmem : cloudLabelPoint ω i ∈ xs.map (cloudLabelPoint ω) ↔ i ∈ xs := by
      constructor
      · intro h
        obtain ⟨j,hj,hji⟩ := List.mem_map.mp h
        rwa [hinj hji] at hj
      · exact List.mem_map_of_mem
    by_cases ha : i.2 < (ω i.1).1
    · by_cases hi : i ∈ xs
      · simp [ha,hi,hmem]
      · simp only [ha, hi, not_false_eq_true, and_self, ite_true, hmem, ite_false,
          Function.comp_apply]
        rw [ih]
        rfl
    · simp [ha]

instance replicaPatternEncodable : (k : ℕ) → Encodable (ReplicaPattern k)
  | 0 => inferInstanceAs (Encodable ℕ)
  | k+1 => by
    letI := replicaPatternEncodable k
    exact inferInstanceAs (Encodable (List (ReplicaPattern k)))

lemma rpcLabelPatternWeight_eq_ae (ms : List ℝ) :
    ∀ᵐ ω ∂cascadeLaw ms, ∀ b : ReplicaPattern ms.length,
      rpcLabelPatternWeight ms b ω = rpcPatternWeight ms b ω := by
  induction ms with
  | nil => exact Eventually.of_forall fun ω b => rfl
  | cons m ms ih =>
    have hc := ae_pointCloud_marks (cascadeLaw ms) ih
    filter_upwards [cloudLabelPoint_injective_ae (cascadeLaw ms), hc] with ω hω hchild
    intro bs
    change PointCloud (CascadeTree ms.length) at ω
    change List (ReplicaPattern ms.length) at bs
    change ENNReal.ofReal ((cascadeTotal (m::ms) ω).toReal ^
      (-(replicaPatternSize (ms.length+1) bs : ℝ))) * _ = _
    change ENNReal.ofReal ((cascadeTotal (m::ms) ω).toReal ^
      (-(replicaPatternSize (ms.length+1) bs : ℝ))) * _ =
      ENNReal.ofReal ((cascadeTotal (m::ms) ω).toReal ^
      (-(replicaPatternSize (ms.length+1) bs : ℝ))) *
      distinctCloudIntegral (bs.map (fun b (z : ℝ × CascadeTree ms.length) =>
        (ENNReal.ofReal (z.1^(-1/m))*cascadeTotal ms z.2)^(replicaPatternSize ms.length b) *
          rpcPatternWeight ms b z.2)) (pointCloudMeasure ω) []
    congr 1
    let fs : List ((ℝ × CascadeTree ms.length) → ℝ≥0∞) := bs.map (fun b z =>
      (ENNReal.ofReal (z.1^(-1/m))*cascadeTotal ms z.2)^(replicaPatternSize ms.length b) *
        rpcPatternWeight ms b z.2)
    have he : (bs.map (fun b i =>
        (ENNReal.ofReal ((cloudLabelPoint ω i).1^(-1/m)) *
          cascadeTotal ms (cloudLabelPoint ω i).2)^(replicaPatternSize ms.length b) *
          rpcLabelPatternWeight ms b (cloudLabelPoint ω i).2)) =
        fs.map (fun f => f ∘ cloudLabelPoint ω) := by
      dsimp only [fs]
      rw [List.map_map]
      apply List.map_congr_left
      intro b hb
      funext i
      dsimp only [Function.comp_apply, cloudLabelPoint]
      rw [hchild i.1 i.2 b]
    rw [he]
    exact labelCloudIntegral_points ω hω fs []
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma ae_cloud_measure_marks {A : Type*} [MeasurableSpace A] [MeasurableSingletonClass (ℝ × A)]
    {ω : PointCloud A} {p : A → Prop} (h : ∀ n j, p ((ω n).2 j).2) :
    ∀ᵐ z ∂pointCloudMeasure ω, p z.2 := by
  classical
  simp only [pointCloudMeasure, Measure.ae_sum_iff]
  intro n j
  split_ifs
  · simpa only [ae_dirac_eq, Filter.eventually_pure] using h n j
  · simp

lemma distinctCloudIntegral_congr_ae {X B : Type*} [MeasurableSpace X]
    (bs : List B) (f g : B → X → ℝ≥0∞) (μ : Measure X)
    (h : ∀ b ∈ bs, f b =ᵐ[μ] g b) (xs : List X) :
    distinctCloudIntegral (bs.map f) μ xs = distinctCloudIntegral (bs.map g) μ xs := by
  induction bs generalizing xs with
  | nil => rfl
  | cons b bs ih =>
    have htail : ∀ b ∈ bs, f b =ᵐ[μ] g b := fun b hb => h b (by simp [hb])
    simp only [List.map_cons, distinctCloudIntegral]
    apply lintegral_congr_ae
    filter_upwards [h b (by simp)] with z hz
    split_ifs
    · rfl
    · rw [hz, ih htail]

lemma exp_log_cascadeTotal_ae (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) :
    ∀ᵐ ω ∂cascadeLaw ms,
      ENNReal.ofReal (Real.exp (Real.log (cascadeTotal ms ω).toReal)) = cascadeTotal ms ω := by
  filter_upwards [(cascadeTotal_properties ms hms h01).1] with ω hω
  rw [Real.exp_log (ENNReal.toReal_pos hω.1.ne' hω.2.ne), ENNReal.ofReal_toReal hω.2.ne]

lemma cascadeTotal_expMarked_ae {ms : List ℝ} {m : ℝ} (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) :
    cascadeTotal (m::ms) =ᵐ[cascadeLaw (m::ms)]
      expMarkedTotal m (fun ω => Real.log (cascadeTotal ms ω).toReal) := by
  have hX : Measurable (fun ω => Real.log (cascadeTotal ms ω).toReal) := by
    exact (measurable_cascadeTotal ms).ennreal_toReal.log
  have he := pointCloudFunctional_mark_congr (cascadeLaw ms)
    (f := fun z : ℝ × CascadeTree ms.length => ENNReal.ofReal (z.1^(-1/m))*cascadeTotal ms z.2)
    (g := expMarkedJump m (fun ω => Real.log (cascadeTotal ms ω).toReal))
    ((exp_log_cascadeTotal_ae ms hms h01).mono fun a ha =>
      show ∀ x : ℝ, ENNReal.ofReal (x^(-1/m))*cascadeTotal ms a =
        expMarkedJump m (fun ω => Real.log (cascadeTotal ms ω).toReal) (x,a) by
        intro x; simp only [expMarkedJump, ha])
  filter_upwards [he] with ω hω
  have hj := expMarkedTotal_integral m hX (ω : PointCloud (CascadeTree ms.length))
  have hk := lintegral_pointCloudMeasure (measurable_expMarkedJump m hX)
    (ω : PointCloud (CascadeTree ms.length))
  exact hω.trans (hk.symm.trans hj.symm)

lemma exp_mul_log_cascadeTotal_ae (ms : List ℝ) (hms : ms.Pairwise (· < ·))
    (h01 : ∀ m ∈ ms, 0 < m ∧ m < 1) (a : ℝ) :
    (fun ω => Real.exp (a*Real.log (cascadeTotal ms ω).toReal)) =ᵐ[cascadeLaw ms]
      (fun ω => (cascadeTotal ms ω).toReal^a) := by
  filter_upwards [(cascadeTotal_properties ms hms h01).1] with ω hω
  rw [Real.rpow_def_of_pos (ENNReal.toReal_pos hω.1.ne' hω.2.ne), mul_comm a]
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma gamma_lintegral {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(a-1))*ENNReal.ofReal (Real.exp (-t*s))) =
      ENNReal.ofReal (Real.Gamma a*s^(-a)) := by
  have hi : IntegrableOn (fun t : ℝ => t^(a-1)*Real.exp (-s*t)) (Set.Ioi 0) := by
    simpa only [Real.rpow_one] using
      integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < a-1) (by norm_num : (0:ℝ)<1) hs
  have he : (fun t : ℝ => ENNReal.ofReal (t^(a-1))*ENNReal.ofReal (Real.exp (-t*s)))
      =ᵐ[volume.restrict (Set.Ioi 0)] (fun t => ENNReal.ofReal (t^(a-1)*Real.exp (-s*t))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)]
    rw [show -t*s = -s*t by ring]
  rw [lintegral_congr_ae he, ← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)]
  have hv : (∫ t in Set.Ioi (0:ℝ), t^(a-1)*Real.exp (-s*t)) =
      (1/s)^a*Real.Gamma a := by
    simpa only [neg_mul] using Real.integral_rpow_mul_exp_neg_mul_Ioi ha hs
  rw [hv]
  congr 1
  rw [one_div, Real.inv_rpow hs.le, Real.rpow_neg hs.le]
  ring

lemma mellin_negative_power {a s : ℝ} (ha : 0 < a) (hs : 0 < s) :
    ENNReal.ofReal (s^(-a)) = (ENNReal.ofReal (Real.Gamma a))⁻¹ *
      ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(a-1))*ENNReal.ofReal (Real.exp (-t*s)) := by
  rw [gamma_lintegral ha hs, ENNReal.ofReal_mul (Real.Gamma_pos_of_pos ha).le,
    ← mul_assoc, ENNReal.inv_mul_cancel (by positivity : ENNReal.ofReal (Real.Gamma a) ≠ 0)
      ENNReal.ofReal_ne_top, one_mul]
lemma generalized_gamma_lintegral {m a b : ℝ} (hm : 0 < m) (ha : 0 < a) (hb : 0 < b) :
    (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(a-1)*Real.exp (-b*t^m))) =
      ENNReal.ofReal (b^(-a/m)*(1/m)*Real.Gamma (a/m)) := by
  have hi := integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith : -1 < a-1) hm hb
  rw [← ofReal_integral_eq_lintegral_ofReal hi (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (Real.rpow_nonneg ht.le _) (Real.exp_pos _).le)]
  have hv := integral_rpow_mul_exp_neg_mul_rpow hm (by linarith : -1 < a-1) hb
  simpa only [sub_add_cancel, neg_div] using congrArg ENNReal.ofReal hv

end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma weighted_mellin_lintegral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    {S D : Ω → ℝ≥0∞} (hS : Measurable S) (hD : AEMeasurable D μ)
    (hs : ∀ᵐ ω ∂μ, 0 < S ω ∧ S ω < ∞) {a : ℝ} (ha : 0 < a) :
    (∫⁻ ω, ENNReal.ofReal ((S ω).toReal^(-a))*D ω ∂μ) =
      (ENNReal.ofReal (Real.Gamma a))⁻¹ * ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(a-1)) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp (-t*(S ω).toReal))*D ω ∂μ) := by
  have he : (fun ω => ENNReal.ofReal ((S ω).toReal^(-a))*D ω) =ᵐ[μ]
      (fun ω => (ENNReal.ofReal (Real.Gamma a))⁻¹ *
        ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^(a-1))*ENNReal.ofReal (Real.exp (-t*(S ω).toReal))*D ω) := by
    filter_upwards [hs] with ω hω
    rw [mellin_negative_power ha (ENNReal.toReal_pos hω.1.ne' hω.2.ne),
      mul_assoc, lintegral_mul_const'' _ (by fun_prop)]
  have hF : AEMeasurable (fun z : Ω × ℝ => ENNReal.ofReal (z.2^(a-1))*
      ENNReal.ofReal (Real.exp (-z.2*(S z.1).toReal))*D z.1)
      (μ.prod (volume.restrict (Set.Ioi 0))) := by
    apply AEMeasurable.mul _ hD.comp_fst
    apply Measurable.aemeasurable
    fun_prop
  rw [lintegral_congr_ae he, lintegral_const_mul' _ _ (by finiteness), lintegral_lintegral_swap hF]
  congr 1
  apply lintegral_congr
  intro t
  simp only [mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma weighted_mellin_comparison {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    (μ : Measure Ω) (ν : Measure Ω') [SFinite μ] [SFinite ν]
    {S D : Ω → ℝ≥0∞} {S' D' : Ω' → ℝ≥0∞}
    (hS : Measurable S) (hD : AEMeasurable D μ) (hS' : Measurable S') (hD' : AEMeasurable D' ν)
    (hs : ∀ᵐ ω ∂μ, 0 < S ω ∧ S ω < ∞) (hs' : ∀ᵐ ω ∂ν, 0 < S' ω ∧ S' ω < ∞)
    {a : ℝ} (ha : 0 < a) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hL : ∀ t : ℝ, 0 < t →
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-t*(S ω).toReal))*D ω ∂μ) =
      C*(∫⁻ ω, ENNReal.ofReal (Real.exp (-t*(S' ω).toReal))*D' ω ∂ν)) :
    (∫⁻ ω, ENNReal.ofReal ((S ω).toReal^(-a))*D ω ∂μ) =
      C*(∫⁻ ω, ENNReal.ofReal ((S' ω).toReal^(-a))*D' ω ∂ν) := by
  rw [weighted_mellin_lintegral μ hS hD hs ha, weighted_mellin_lintegral ν hS' hD' hs' ha]
  have he : (fun t : ℝ => ENNReal.ofReal (t^(a-1))*
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-t*(S ω).toReal))*D ω ∂μ)) =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t => C*(ENNReal.ofReal (t^(a-1))*
        (∫⁻ ω, ENNReal.ofReal (Real.exp (-t*(S' ω).toReal))*D' ω ∂ν))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [hL t ht]; ac_rfl
  rw [lintegral_congr_ae he, lintegral_const_mul' _ _ hC]
  ac_rfl
end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def stableGammaProduct (m : ℝ) (ns : List ℕ) : ℝ :=
  (ns.map (fun n : ℕ => Real.Gamma ((n:ℝ)-m))).prod

lemma stableGammaProduct_pos {m : ℝ} (hm1 : m < 1) (ns : List ℕ)
    (hns : ∀ n ∈ ns, 0 < n) : 0 < stableGammaProduct m ns := by
  unfold stableGammaProduct
  apply List.prod_pos
  intro x hx
  obtain ⟨n, hn, rfl⟩ := List.mem_map.mp hx
  apply Real.Gamma_pos_of_pos
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hns n hn
  linarith

lemma stable_gamma_factor_product {m c t : ℝ} (hm : 0 < m) (hm1 : m < 1)
    (hc : 0 < c) (ht : 0 < t) (ns : List ℕ) (hns : ∀ n ∈ ns, 0 < n) :
    (ns.map (fun n : ℕ => ENNReal.ofReal (c*m*Real.Gamma ((n:ℝ)-m)*t^(m-(n:ℝ))))).prod =
      ENNReal.ofReal ((c*m)^ns.length * stableGammaProduct m ns *
        t^((ns.length:ℝ)*m-(ns.sum:ℝ))) := by
  induction ns with
  | nil => simp [stableGammaProduct]
  | cons n ns ih =>
    have hn := hns n (by simp)
    have htail : ∀ n ∈ ns, 0 < n := fun n hn => hns n (by simp [hn])
    have hgn : 0 < Real.Gamma ((n:ℝ)-m) := by
      apply Real.Gamma_pos_of_pos
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
      linarith
    simp only [List.map_cons, List.prod_cons, ih htail, List.length_cons, List.sum_cons,
      Nat.cast_add, Nat.cast_one]
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    simp only [stableGammaProduct, List.map_cons, List.prod_cons, pow_succ]
    rw [show ((ns.length:ℝ)+1)*m-((n:ℝ)+(ns.sum:ℝ)) =
      (m-(n:ℝ))+((ns.length:ℝ)*m-(ns.sum:ℝ)) by ring, Real.rpow_add ht]
    ring

lemma stable_mellin_factorial {m c η : ℝ} (hm : 0 < m) (hm1 : m < 1) (hc : 0 < c)
    (ns : List ℕ) (ha : 0 < (ns.sum:ℝ)-η) :
    (∫⁻ ω, poissonPartitionNumerator m c η ns ω ∂pointCloudLaw (Measure.dirac ())) =
      (ENNReal.ofReal (Real.Gamma ((ns.sum:ℝ)-η)))⁻¹ *
      ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^((ns.sum:ℝ)-η-1)) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp (-t*(stableTotal m c ω).toReal)) *
          distinctCloudIntegral (ns.map (fun n z => stableJump m c z^n)) (pointCloudMeasure ω) []
          ∂pointCloudLaw (Measure.dirac ())) := by
  let μ := pointCloudLaw (Measure.dirac ())
  let D := fun ω : PointCloud Unit => distinctCloudIntegral
    (ns.map (fun n z => stableJump m c z^n)) (pointCloudMeasure ω) []
  have hfs : ∀ f ∈ ns.map (fun n z => stableJump m c z^n), Measurable f := by
    intro f hf
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hf
    exact (measurable_stableJump m c).pow_const n
  have hD : AEMeasurable D μ := aemeasurable_distinct_cloud _ _ hfs []
  have he : (fun ω => poissonPartitionNumerator m c η ns ω) =ᵐ[μ]
      (fun ω => (ENNReal.ofReal (Real.Gamma ((ns.sum:ℝ)-η)))⁻¹ *
        ∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal (t^((ns.sum:ℝ)-η-1)) *
          ENNReal.ofReal (Real.exp (-t*(stableTotal m c ω).toReal)) * D ω) := by
    filter_upwards [(stableTotal_properties hm hm1 hc).1] with ω hω
    have hs : 0 < (stableTotal m c ω).toReal := ENNReal.toReal_pos hω.1.ne' hω.2.ne
    unfold poissonPartitionNumerator
    rw [show η-(ns.sum:ℝ) = -((ns.sum:ℝ)-η) by ring, mellin_negative_power ha hs,
      mul_assoc, lintegral_mul_const'' _ (by fun_prop)]
  have hF : AEMeasurable (fun z : PointCloud Unit × ℝ => ENNReal.ofReal (z.2^((ns.sum:ℝ)-η-1)) *
      ENNReal.ofReal (Real.exp (-z.2*(stableTotal m c z.1).toReal)) * D z.1)
      (μ.prod (volume.restrict (Set.Ioi 0))) := by
    apply AEMeasurable.mul _ hD.comp_fst
    apply Measurable.aemeasurable
    have hS := measurable_stableTotal m c
    fun_prop
  change (∫⁻ ω, poissonPartitionNumerator m c η ns ω ∂μ) = _
  rw [lintegral_congr_ae he, lintegral_const_mul' _ _ (by finiteness),
    lintegral_lintegral_swap hF]
  congr 1
  apply lintegral_congr
  intro t
  simp only [mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

lemma stable_partition_numerator_value {m c η : ℝ} (hm : 0 < m) (hm1 : m < 1) (hc : 0 < c)
    (ns : List ℕ) (hns : ∀ n ∈ ns, 0 < n) (ha : 0 < (ns.sum:ℝ)-η)
    (hk : 0 < (ns.length:ℝ)*m-η) :
    (∫⁻ ω, poissonPartitionNumerator m c η ns ω ∂pointCloudLaw (Measure.dirac ())) =
      ENNReal.ofReal (((c*m)^ns.length*stableGammaProduct m ns) *
        ((c*Real.Gamma (1-m))^(-((ns.length:ℝ)*m-η)/m)*(1/m)*
          Real.Gamma (((ns.length:ℝ)*m-η)/m)) / Real.Gamma ((ns.sum:ℝ)-η)) := by
  have hb : 0 < c*Real.Gamma (1-m) := mul_pos hc (Real.Gamma_pos_of_pos (by linarith))
  have hC : 0 < (c*m)^ns.length*stableGammaProduct m ns :=
    mul_pos (pow_pos (mul_pos hc hm) _) (stableGammaProduct_pos hm1 ns hns)
  have hfs : ∀ f ∈ ns.map (fun n z => stableJump m c z^n), Measurable f := by
    intro f hf
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hf
    exact (measurable_stableJump m c).pow_const n
  rw [stable_mellin_factorial hm hm1 hc ns ha]
  have he : (fun t : ℝ => ENNReal.ofReal (t^((ns.sum:ℝ)-η-1)) *
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-t*(stableTotal m c ω).toReal)) *
        distinctCloudIntegral (ns.map (fun n z => stableJump m c z^n)) (pointCloudMeasure ω) []
        ∂pointCloudLaw (Measure.dirac ()))) =ᵐ[volume.restrict (Set.Ioi 0)]
      (fun t => ENNReal.ofReal ((c*m)^ns.length*stableGammaProduct m ns) *
        ENNReal.ofReal (t^((ns.length:ℝ)*m-η-1)*Real.exp (-(c*Real.Gamma (1-m))*t^m))) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [stable_factorial_laplace hm hm1 hc ht.le _ hfs]
    have hfactors : ((ns.map (fun n z => stableJump m c z^n)).map
        (fun f => ∫⁻ z, f z*ENNReal.ofReal (expNeg (ENNReal.ofReal t*stableJump m c z))
          ∂(volume.restrict (Set.Ioi 0)).prod (Measure.dirac ()))) =
        ns.map (fun n : ℕ => ENNReal.ofReal (c*m*Real.Gamma ((n:ℝ)-m)*t^(m-(n:ℝ)))) := by
      rw [List.map_map]
      apply List.map_congr_left
      intro n hn
      apply selected_jump_gamma hm hc ht n
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hns n hn
      linarith
    rw [hfactors, stable_gamma_factor_product hm hm1 hc ht ns hns,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← ENNReal.ofReal_mul hC.le]
    congr 1
    rw [show (ns.length:ℝ)*m-η-1 = ((ns.sum:ℝ)-η-1)+((ns.length:ℝ)*m-(ns.sum:ℝ)) by ring,
      Real.rpow_add ht]
    ring
  rw [lintegral_congr_ae he, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    generalized_gamma_lintegral hm hk hb, ← ENNReal.ofReal_mul hC.le,
    ← ENNReal.ofReal_inv_of_pos (Real.Gamma_pos_of_pos ha),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (Real.Gamma_pos_of_pos ha).le)]
  congr 1
  ring

end MicroscopicJamming

 
 
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma gamma_nat_sub_product {x : ℝ} (hx : x < 1) (n : ℕ) (hn : 0 < n) :
    Real.Gamma ((n:ℝ)-x) = Real.Gamma (1-x)*∏ a ∈ Finset.Ico 1 n, ((a:ℝ)-x) := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  induction k with
  | zero => simp
  | succ k ih =>
    have harg : 0 < ((k+1:ℕ):ℝ)-x := by push_cast; have := Nat.cast_nonneg (α := ℝ) k; linarith
    rw [show ((k+1+1:ℕ):ℝ)-x = (((k+1:ℕ):ℝ)-x)+1 by push_cast; ring,
      Real.Gamma_add_one harg.ne', ih (by omega),
      Finset.prod_Ico_succ_top (by omega : 1 ≤ k+1)]
    ring

lemma scaled_partition_product {m η : ℝ} (hm : m ≠ 0) (k : ℕ) (hk : 0 < k) :
    m * (∏ a ∈ Finset.Ico 1 k, ((a:ℝ)*m-η)) =
      m^k * ∏ a ∈ Finset.Ico 1 k, ((a:ℝ)-η/m) := by
  have he : (∏ a ∈ Finset.Ico 1 k, ((a:ℝ)*m-η)) =
      ∏ a ∈ Finset.Ico 1 k, (m*((a:ℝ)-η/m)) := by
    apply Finset.prod_congr rfl
    intro a ha
    field_simp
  rw [he, Finset.prod_mul_distrib, Finset.prod_const, Nat.card_Ico]
  rw [← mul_assoc, ← pow_succ', show k-1+1 = k by omega]

lemma partition_denominator_pos {η : ℝ} (hη : η < 1) (n : ℕ) :
    0 < ∏ a ∈ Finset.Ico 1 n, ((a:ℝ)-η) := by
  apply Finset.prod_pos
  intro a ha
  have ha1 : (1:ℝ) ≤ a := by exact_mod_cast (Finset.mem_Ico.mp ha).1
  linarith

end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma stableGammaProduct_eq {m : ℝ} (hm : m < 1) (ns : List ℕ) (hns : ∀ n ∈ ns, 0 < n) :
    stableGammaProduct m ns = Real.Gamma (1-m)^ns.length *
      (ns.map (fun n : ℕ => ∏ a ∈ Finset.Ico 1 n, ((a:ℝ)-m))).prod := by
  induction ns with
  | nil => simp [stableGammaProduct]
  | cons n ns ih =>
    have hn := hns n (by simp)
    have htail : ∀ n ∈ ns, 0 < n := fun n hn => hns n (by simp [hn])
    change Real.Gamma ((n:ℝ)-m)*stableGammaProduct m ns = _
    rw [gamma_nat_sub_product hm n hn, ih htail]
    simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
    ring

lemma eppf_algebra (c m g h j d x p r B : ℝ) (k : ℕ)
    (hc : c ≠ 0) (hm : m ≠ 0) (hg : g ≠ 0) (hh : h ≠ 0) (hj : j ≠ 0)
    (hd : d ≠ 0) (hx : x ≠ 0) (hrel : m*B = m^k*r) :
    (((c*m)^k*g^k*p) * (x/(c*g)^k*(1/m)*(h*r)) / (j*d)) / (x*h/j) = B/d*p := by
  rw [mul_pow, mul_pow]
  field_simp
  calc
    m^k*p*r = p*(m^k*r) := by ring
    _ = p*(m*B) := by rw [← hrel]
    _ = p*m*B := by ring

lemma partition_natural_bounds (ns : List ℕ) (hne : ns ≠ []) (hns : ∀ n ∈ ns, 0 < n) :
    0 < ns.length ∧ 0 < ns.sum := by
  exact ⟨List.length_pos_iff.mpr hne, List.sum_pos ns hns hne⟩

lemma stable_partition_gamma_ratio {m c η : ℝ} (hm : 0 < m) (hm1 : m < 1)
    (hc : 0 < c) (hηm : η < m) (ns : List ℕ) (hne : ns ≠ []) (hns : ∀ n ∈ ns, 0 < n) :
    (((c*m)^ns.length*stableGammaProduct m ns) *
      ((c*Real.Gamma (1-m))^(-((ns.length:ℝ)*m-η)/m)*(1/m)*
        Real.Gamma (((ns.length:ℝ)*m-η)/m)) / Real.Gamma ((ns.sum:ℝ)-η)) /
      ((c*Real.Gamma (1-m))^(η/m)*Real.Gamma (1-η/m)/Real.Gamma (1-η)) =
      partitionProduct m η ns := by
  have hb := partition_natural_bounds ns hne hns
  have hη1 : η < 1 := hηm.trans hm1
  have hηdiv : η/m < 1 := (div_lt_one hm).mpr hηm
  have hg : 0 < Real.Gamma (1-m) := Real.Gamma_pos_of_pos (by linarith)
  have hgη : 0 < Real.Gamma (1-η) := Real.Gamma_pos_of_pos (by linarith)
  have hgηm : 0 < Real.Gamma (1-η/m) := Real.Gamma_pos_of_pos (by linarith)
  have hcG : 0 < c*Real.Gamma (1-m) := mul_pos hc hg
  have hpow : (c*Real.Gamma (1-m))^(-((ns.length:ℝ)*m-η)/m) =
      (c*Real.Gamma (1-m))^(η/m) / (c*Real.Gamma (1-m))^ns.length := by
    rw [show -((ns.length:ℝ)*m-η)/m = η/m-(ns.length:ℝ) by field_simp; ring,
      Real.rpow_sub hcG, Real.rpow_natCast]
  rw [hpow, show ((ns.length:ℝ)*m-η)/m = (ns.length:ℝ)-η/m by field_simp,
    stableGammaProduct_eq hm1 ns hns, gamma_nat_sub_product hη1 ns.sum hb.2,
    gamma_nat_sub_product hηdiv ns.length hb.1]
  unfold partitionProduct
  convert eppf_algebra c m (Real.Gamma (1-m)) (Real.Gamma (1-η/m)) (Real.Gamma (1-η))
    (∏ a ∈ Finset.Ico 1 ns.sum, ((a:ℝ)-η)) ((c*Real.Gamma (1-m))^(η/m))
    (ns.map (fun n : ℕ => ∏ a ∈ Finset.Ico 1 n, ((a:ℝ)-m))).prod
    (∏ a ∈ Finset.Ico 1 ns.length, ((a:ℝ)-η/m))
    (∏ a ∈ Finset.Ico 1 ns.length, ((a:ℝ)*m-η)) ns.length
    hc.ne' hm.ne' hg.ne' hgηm.ne' hgη.ne'
    (partition_denominator_pos hη1 ns.sum).ne' (Real.rpow_pos_of_pos hcG _).ne'
    (scaled_partition_product hm.ne' ns.length hb.1) using 1
  ring

 theorem cascadeEPPF : CascadeEPPFStatement := by
  intro m c η hm hm1 hc hη hηm ns hne hns
  have hb := partition_natural_bounds ns hne hns
  have hn1 : (1:ℝ) ≤ ns.sum := by exact_mod_cast hb.2
  have hk1 : (1:ℝ) ≤ ns.length := by exact_mod_cast hb.1
  have ha : 0 < (ns.sum:ℝ)-η := by linarith
  have hk : 0 < (ns.length:ℝ)*m-η := by nlinarith
  rw [stable_partition_numerator_value hm hm1 hc ns hns ha hk,
    stableTotal_moment hm hm1 hc hη hηm]
  have hden : 0 < (c*Real.Gamma (1-m))^(η/m)*Real.Gamma (1-η/m)/Real.Gamma (1-η) := by
    apply div_pos
    · apply mul_pos
      · apply Real.rpow_pos_of_pos
        exact mul_pos hc (Real.Gamma_pos_of_pos (by linarith))
      · apply Real.Gamma_pos_of_pos
        have := (div_lt_one hm).mpr hηm
        linarith
    · apply Real.Gamma_pos_of_pos; linarith
  rw [← ENNReal.ofReal_div_of_pos hden, stable_partition_gamma_ratio hm hm1 hc hηm ns hne hns]

end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

lemma marked_partition_comparison {A : Type} [MeasurableSpace A] [MeasurableEq A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m η : ℝ} (hm : 0 < m) (hm1 : m < 1)
    {X : A → ℝ} (hX : Measurable X) (hi : Integrable (fun a => Real.exp (m*X a)) ν)
    (bs : List (ℕ × Set A)) (hbs : ∀ b ∈ bs, 0 < b.1 ∧ MeasurableSet b.2)
    (ha : 0 < ((bs.map Prod.fst).sum:ℝ)-η) :
    (∫⁻ ω, markedPartitionNumerator m η X bs ω ∂pointCloudLaw ν) =
    (bs.map (fun b => tiltedChildProbability ν m X b.2)).prod *
    (∫⁻ ω, poissonPartitionNumerator m (∫ a, Real.exp (m*X a) ∂ν) η (bs.map Prod.fst) ω
      ∂pointCloudLaw (Measure.dirac ())) := by
  let c := ∫ a, Real.exp (m*X a) ∂ν
  have hc : 0 < c := integral_exp_pos hi
  have hf : ∀ f ∈ bs.map (fun b => expMarkedBlock m X b.1 b.2), Measurable f := by
    intro f hf
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hf
    exact measurable_expMarkedBlock m hX b.1 (hbs b hb).2
  have hf' : ∀ f ∈ (bs.map Prod.fst).map (fun n z => stableJump m c z^n), Measurable f := by
    intro f hf
    obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hf
    exact (measurable_stableJump m c).pow_const n
  have hC : (bs.map (fun b => tiltedChildProbability ν m X b.2)).prod ≠ ∞ := by
    clear hf hf' ha hbs
    induction bs with
    | nil => simp
    | cons b bs ih =>
      simp only [List.map_cons, List.prod_cons]
      exact ENNReal.mul_ne_top (tiltedChildProbability_ne_top ν hi b.2) ih
  have h := weighted_mellin_comparison (pointCloudLaw ν) (pointCloudLaw (Measure.dirac ()))
    (measurable_expMarkedTotal m hX) (aemeasurable_distinct_cloud _ _ hf [])
    (measurable_stableTotal m c) (aemeasurable_distinct_cloud _ _ hf' [])
    (expMarkedTotal_properties ν hm hm1 hX hi).1 (stableTotal_properties hm hm1 hc).1
    ha hC (fun t ht => expMarked_factorial_comparison ν hm hm1 hX hi ht bs hbs)
  simpa only [markedPartitionNumerator, poissonPartitionNumerator, neg_sub] using h

 theorem markedEPPF : MarkedEPPFStatement := by
  intro A _ _ ν _ m η hm hm1 hη hηm X hX hi bs hne hbs
  have hns : ∀ n ∈ bs.map Prod.fst, 0 < n := by
    intro n hn
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hn
    exact (hbs b hb).1
  have hnsne : bs.map Prod.fst ≠ [] := by simpa using hne
  have hsum := (partition_natural_bounds (bs.map Prod.fst) hnsne hns).2
  have ha : 0 < ((bs.map Prod.fst).sum:ℝ)-η := by
    have : (1:ℝ) ≤ (bs.map Prod.fst).sum := by exact_mod_cast hsum
    linarith
  rw [marked_partition_comparison ν hm hm1 hX hi bs hbs ha,
    expMarkedTotal_moment_eq ν hm hm1 hX hi hη hηm, mul_div_assoc,
    cascadeEPPF m _ η hm hm1 (integral_exp_pos hi) hη hηm (bs.map Prod.fst) hnsne hns]
  exact mul_comm _ _
end MicroscopicJamming

 
 

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming

def weightedMarkedBlock {A : Type*} (m : ℝ) (X : A → ℝ) (n : ℕ)
    (w : A → ℝ≥0∞) (z : ℝ × A) : ℝ≥0∞ := expMarkedJump m X z^n*w z.2

def weightedChildMean {A : Type*} [MeasurableSpace A] (ν : Measure A)
    (m : ℝ) (X : A → ℝ) (w : A → ℝ≥0∞) : ℝ≥0∞ :=
  (∫⁻ a, w a * ENNReal.ofReal (Real.exp (m*X a)) ∂ν) /
    ENNReal.ofReal (∫ a, Real.exp (m*X a) ∂ν)

def weightedMarkedPartitionNumerator {A : Type*} [MeasurableSpace A]
    (m η : ℝ) (X : A → ℝ) (bs : List (ℕ × (A → ℝ≥0∞))) (ω : PointCloud A) : ℝ≥0∞ :=
  ENNReal.ofReal ((expMarkedTotal m X ω).toReal^(η-((bs.map Prod.fst).sum:ℝ))) *
    distinctCloudIntegral (bs.map (fun b => weightedMarkedBlock m X b.1 b.2)) (pointCloudMeasure ω) []

lemma measurable_weightedMarkedBlock {A : Type*} [MeasurableSpace A]
    (m : ℝ) {X : A → ℝ} (hX : Measurable X) (n : ℕ)
    {w : A → ℝ≥0∞} (hw : Measurable w) : Measurable (weightedMarkedBlock m X n w) :=
  ((measurable_expMarkedJump m hX).pow_const n).mul (hw.comp measurable_snd)
end MicroscopicJamming

 
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal BigOperators

namespace MicroscopicJamming
lemma selected_exp_weighted_block {A : Type*} [MeasurableSpace A]
    (ν : Measure A) [IsProbabilityMeasure ν] {m t : ℝ} (hm : 0 < m) (ht : 0 < t)
    {X : A → ℝ} (hX : Measurable X) (hi : Integrable (fun a => Real.exp (m*X a)) ν)
    (n : ℕ) (hn : m < (n:ℝ)) {w : A → ℝ≥0∞} (hw : Measurable w) :
    (∫⁻ z, weightedMarkedBlock m X n w z *
      ENNReal.ofReal (expNeg (ENNReal.ofReal t*expMarkedJump m X z))
      ∂(volume.restrict (Set.Ioi 0)).prod ν) =
      weightedChildMean ν m X w *
        ENNReal.ofReal ((∫ a, Real.exp (m*X a) ∂ν)*m*Real.Gamma ((n:ℝ)-m)*t^(m-(n:ℝ))) := by
  let K : ℝ := m*Real.Gamma ((n:ℝ)-m)*t^(m-(n:ℝ))
  have hf : Measurable (fun z : ℝ × A => weightedMarkedBlock m X n w z *
      ENNReal.ofReal (expNeg (ENNReal.ofReal t*expMarkedJump m X z))) :=
    (measurable_weightedMarkedBlock m hX n hw).mul
      (continuous_expNeg.measurable.comp (measurable_const.mul (measurable_expMarkedJump m hX))).ennreal_ofReal
  rw [lintegral_prod_symm _ hf.aemeasurable]
  have he (a : A) : (∫⁻ r in Set.Ioi (0:ℝ), weightedMarkedBlock m X n w (r,a) *
      ENNReal.ofReal (expNeg (ENNReal.ofReal t*expMarkedJump m X (r,a)))) =
      ENNReal.ofReal K * (w a * ENNReal.ofReal (Real.exp (m*X a))) := by
    have hh : Measurable (fun r : ℝ => expMarkedJump m X (r,a)^n *
      ENNReal.ofReal (expNeg (ENNReal.ofReal t*expMarkedJump m X (r,a)))) := by
      have hx : Measurable (fun r : ℝ => expMarkedJump m X (r,a)) :=
        (measurable_expMarkedJump m hX).comp (measurable_id.prodMk measurable_const)
      exact (hx.pow_const n).mul (continuous_expNeg.measurable.comp (measurable_const.mul hx)).ennreal_ofReal
    simp only [weightedMarkedBlock]
    simp_rw [show ∀ r : ℝ, expMarkedJump m X (r,a)^n * w a *
      ENNReal.ofReal (expNeg (ENNReal.ofReal t*expMarkedJump m X (r,a))) =
      (expMarkedJump m X (r,a)^n *
      ENNReal.ofReal (expNeg (ENNReal.ofReal t*expMarkedJump m X (r,a)))) * w a by
        intro r; ac_rfl]
    rw [lintegral_mul_const _ hh]
    rw [show (∫⁻ r in Set.Ioi (0:ℝ), expMarkedJump m X (r,a)^n *
        ENNReal.ofReal (expNeg (ENNReal.ofReal t*expMarkedJump m X (r,a)))) =
        ENNReal.ofReal K * ENNReal.ofReal (Real.exp (m*X a)) from by simpa only [expMarkedJump, K] using (selected_exp_jump (x := X a) hm ht n hn)]
    ac_rfl
  simp_rw [he]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hc := integral_exp_pos hi
  have hmul : ENNReal.ofReal ((∫ a, Real.exp (m*X a) ∂ν)*m*Real.Gamma ((n:ℝ)-m)*t^(m-(n:ℝ))) =
      ENNReal.ofReal (∫ a, Real.exp (m*X a) ∂ν)*ENNReal.ofReal K := by
    rw [← ENNReal.ofReal_mul hc.le]; congr 1; dsimp [K]; ring
  rw [hmul, weightedChildMean, ← mul_assoc,
    ENNReal.div_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hc) ENNReal.ofReal_ne_top]
  exact mul_comm _ _
end MicroscopicJamming

end

end OAI
