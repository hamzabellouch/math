import Mathlib
import OAI.Probability.Perceptron.Cavity.CavityRoundedLower

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BigOperators NNReal BoundedContinuousFunction
namespace SphericalPerceptronFreeEnergy

structure BulkCavityData (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (α K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hg : HasCompactSupport (g.d1 : ℝ→ℝ)) where
  a : ℝ
  c : ℝ
  a_nonneg : 0≤a
  a_le_K : a≤K
  a_le : a≤α*‖g.d1‖^2
  c_bound : |c|≤α*‖g.dilationMark hg‖
  a_L2 : Tendsto (fun j=>bulkReplicaMean (s j) (M (s j)+2) g.f (v (s j)) 1
    (fun b x=>(bulkB (s j+1) (M (s j)+2) g b.1 (x 0) (x 0)-a)^2)) atTop (𝓝 0)
  c_L2 : Tendsto (fun j=>bulkReplicaMean (s j) (M (s j)+2) g.f (v (s j)) 1
    (fun b x=>(bulkC (s j+1) (M (s j)+2) g b.1 (x 0)-c)^2)) atTop (𝓝 0)
  support : ∀ᵐ r : Time ∂markedTimePair K μ,(r:ℝ)≤(α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)
  field_bound : ∀ᵐ r : Time ∂markedTimePair K μ,
    cappedA (markedTimePair K μ) ((α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)) r≤a
  radial : (c+a)/2=cavityProfileMoment (markedTimePair K μ) ((α*‖g.d1‖^2)/(1+α*‖g.d1‖^2))
  capped : ∀ n d (Λ : ℝ) (hΛ : 1≤Λ),
    Tendsto (fun j=>cavityBulkLog n d (s j) (M (s j)+2) g (v (s j)) Λ hΛ-
      roundedCavityLog n d g.f Λ hΛ (markedTimePair K μ)
        ((α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)) a_nonneg a_le_K j) atTop (𝓝 0)

theorem bulk_cavity_data (M : ℕ→ℕ) (g : Jet3) (hg : HasCompactSupport (g.d1 : ℝ→ℝ))
    (v : ℕ→ℕ→ℝ) (hv : ∀ n p,1≤v n p) {C : ℝ} (hC : 0≤C) (hvC : ∀ n p,|v n (p+1)|≤C)
    (hdO : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n) g.f p (v n)) atTop (𝓝 0))
    (hdF : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n+2) g.f p (v n)) atTop (𝓝 0))
    (s : ℕ→ℕ) (hs : StrictMono s) (α : ℝ) (hα : 0≤α)
    (hd : Tendsto (fun n=>((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (ho : Tendsto (fun n=>bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (K : ℝ) (hK0 : 0≤K) (hK : ∀ n,((M n+2:ℕ):ℝ)/(n+1:ℕ)*‖g.d1‖^2≤K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hf : Tendsto (fun n=>bulkMarkedArrayLaw (s n) (M (s n)+2) g (v (s n)) K (hK (s n))) atTop (𝓝 μ)) :
    Nonempty (BulkCavityData M g v s α K μ hg) := by
  have hOm:=bulk_limit_geometry M g.f v (Eventually.of_forall hv) hdO hs ho
  obtain ⟨⟨a,ha,hLa⟩,⟨c,hc,hLc⟩⟩:=bulk_diagonal_C_concentration M g hg v s hs.tendsto_atTop α hd ho
    hOm.2.2 hOm.1 hOm.2.1
  rw [abs_of_nonneg hα] at ha hc
  have hD2:=bulkMarkedArray_limit_diagonal_const (fun n=>M n+2) g v s K (fun j=>hK (s j)) μ hf a hLa
  have hmg:=bulkMarkedArray_limit_mark_geometry (fun n=>M n+2) g v s K (fun j=>hK (s j)) hf
  obtain ⟨Q,hQ,hpos⟩:=(hD2.and hmg.1).exists
  have ha0 : 0≤a:=by simpa only [hQ 0] using hpos 0
  have haK : a≤K:=by simpa only [hQ 0] using (Q 0 0).2.prop.2
  have haA : a≤α*‖g.d1‖^2:=(le_abs_self a).trans ha
  have hBd : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,(Q i j).2.val≤a := by
    filter_upwards [hD2,hmg.2] with Q hD hG
    intro i j
    have h:=hG i j
    rw [hD i,hD j] at h
    linarith
  obtain ⟨f,_hfm,hfb,hfg,hsc,hbound⟩:=bulk_marked_self_consistency M g v hv hC hvC hdO hdF s hs α hα hd ν ho
    K hK0 (fun j=>hK (s j)) μ hf
  let η:=markedTimePair K μ
  let B:=(α*‖g.d1‖^2)/(1+α*‖g.d1‖^2)
  have hA0 : 0≤α*‖g.d1‖^2:=mul_nonneg hα (sq_nonneg _)
  have hB : B<1:=(div_lt_one (by linarith : 0<1+α*‖g.d1‖^2)).mpr (by linarith)
  have he e:=compact_exchangeability_limit hf e
    (fun j=>bulkMarkedArray_exchangeable (s j) (M (s j)+2) g (v (s j)) K (hK (s j)) e)
  have hp:=bulkMarkedArray_limit_overlap (fun n=>M n+2) g v s K (fun j=>hK (s j)) hf
  have hgF:=bulk_limit_geometry (fun n=>M n+2) g.f v (Eventually.of_forall hv) hdF hs hp
  have hgeom:=marked_overlap_geometry K μ he hgF.1 hgF.2.1
  have hm:=marked_cappedA_identification μ hB (hgeom.2.2.mono fun _array hQ=>hQ 0 1)
    (hBd.mono fun _array hQ=>hQ 0 1) f (hfg.mono fun _array hQ=>hQ 0 1 (by omega)) hsc hbound
  have hrad : (c+a)/2=cavityProfileMoment η B := by
    have ht:=ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hf
      (by fun_prop : Continuous (fun Q : CompactArray (BulkPairRange K)=>Q 1 0))
    simp_rw [bulkMarkedArray_pair] at ht
    have hr:=bulk_radial_limit_relation s (fun j=>M (s j)+2) g hg (fun j=>v (s j)) c a hLc hLa K
      (fun j=>hK (s j)) _ ht
    rw [ProbabilityMeasure.toMeasure_map,integral_map (by fun_prop : Measurable
      (fun Q : CompactArray (BulkPairRange K)=>Q 1 0)).aemeasurable (by fun_prop)] at hr
    have hs:=integral_map (he (Equiv.swap 0 1)).measurable.aemeasurable
      (show AEStronglyMeasurable (fun Q : CompactArray (BulkPairRange K)=>(Q 0 1).1.val*(Q 0 1).2.val)
        ((μ : Measure _).map (compactRelabel (Equiv.swap 0 1))) from by fun_prop)
    rw [(he (Equiv.swap 0 1)).map_eq] at hs
    simp only [compactRelabel,Equiv.swap_apply_left,Equiv.swap_apply_right] at hs
    rw [hm.2,hr,hs]
  have hD1:=ae_of_ae_map (compactMapArray_continuous (show Continuous
    (Prod.fst : BulkPairRange K → CompactOverlap) from continuous_fst)).measurable.aemeasurable
    (bulkGibbsArray_limit_diagonal g.f (fun n=>M n+2) v s hp)
  have hgraph:=marked_graph_law μ hB ha0 haK he hgeom.2.2 hD1 hD2 hBd f
    (fun r=>(hfb r).1) hfg hsc hbound
  obtain ⟨hGG,hGe,hEx⟩:=bulk_marked_time_inputs (fun n=>M n+2) g v (Eventually.of_forall hv) hdF s hs K
    (fun j=>hK (s j)) μ hf
  let q:=boundedQuantile η
  let hq:=boundedQuantile_monotone η
  let F:=unitQuantileField q hq
  have hpair : (markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)=timeLaw.map q :=
    (boundedQuantile_law η).symm
  have hrpc:=cavityLabelMarkedLaw_tendsto_graph (markedTimeLaw K μ) q hq hpair hGG hGe hEx
    (continuousCavityProfile η B ha0 haK) (continuousCavityProfile_continuous η hB ha0 haK)
    (cavityTrueDiagonal ha0 haK)
  rw [hgraph] at hrpc
  refine ⟨⟨a,c,ha0,haK,haA,hc,hLa,hLc,hbound,hm.1,hrad,?_⟩⟩
  intro n d Λ hΛ
  have hprof j:=roundedCavityPair_conditions n d η hB ha0 haK j
  exact cavity_joint_array_recursion_limit n d (fun m=>M m+2) g v Λ hΛ K hK s hf
    (fun j=>(strictRoundModel F j).depth) (roundedCavityPair η B ha0 haK)
    (fun _=>cavityTrueDiagonal ha0 haK) (fun j=>stepCumulative (strictRoundModel F j).weight)
    (fun j=>(hprof j).1) (fun j=>(hprof j).2.1) (fun j=>(hprof j).2.2)
    (fun j=>stepCumulative_strictMono _ (strictRoundModel F j).weight_pos)
    (fun j=>stepCumulative_pos _ (strictRoundModel F j).weight_pos)
    (fun j=>stepCumulative_lt_one _ (strictRoundModel F j).weight_pos (strictRoundModel F j).weight_sum) hrpc
end SphericalPerceptronFreeEnergy

end

end OAI
