import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkMarkedTangentLimit
import OAI.Probability.Perceptron.Variational.MarkedTangentCanonical

namespace OAI

noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology BoundedContinuousFunction ContDiff
namespace SphericalPerceptronFreeEnergy

lemma marked_overlap_geometry (K : ℝ) (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (he : ∀ e : Equiv.Perm ℕ,MeasurePreserving (compactRelabel (K:=BulkPairRange K) e) (μ : Measure _) (μ : Measure _))
    (hg : ∀ᵐ Q ∂(bulkJointLaw (compactMapLaw Prod.fst continuous_fst μ) : Measure (CompactArray CompactJointOverlap)),CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw (compactMapLaw Prod.fst continuous_fst μ) : Measure (CompactArray CompactJointOverlap)),0≤(Q 0 1).1.val) :
    (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,(Q i j).1=(Q j i).1) ∧
    (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j k,min (Q i j).1.val (Q i k).1.val≤(Q j k).1.val) ∧
    (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,0≤(Q i j).1.val) := by
  have h1 := ae_of_ae_map (compactMapArray_continuous bulkJointEmbedding_continuous).measurable.aemeasurable hg
  have h2 := ae_of_ae_map (compactMapArray_continuous (show Continuous (Prod.fst : BulkPairRange K → CompactOverlap) from continuous_fst)).measurable.aemeasurable h1
  have h3 := ae_of_ae_map (compactMapArray_continuous bulkJointEmbedding_continuous).measurable.aemeasurable hn
  have h4 := ae_of_ae_map (compactMapArray_continuous (show Continuous (Prod.fst : BulkPairRange K → CompactOverlap) from continuous_fst)).measurable.aemeasurable h3
  have hsy : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,(Q i j).1=(Q j i).1 :=
    h2.mono fun Q hQ i j=>Subtype.ext (hQ.1 i j)
  refine ⟨hsy,h2.mono (fun Q hQ=>hQ.2.2),?_⟩
  have h10 : ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),0≤(Q 1 0).1.val := by
    filter_upwards [hsy,h4] with Q hQ hN
    change 0≤(Q 0 1).1.val at hN
    simpa only [hQ 1 0] using hN
  have ha := compact_exchangeable_offdiag_ae μ he (fun p=>0≤p.1.val) h10
  filter_upwards [ha,h2] with Q hQ hG
  intro i j
  by_cases hij : i=j
  · subst j
    have hd : (Q i i).1.val=1 := hG.2.1 i
    rw [hd]; norm_num
  · exact hQ i j hij

theorem bulk_marked_self_consistency (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ)
    (hv : ∀ n p,1≤v n p) {C : ℝ} (hC : 0≤C) (hvC : ∀ n p,|v n (p+1)|≤C)
    (hdO : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n) g.f p (v n)) atTop (𝓝 0))
    (hdF : ∀ p,Tendsto (fun n=>bulkDeviationAt n (M n+2) g.f p (v n)) atTop (𝓝 0))
    (s : ℕ→ℕ) (hs : StrictMono s) (α : ℝ) (hα : 0≤α)
    (hd : Tendsto (fun n=>((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (ho : Tendsto (fun n=>bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (K : ℝ) (hK0 : 0≤K) (hK : ∀ n,((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖g.d1‖^2≤K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hf : Tendsto (fun n=>bulkMarkedArrayLaw (s n) (M (s n)+2) g (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    ∃ a : ℝ→ℝ,Monotone a ∧ (∀ r,0≤a r ∧ a r≤α*‖g.d1‖^2) ∧
      (∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,i≠j→(Q i j).2.val=a (Q i j).1.val) ∧
      (∀ᵐ x : Time ∂((markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)),
        a x=∫ y in 0..(x:ℝ),(realTail ((markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)) y)⁻¹^2) ∧
      ∀ᵐ x : Time ∂((markedTimeLaw K μ : Measure (CompactArray Time)).map (fun Q=>Q 0 1)),
        (x:ℝ)≤(α*‖g.d1‖^2)/(1+α*‖g.d1‖^2) := by
  have hOm := bulk_limit_geometry M g.f v (Eventually.of_forall hv) hdO hs ho
  obtain ⟨a,ham,hab,_,hag⟩ := bulkMarkedArray_identification M g v s hs.tendsto_atTop α hα hd ν ho
    hOm.2.2 hOm.1 hOm.2.1 K hK0 hK μ hf
  have hf' := bulkMarkedArray_limit_overlap (fun n=>M n+2) g v s K hK hf
  have hFm := bulk_limit_geometry (fun n=>M n+2) g.f v (Eventually.of_forall hv) hdF hs hf'
  have he (e : Equiv.Perm ℕ) := compact_exchangeability_limit hf e
    (fun n=>bulkMarkedArray_exchangeable (s n) (M (s n)+2) g (v (s n)) K (hK n) e)
  have hGm := marked_overlap_geometry K μ he hFm.1 hFm.2.1
  have hsc := marked_time_self_consistency K μ he
    (bulk_limit_gg (fun n=>M n+2) g.f v (Eventually.of_forall hv) hdF hs hf')
    hGm.1 hGm.2.1 hGm.2.2 a ham.measurable (mul_nonneg hα (sq_nonneg _)) hab hag
    (fun G hG=>bulk_marked_tangent_limit (fun n=>M n+2) g v hC hvC K hs hK μ hf G hG)
  exact ⟨a,ham,hab,hag,hsc.1,hsc.2⟩

end SphericalPerceptronFreeEnergy
end

end OAI
