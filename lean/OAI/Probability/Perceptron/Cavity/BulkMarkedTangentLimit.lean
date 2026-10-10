import Mathlib
import OAI.Probability.Perceptron.Cavity.BulkMarkedArray

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology BoundedContinuousFunction ContDiff

lemma bulkScale_sq_div (n : ℕ) : bulkScale (n+1)^2/(n+1:ℕ)=((n+1:ℕ):ℝ)^(-(1:ℝ)/4) := by
  have hn : (0:ℝ)<(n+1:ℕ) := by positivity
  unfold bulkScale
  rw [←Real.rpow_mul_natCast hn.le]
  calc
    _ = ((n+1:ℕ):ℝ)^((3:ℝ)/8*(2:ℕ))/((n+1:ℕ):ℝ)^(1:ℝ) := by rw [Real.rpow_one]
    _ = _ := by rw [←Real.rpow_sub hn]; norm_num

lemma bulk_tangent_error_tendsto (A D C : ℝ) :
    Tendsto (fun n : ℕ => (A+D+8*A*C^2*bulkScale (n+1)^2)/(n+1:ℕ)) atTop (𝓝 0) := by
  have hN : Tendsto (fun n : ℕ => ((n+1:ℕ):ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hi := tendsto_inv_atTop_zero.comp hN
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0:ℝ)<1/4)).comp hN
  have he (n : ℕ) : (A+D+8*A*C^2*bulkScale (n+1)^2)/(n+1:ℕ)=
      (A+D)*((n+1:ℕ):ℝ)⁻¹+8*A*C^2*((n+1:ℕ):ℝ)^(-(1:ℝ)/4) := by
    rw [add_div,mul_div_assoc,bulkScale_sq_div,div_eq_mul_inv]
  simp_rw [he]
  convert (hi.const_mul (A+D)).add (hp.const_mul (8*A*C^2)) using 1 <;>
    simp only [mul_zero,add_zero,Function.comp_def,neg_div]

lemma marked_tangent_continuous (K : ℝ) (G : ℝ→ᵇℝ) :
    Continuous (fun μ : ProbabilityMeasure (CompactArray (BulkPairRange K)) =>
      (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(μ : Measure _))-
        (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(μ : Measure _))+
        2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(μ : Measure _))) := by
  have hh (r : ℕ) (F : CompactBlock (BulkPairRange K) r→ᵇℝ) :=
    ProbabilityMeasure.continuous_integral_boundedContinuousFunction
      (F.compContinuous ⟨compactBlock r,compactBlock_continuous r⟩)
  exact ((hh 2 (markedTangentR K G)).sub (hh 2 (markedTangentPair K G))).add
    (continuous_const.mul (hh 3 (markedTangentTriple K G)))

lemma bulk_marked_tangent_limit (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ)
    {C : ℝ} (hC : 0≤C) (hv : ∀ n j,|v n (j+1)|≤C)
    (K : ℝ) {s : ℕ→ℕ} (hs : StrictMono s)
    (hK : ∀ n,M (s n)/(s n+1:ℕ)*‖f.d1‖^2≤K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hlim : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n)) atTop (𝓝 μ))
    (G : ℝ→ᵇℝ) (hG : ContDiff ℝ 1 (G : ℝ→ℝ)) :
    (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(μ : Measure _))-
      (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(μ : Measure _))+
      2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(μ : Measure _))=0 := by
  have hc : Continuous (fun r : CompactOverlap=>deriv (G : ℝ→ℝ) r.val*(1-r.val^2)) :=
    ((hG.continuous_deriv (by norm_num)).comp continuous_subtype_val).mul
      (continuous_const.sub (continuous_subtype_val.pow 2))
  obtain ⟨D,hD,hbD⟩ := continuous_real_compact_bound hc
  have hzero : Tendsto (fun n =>
      (∫ Q,markedTangentR K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n) : Measure _))-
      (∫ Q,markedTangentPair K G (compactBlock 2 Q) ∂(bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n) : Measure _))+
      2*(∫ Q,markedTangentTriple K G (compactBlock 3 Q) ∂(bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n) : Measure _))) atTop (𝓝 0) := by
    apply squeeze_zero_norm (a:=fun n => (‖G‖+D+8*‖G‖*C^2*bulkScale (s n+1)^2)/(s n+1:ℕ))
    · intro n
      simpa only [Real.norm_eq_abs] using bulk_marked_tangent_bound (s n) (M (s n)) f (v (s n)) G hG hC (hv (s n)) K (hK n) hD hbD
    · exact (bulk_tangent_error_tendsto ‖G‖ D C).comp hs.tendsto_atTop
  exact tendsto_nhds_unique ((marked_tangent_continuous K G).continuousAt.tendsto.comp hlim) hzero

lemma exists_nat_perm_pair (i j : ℕ) (hij : i≠j) :
    ∃ e : Equiv.Perm ℕ,e 1=i ∧ e 0=j := by
  classical
  let u := Equiv.swap 1 i
  have hu : u 0≠i := by
    intro h
    have he : u 0=u 1 := by simpa [u] using h
    have := u.injective he
    omega
  refine ⟨u.trans (Equiv.swap (u 0) j),?_,?_⟩
  · change Equiv.swap (u 0) j (u 1)=i
    simp only [u,Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne hu.symm hij
  · change Equiv.swap (u 0) j (u 0)=j
    exact Equiv.swap_apply_left _ _

lemma compact_exchangeable_offdiag_ae {K : Type*} [TopologicalSpace K]
    [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]
    (μ : ProbabilityMeasure (CompactArray K))
    (he : ∀ e : Equiv.Perm ℕ,MeasurePreserving (compactRelabel (K:=K) e) (μ : Measure _) (μ : Measure _))
    (P : K→Prop) (hP : ∀ᵐ Q ∂(μ : Measure (CompactArray K)),P (Q 1 0)) :
    ∀ᵐ Q ∂(μ : Measure (CompactArray K)),∀ i j,i≠j→P (Q i j) := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i=j
  · exact ae_of_all _ fun Q h => (h hij).elim
  · obtain ⟨e,he1,he0⟩ := exists_nat_perm_pair i j hij
    have h := (he e).quasiMeasurePreserving.ae hP
    simpa only [compactRelabel,he1,he0] using h.mono (fun Q h _ => h)

lemma bulkMarkedArray_limit_overlap (M : ℕ→ℕ) (f : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (K : ℝ) (hK : ∀ n,(M (s n):ℝ)/(s n+1:ℕ)*‖f.d1‖^2≤K)
    {μ : ProbabilityMeasure (CompactArray (BulkPairRange K))}
    (hlim : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) f.f (v (s n))) atTop
      (𝓝 (compactMapLaw Prod.fst continuous_fst μ)) := by
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hlim
    (compactMapArray_continuous (show Continuous (Prod.fst : BulkPairRange K → CompactOverlap) from continuous_fst))
  change Tendsto (fun n => compactMapLaw Prod.fst continuous_fst (bulkMarkedArrayLaw (s n) (M (s n)) f (v (s n)) K (hK n))) atTop (𝓝 (compactMapLaw Prod.fst continuous_fst μ)) at ht
  simpa only [bulkMarkedArray_overlap] using ht

theorem bulkMarkedArray_identification (M : ℕ→ℕ) (g : Jet3) (v : ℕ→ℕ→ℝ) (s : ℕ→ℕ)
    (hs : Tendsto s atTop atTop) (α : ℝ) (hα : 0≤α)
    (hd : Tendsto (fun n => ((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)) atTop (𝓝 α))
    (ν : ProbabilityMeasure (CompactArray CompactOverlap))
    (hlim : Tendsto (fun n => bulkGibbsArrayLaw (s n) (M (s n)) g.f (v (s n))) atTop (𝓝 ν))
    (hGG : ∀ (r : ℕ) (i : Fin r) (G : CompactBlock CompactJointOverlap r →ᵇ ℝ)
      (a : CompactJointOverlap →ᵇ ℝ), compactGGDefect (bulkJointLaw ν) r i G a=0)
    (hgeo : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), CompactSpinGeometry Q)
    (hn : ∀ᵐ Q ∂(bulkJointLaw ν : Measure (CompactArray CompactJointOverlap)), 0≤(Q 0 1).1.val)
    (K : ℝ) (hK0 : 0≤K) (hK : ∀ n,((M (s n)+2:ℕ):ℝ)/(s n+1:ℕ)*‖g.d1‖^2≤K)
    (μ : ProbabilityMeasure (CompactArray (BulkPairRange K)))
    (hmarked : Tendsto (fun n => bulkMarkedArrayLaw (s n) (M (s n)+2) g (v (s n)) K (hK n)) atTop (𝓝 μ)) :
    ∃ a : ℝ→ℝ,Monotone a ∧ (∀ r,0≤a r ∧ a r≤α*‖g.d1‖^2) ∧
      (μ : Measure (CompactArray (BulkPairRange K))).map (fun Q => (Q 1 0).1)=
        (compactPairMarginal ν : Measure CompactOverlap) ∧
      ∀ᵐ Q ∂(μ : Measure (CompactArray (BulkPairRange K))),∀ i j,i≠j→(Q i j).2.val=a (Q i j).1.val := by
  have hc : Continuous (fun Q : CompactArray (BulkPairRange K)=>Q 1 0) := by fun_prop
  let ρ := μ.map (fun Q => Q 1 0)
  have ht := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hmarked hc
  change Tendsto (fun n => (bulkMarkedArrayLaw (s n) (M (s n)+2) g (v (s n)) K (hK n)).map (fun Q => Q 1 0)) atTop (𝓝 ρ) at ht
  simp_rw [bulkMarkedArray_pair] at ht
  obtain ⟨a,ham,hab,hmarg,hgraph⟩ := bulkPairLaw_identification M g v s hs α hα hd ν hlim hGG hgeo hn g.d1 K hK0 hK ρ ht
  refine ⟨a,ham,hab,?_,?_⟩
  · change (Measure.map Prod.fst (Measure.map (fun Q : CompactArray (BulkPairRange K)=>Q 1 0) (μ : Measure _)))=_ at hmarg
    rwa [Measure.map_map measurable_fst hc.measurable] at hmarg
  · apply compact_exchangeable_offdiag_ae μ
      (fun e => compact_exchangeability_limit hmarked e (fun n => bulkMarkedArray_exchangeable (s n) (M (s n)+2) g (v (s n)) K (hK n) e))
      (fun p => p.2.val=a p.1.val)
    exact ae_of_ae_map hc.measurable.aemeasurable hgraph

end SphericalPerceptronFreeEnergy
end

end OAI
