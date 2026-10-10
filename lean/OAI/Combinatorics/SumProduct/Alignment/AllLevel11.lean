import Mathlib
import OAI.Combinatorics.SumProduct.Alignment.AllLevel07
import OAI.Combinatorics.SumProduct.Alignment.AllLevel10
import OAI.Geometry.NilpotentCharts.Main

namespace OAI

open scoped BigOperators
section
section
noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
open Filter
namespace CompactUniformComposition

lemma compose {X E Y : Type*} [TopologicalSpace X] [PseudoMetricSpace E]
    [PseudoMetricSpace Y] (A : Set X) (hA : IsCompact A)
    (f : X → E) (hf : Continuous f) (u : ℕ → X → E)
    (hu : TendstoUniformlyOn u f atTop A) (g : E → Y) (hg : Continuous g) :
    TendstoUniformlyOn (fun N t=>g (u N t)) (fun t=>g (f t)) atTop A := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hr : {p : Y×Y | dist p.1 p.2 < ε}∈uniformity Y:=
    Metric.mem_uniformity_dist.mpr ⟨ε,hε,fun {_ _} h=>h⟩
  have huni := (hA.image hf).uniformContinuousAt_of_continuousAt g
    (fun _ _=>hg.continuousAt) hr
  obtain ⟨δ,hδ,hδs⟩:=Metric.mem_uniformity_dist.mp huni
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hu δ hδ] with N hN
  intro t ht
  exact hδs (hN t ht) ⟨t,ht,rfl⟩

lemma floor_normalized_close {l : ℝ} (hl : 0 < l) {k : ℕ} (hk : k < ⌊l⌋₊) :
    (k:ℝ)/l∈Set.Icc (0:ℝ) 1 ∧ (k:ℝ)/(⌊l⌋₊:ℝ)∈Set.Icc (0:ℝ) 1 ∧
      dist ((k:ℝ)/l) ((k:ℝ)/(⌊l⌋₊:ℝ)) ≤ 1/l := by
  have hM : 0 < (⌊l⌋₊:ℝ):=by exact_mod_cast (Nat.zero_lt_of_lt hk)
  have hkR : (k:ℝ) < (⌊l⌋₊:ℝ):=by exact_mod_cast hk
  have hf := Nat.floor_le hl.le
  have hf' := Nat.lt_floor_add_one l
  have hu0 : 0 ≤ (k:ℝ)/(⌊l⌋₊:ℝ):=by positivity
  have hu1 : (k:ℝ)/(⌊l⌋₊:ℝ) ≤ 1:=(div_le_one hM).mpr hkR.le
  have hv0 : 0 ≤ (k:ℝ)/l:=by positivity
  have hv1 : (k:ℝ)/l ≤ 1:=(div_le_one hl).mpr (hkR.le.trans hf)
  refine ⟨⟨hv0,hv1⟩,⟨hu0,hu1⟩,?_⟩
  have hvu : (k:ℝ)/l ≤ (k:ℝ)/(⌊l⌋₊:ℝ):=
    div_le_div_of_nonneg_left (by positivity) hM hf
  rw [Real.dist_eq,abs_of_nonpos (sub_nonpos.mpr hvu)]
  have he : ((k:ℝ)/(⌊l⌋₊:ℝ)-(k:ℝ)/l)*l=
      ((k:ℝ)/(⌊l⌋₊:ℝ))*(l-(⌊l⌋₊:ℝ)):=by field_simp
  apply (le_div_iff₀ hl).mpr
  have hdiff0 : 0 ≤ l-(⌊l⌋₊:ℝ):=sub_nonneg.mpr hf
  have hh:=mul_le_mul_of_nonneg_right hu1 hdiff0
  rw [neg_sub]
  rw [he]
  nlinarith
end CompactUniformComposition

namespace AllLevelFactorization.Factorization
open RationalLattice CubeFaces
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable (F : Factorization c Γ s K P L)
variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

lemma smooth_composed_uniform {Y : Type*} [PseudoMetricSpace Y]
    (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    (A : Set ℝ) (hA : IsCompact A) (g : G → Y) (hg : Continuous g) :
    TendstoUniformlyOn (fun N t=>g (F.smoothPart N (L (F.state.subseq N)*t)))
      (fun t=>g (F.smoothLimit t)) atTop A := by
  have hu : TendstoUniformlyOn
      (fun N t=>c.coord (F.smoothPart N (L (F.state.subseq N)*t)))
      (fun t=>c.coord (F.smoothLimit t)) atTop A := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    simpa only [dist_comm] using F.smooth_coord_uniform hL ht A hA ε hε
  have hh:=CompactUniformComposition.compose A hA
    (fun t=>c.coord (F.smoothLimit t)) (c.coord.continuous.comp F.smoothLimit_continuous)
    _ hu (g∘c.coord.symm) (hg.comp c.coord.symm.continuous)
  simpa only [Function.comp_def,Homeomorph.symm_apply_apply] using hh

 

lemma smooth_floor_tests (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    (g : G → C(X,ℂ)) (hg : Continuous g) :
    ∀ ε : ℝ,0 < ε → ∀ᶠ N : ℕ in atTop,∀ k : Fin ⌊L (F.state.subseq N)⌋₊,
      dist (g (F.smoothPart N (k.val:ℝ)))
        (g (F.smoothLimit ((k.val:ℝ)/(⌊L (F.state.subseq N)⌋₊:ℝ)))) < ε := by
  intro ε hε
  have hlc : Continuous (fun t=>g (F.smoothLimit t)):=hg.comp F.smoothLimit_continuous
  have hc : UniformContinuousOn (fun t=>g (F.smoothLimit t)) (Set.Icc (0:ℝ) 1):=
    isCompact_Icc.uniformContinuousOn_of_continuous hlc.continuousOn
  obtain ⟨δ,hδ,hδs⟩:=Metric.uniformContinuousOn_iff.mp hc (ε/2) (by positivity)
  have huv:=F.smooth_composed_uniform hL ht (Set.Icc (0:ℝ) 1) isCompact_Icc g hg
  have hbig:=(ht.comp F.state.strictmono.tendsto_atTop).eventually
    (eventually_gt_atTop (1/δ))
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp huv (ε/2) (by positivity),hbig] with N hN hb
  intro k
  have hpoint:=CompactUniformComposition.floor_normalized_close (hL _) k.isLt
  have htδ : dist ((k.val:ℝ)/L (F.state.subseq N))
      ((k.val:ℝ)/(⌊L (F.state.subseq N)⌋₊:ℝ)) < δ := by
    apply hpoint.2.2.trans_lt
    apply (div_lt_iff₀ (hL _)).mpr
    have hh:=(div_lt_iff₀ hδ).mp hb
    simpa only [Function.comp_apply,mul_comm] using hh
  have he : L (F.state.subseq N)*((k.val:ℝ)/L (F.state.subseq N))=k.val:=by
    field_simp [ne_of_gt (hL (F.state.subseq N))]
  have hfirst:=hN ((k.val:ℝ)/L (F.state.subseq N)) hpoint.1
  rw [he,dist_comm] at hfirst
  have hsecond:=hδs _ hpoint.1 _ hpoint.2.1 htδ
  exact (dist_triangle _ (g (F.smoothLimit ((k.val:ℝ)/L (F.state.subseq N)))) _).trans_lt
    (by linarith only [hfirst,hsecond])

end AllLevelFactorization.Factorization
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology
open Filter MeasureTheory
namespace AllLevelFactorization.Factorization
open RationalLattice CubeFaces
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {n s : ℕ} {c : RealCoordinates G n} {Γ : Subgroup G}
variable {K : Filtration G} {P : ℕ → ℤ → G} {L : ℕ → ℝ}
variable (F : Factorization c Γ s K P L)

def natResidue (k : ℕ) : Fin F.period:=⟨k%F.period,Nat.mod_lt _ F.period_pos⟩
def pointStructured (N k : ℕ) : G⧸Γ :=
  QuotientGroup.mk (F.state.domain.embed (F.structuredPart N (k:ℤ))*F.residue (F.natResidue k))

def leftTest (f : C(G⧸Γ,ℂ)) (a : G) : C(G⧸Γ,ℂ) :=
  ⟨fun x=>f (a•x),f.continuous.comp ((continuous_const : Continuous (fun _ : G⧸Γ=>a)).smul continuous_id)⟩

lemma leftTest_continuous (f : C(G⧸Γ,ℂ)) : Continuous (leftTest f) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact f.continuous.comp (show Continuous (fun p : G×(G⧸Γ)=>p.1•p.2) from
    continuous_fst.smul continuous_snd)

def limitTest (f : C(G⧸Γ,ℂ)) (β : ℝ) : C(G⧸Γ,ℂ) :=leftTest f (F.smoothLimit β)

lemma limitTest_continuous (f : C(G⧸Γ,ℂ)) : Continuous (F.limitTest f) :=
  (leftTest_continuous f).comp F.smoothLimit_continuous

lemma point_realization (N k : ℕ) :
    (QuotientGroup.mk (P (F.state.subseq N) (k:ℤ)) : G⧸Γ)=
      F.smoothPart N (k:ℝ) • F.pointStructured N k := by
  have hr : (k:ℤ)%(F.period:ℤ)=((F.natResidue k).val:ℤ):=by
    simp [natResidue,Int.natCast_emod]
  rw [F.realization_of_residue N k (F.natResidue k) hr]
  change QuotientGroup.mk (F.smoothPart N (k:ℝ)*F.state.domain.embed
    (F.structuredPart N (k:ℤ))*F.residue (F.natResidue k))=
    QuotientGroup.mk (F.smoothPart N (k:ℝ)*(F.state.domain.embed
      (F.structuredPart N (k:ℤ))*F.residue (F.natResidue k)))
  rw [mul_assoc]

variable (C : (r : Fin F.period) → F.ResidueCover r)
variable [∀ r,MeasurableSpace ((C r).CubeSpace (ι:=Empty))]
variable [∀ r,BorelSpace ((C r).CubeSpace (ι:=Empty))]
variable [MeasurableSpace (G⧸Γ)] [BorelSpace (G⧸Γ)] [CompactSpace (G⧸Γ)]

omit [CompactSpace (G ⧸ Γ)] in
lemma pointStructured_local (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (r : Fin F.period) (f : C(G⧸Γ,ℂ)) :
    Tendsto (fun N=>𝔼 k∈GlobalPointLaw.cell ⌊L (F.state.subseq N)⌋₊ F.period r.val a b,
      f (F.pointStructured N k.val)) atTop (𝓝 (∫ y,f y ∂((C r).pointHaar : Measure _))) := by
  have he (N : ℕ) :
      (𝔼 k∈GlobalPointLaw.cell ⌊L (F.state.subseq N)⌋₊ F.period r.val a b,
        f (F.pointStructured N k.val))=
      (𝔼 k∈GlobalPointLaw.cell ⌊L (F.state.subseq N)⌋₊ F.period r.val a b,
        f (QuotientGroup.mk (F.state.domain.embed (F.structuredPart N (k.val:ℤ))*F.residue r))) := by
    apply Finset.expect_congr rfl
    intro k hk
    have hh:= (GlobalPointLaw.mem_cell.mp hk).2.2
    have hr : F.natResidue k.val=r:=Fin.ext hh
    simp only [pointStructured,hr]
  simp_rw [he]
  exact (C r).structured_local_haar hL ht ha hab hb f

lemma empirical_eq_expect {X : Type*} [TopologicalSpace X] {M : ℕ}
    (q : Fin M → X) (Φ : ℝ → C(X,ℂ)) :
    GlobalPointLaw.empirical q Φ=(𝔼 k : Fin M,Φ ((k.val:ℝ)/M) (q k)) := by
  rw [Fintype.expect_eq_sum_div_card]
  simp [GlobalPointLaw.empirical,Complex.real_smul,div_eq_mul_inv,mul_comm]

 

theorem global_point_law (hL : ∀ N,0 < L N) (ht : Tendsto L atTop atTop)
    (f : C(G⧸Γ,ℂ)) :
    Tendsto (fun N=>𝔼 k : Fin ⌊L (F.state.subseq N)⌋₊,
      f (QuotientGroup.mk (P (F.state.subseq N) (k.val:ℤ)))) atTop
      (𝓝 (GlobalPointLaw.betaMixture (fun r=>(C r).pointHaar) (F.limitTest f))) := by
  have hlen:=tendsto_nat_floor_atTop.comp (ht.comp F.state.strictmono.tendsto_atTop)
  have hglobal:=GlobalPointLaw.global_point_law_of_local_haar hlen F.period_pos
    (fun N k=>F.pointStructured N k.val) (fun r=>(C r).pointHaar) (F.limitTest f)
    (F.limitTest_continuous f) (fun _ _ ha hab hb r g=>F.pointStructured_local C hL ht ha hab hb r g)
  simp_rw [empirical_eq_expect] at hglobal
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [Metric.tendsto_nhds.mp hglobal (ε/2) (by positivity),
    F.smooth_floor_tests hL ht (leftTest f) (leftTest_continuous f) (ε/4) (by positivity),
    hlen.eventually (eventually_gt_atTop 0)] with N hN hs hpos
  have : Nonempty (Fin ⌊L (F.state.subseq N)⌋₊):=⟨⟨0,hpos⟩⟩
  have hbound : dist
      (𝔼 k : Fin ⌊L (F.state.subseq N)⌋₊,f (QuotientGroup.mk (P (F.state.subseq N) (k.val:ℤ))))
      (𝔼 k : Fin ⌊L (F.state.subseq N)⌋₊,
        F.limitTest f ((k.val:ℝ)/(⌊L (F.state.subseq N)⌋₊:ℝ)) (F.pointStructured N k.val)) ≤ ε/4 := by
    rw [dist_eq_norm,←Finset.expect_sub_distrib]
    apply (RCLike.norm_expect_le (K:=ℂ)).trans
    apply Finset.expect_le Finset.univ_nonempty
    intro k hk
    rw [F.point_realization]
    have hh:= (ContinuousMap.dist_apply_le_dist (F.pointStructured N k.val)).trans (hs k).le
    simpa only [dist_eq_norm,leftTest,limitTest,ContinuousMap.coe_mk] using hh
  simp only [Function.comp_apply] at hN
  exact (dist_triangle _
    (𝔼 k : Fin ⌊L (F.state.subseq N)⌋₊,
      F.limitTest f ((k.val:ℝ)/(⌊L (F.state.subseq N)⌋₊:ℝ)) (F.pointStructured N k.val))
    _).trans_lt (by linarith only [hbound,hN,hε])

end AllLevelFactorization.Factorization
end
 
end

section
 

 

noncomputable section
open scoped BigOperators Topology ENNReal
open MeasureTheory Filter
namespace ProbabilityMixtures
variable {I X Y : Type*} [Fintype I] [Nonempty I]
variable [MeasurableSpace X] [MeasurableSpace Y]

def finiteAverage (μ : I → ProbabilityMeasure X) : ProbabilityMeasure X :=
  ⟨(Fintype.card I : ℝ≥0∞)⁻¹ • ∑ i, (μ i : Measure X), by
    constructor
    simp only [Measure.smul_apply,Measure.finsetSum_apply,measure_univ,
      Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one,smul_eq_mul]
    exact ENNReal.inv_mul_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _)⟩

lemma finiteAverage_integral (μ : I → ProbabilityMeasure X) (f : X → ℂ)
    (hf : ∀ i,Integrable f (μ i : Measure X)) :
    (∫ x,f x ∂(finiteAverage μ : Measure X))=(1/(Fintype.card I:ℝ)) •
      ∑ i,∫ x,f x ∂(μ i : Measure X) := by
  change (∫ x,f x ∂((Fintype.card I:ℝ≥0∞)⁻¹ • ∑ i,(μ i:Measure X)))=_
  rw [integral_smul_measure,integral_finsetSum_measure (fun i _=>hf i)]
  simp

def unitTime : Measure ℝ:=volume.restrict (Set.Icc 0 1)
instance unitTime_probability : IsProbabilityMeasure unitTime := by
  constructor
  simp [unitTime]

variable [TopologicalSpace X] [TopologicalSpace Y] [BorelSpace X] [BorelSpace Y]
variable [SecondCountableTopology X]

def intervalPush (μ : ProbabilityMeasure X) (h : C(ℝ×X,Y)) : ProbabilityMeasure Y :=
  ⟨(unitTime.prod (μ:Measure X)).map h, inferInstance⟩

lemma intervalPush_integral [CompactSpace Y] (μ : ProbabilityMeasure X)
    (h : C(ℝ×X,Y)) (f : C(Y,ℂ)) :
    (∫ y,f y ∂(intervalPush μ h : Measure Y))=
      ∫ β in (0:ℝ)..1,∫ x,f (h (β,x)) ∂(μ:Measure X) := by
  change (∫ y,f y ∂(unitTime.prod (μ:Measure X)).map h)=_
  rw [integral_map h.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  have hf : Integrable (fun z : ℝ×X=>f (h z)) (unitTime.prod (μ:Measure X)):=
    Integrable.of_bound (f.continuous.comp h.continuous).aestronglyMeasurable ‖f‖
      (Eventually.of_forall fun z=>f.norm_coe_le_norm (h z))
  rw [integral_prod _ hf]
  rw [intervalIntegral.integral_of_le zero_le_one]
  exact integral_Icc_eq_integral_Ioc

variable [MeasurableSingletonClass Y]
def empirical (M : ℕ) (q : ℕ → Y) : ProbabilityMeasure Y :=
  if hM : 0<M then
    letI : Nonempty (Fin M):=⟨⟨0,hM⟩⟩
    finiteAverage (fun k : Fin M=>(⟨Measure.dirac (q k.val),inferInstance⟩ : ProbabilityMeasure Y))
  else ⟨Measure.dirac (q 0),inferInstance⟩

lemma empirical_integral [CompactSpace Y] (M : ℕ) (hM : 0<M) (q : ℕ → Y) (f : C(Y,ℂ)) :
    (∫ y,f y ∂(empirical M q : Measure Y))=𝔼 k : Fin M,f (q k.val) := by
  let : Nonempty (Fin M):=⟨⟨0,hM⟩⟩
  let μ : Fin M → ProbabilityMeasure Y := fun k=>⟨Measure.dirac (q k.val),inferInstance⟩
  have hμ : ∀ k, Integrable f (μ k : Measure Y) := fun _=>
    Integrable.of_bound f.continuous.aestronglyMeasurable ‖f‖
      (Eventually.of_forall f.norm_coe_le_norm)
  have H := finiteAverage_integral μ f hμ
  calc
    (∫ y,f y ∂(empirical M q : Measure Y)) = (∫ y,f y ∂(finiteAverage μ : Measure Y)) := by
      congr 1
      simp only [empirical,hM,↓reduceDIte,μ]
    _ = (1/(Fintype.card (Fin M):ℝ)) • ∑ k, ∫ y,f y ∂(μ k : Measure Y) := H
    _ = 𝔼 k : Fin M,f (q k.val) := by
      simp [μ,Fintype.expect_eq_sum_div_card,Complex.real_smul,div_eq_mul_inv,Finset.mul_sum,mul_comm]

end ProbabilityMixtures

end
end
end

end OAI
