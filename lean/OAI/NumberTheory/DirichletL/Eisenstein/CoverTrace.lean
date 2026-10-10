import OAI.NumberTheory.DirichletL.Eisenstein.IntegralCover

namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

lemma integralCoverSheet_measure (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) (q : IntegralCoverCosets H K)
    (S : Set (IntegralOrbitQuotient K)) (hS : MeasurableSet S) :
    hyperbolicVolume ((integralOrbitProjection K) ⁻¹' S ∩ integralCoverSheet H K q)=
      integralQuotientVolume K S := by
  have he : (integralOrbitProjection K) ⁻¹' S ∩ integralCoverSheet H K q=
      (fun w=>integralCoverRep H K q • w) ⁻¹'
        ((integralOrbitProjection K) ⁻¹' S ∩ hyperbolicFundamentalSet K) := by
    ext w
    change (integralOrbitProjection K w∈S ∧ integralCoverRep H K q•w∈hyperbolicFundamentalSet K) ↔
      (integralOrbitProjection K (integralCoverRep H K q•w)∈S ∧
        integralCoverRep H K q•w∈hyperbolicFundamentalSet K)
    rw [integralSubgroup_smul,integralOrbitProjection_eq]
  rw [he,measure_preimage_smul]
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection K) hS,
    Measure.restrict_apply ((measurable_integralOrbitProjection K) hS)]

theorem integralCoverMap_measure {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    Measure.map (integralCoverMap hHK) (integralQuotientVolume H)=
      (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  have hH : H≤CubicKubota.levelThree := hHK.trans hK
  rw [←integralQuotientVolume_independent H hH (integralCoverDomain H K)
    (integralCoverDomain_isFundamentalDomain hHK hK)]
  rw [Measure.map_map (integralCoverMap_measurable hHK) (measurable_integralOrbitProjection H)]
  change Measure.map (integralOrbitProjection K) (hyperbolicVolume.restrict (integralCoverDomain H K))=_
  apply Measure.ext
  intro S hS
  rw [Measure.map_apply (measurable_integralOrbitProjection K) hS,
    Measure.restrict_apply ((measurable_integralOrbitProjection K) hS),Measure.smul_apply,smul_eq_mul]
  rw [integralCoverDomain,Set.inter_iUnion]
  rw [measure_iUnion]
  · simp_rw [integralCoverSheet_measure H K _ S hS]
    rw [tsum_fintype]
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    congr 1
    rw [Subgroup.relIndex,Subgroup.index,Nat.card_eq_fintype_card]
  · intro q r hqr
    exact (integralCoverSheet_pairwiseDisjoint H K hK hqr).mono Set.inter_subset_right Set.inter_subset_right
  · intro q
    exact ((measurable_integralOrbitProjection K) hS).inter (integralCoverSheet_measurable H K q)

lemma integralCoverMap_measurePreserving {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    MeasurePreserving (integralCoverMap hHK) (integralQuotientVolume H)
      ((H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) :=
  ⟨integralCoverMap_measurable hHK,integralCoverMap_measure hHK hK⟩

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal InnerProductSpace InnerProduct
open Finset AddChar MulChar EisensteinEmbedding

section
local notation "O" => ActualEisensteinCubic.O

abbrev IntegralQuotientL2 (H : Subgroup (SL(2,ActualEisensteinCubic.O))) :=
  Lp ℂ 2 (integralQuotientVolume H)

def integralCoverPullback {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    IntegralQuotientL2 K→L[ℂ]IntegralQuotientL2 H :=
  (Lp.compMeasurePreservingₗᵢ ℂ (integralCoverMap hHK)
    (integralCoverMap_measurePreserving hHK hK)).toContinuousLinearMap.comp
      (dominatedComplexL2 (by simp : (H.relIndex K:ℝ≥0∞)≠⊤) le_rfl)

theorem integralCoverPullback_ae {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (F : IntegralQuotientL2 K) :
    integralCoverPullback hHK hK F=ᵐ[integralQuotientVolume H]
      fun q=>F (integralCoverMap hHK q) := by
  have hm := integralCoverMap_measurePreserving hHK hK
  have he := dominatedComplexL2_ae
    (by simp : (H.relIndex K:ℝ≥0∞)≠⊤)
    (le_rfl : (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K≤
      (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) F
  exact (Lp.coeFn_compMeasurePreserving _ hm).trans
    (hm.quasiMeasurePreserving.ae_eq_comp he)

theorem integralCoverPullback_norm_le {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (F : IntegralQuotientL2 K) :
    ‖integralCoverPullback hHK hK F‖≤(H.relIndex K:ℝ)^((1:ℝ)/2)*‖F‖ := by
  change ‖Lp.compMeasurePreserving (integralCoverMap hHK)
    (integralCoverMap_measurePreserving hHK hK)
    (dominatedComplexL2 (by simp : (H.relIndex K:ℝ≥0∞)≠⊤) le_rfl F)‖≤_
  rw [Lp.norm_compMeasurePreserving]
  simpa only [ENNReal.toReal_natCast] using dominatedComplexL2_norm_le
    (by simp : (H.relIndex K:ℝ≥0∞)≠⊤)
    (le_rfl : (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K≤
      (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) F

theorem integralCoverPullback_inner {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (F G : IntegralQuotientL2 K) :
    ⟪integralCoverPullback hHK hK F,integralCoverPullback hHK hK G⟫_ℂ=
      (H.relIndex K:ℂ)*⟪F,G⟫_ℂ := by
  let changeMeasure : IntegralQuotientL2 K→L[ℂ]
      Lp ℂ 2 ((H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) :=
    dominatedComplexL2 (by simp : (H.relIndex K:ℝ≥0∞)≠⊤) le_rfl
  change ⟪(Lp.compMeasurePreservingₗᵢ ℂ (integralCoverMap hHK)
    (integralCoverMap_measurePreserving hHK hK)) (changeMeasure F),
    (Lp.compMeasurePreservingₗᵢ ℂ (integralCoverMap hHK)
    (integralCoverMap_measurePreserving hHK hK)) (changeMeasure G)⟫_ℂ=_
  rw [LinearIsometry.inner_map_map,L2.inner_def,L2.inner_def]
  have hF := dominatedComplexL2_ae
    (by simp : (H.relIndex K:ℝ≥0∞)≠⊤)
    (le_rfl : (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K≤
      (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) F
  have hG := dominatedComplexL2_ae
    (by simp : (H.relIndex K:ℝ≥0∞)≠⊤)
    (le_rfl : (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K≤
      (H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) G
  calc
    _ = ∫q,⟪F q,G q⟫_ℂ ∂((H.relIndex K:ℝ≥0∞) • integralQuotientVolume K) := by
      apply integral_congr_ae
      filter_upwards [hF,hG] with q hqF hqG
      change ⟪changeMeasure F q,changeMeasure G q⟫_ℂ=⟪F q,G q⟫_ℂ
      rw [show changeMeasure F q=F q from hqF,show changeMeasure G q=G q from hqG]
    _ = _ := by
      rw [integral_smul_measure]
      simp only [ENNReal.toReal_natCast,Complex.real_smul,Complex.ofReal_natCast]

def integralCoverTrace {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    IntegralQuotientL2 H→L[ℂ]IntegralQuotientL2 K :=
  ContinuousLinearMap.adjoint (integralCoverPullback hHK hK)

theorem integralCoverTrace_pairing {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (F : IntegralQuotientL2 K) (G : IntegralQuotientL2 H) :
    ⟪F,integralCoverTrace hHK hK G⟫_ℂ=⟪integralCoverPullback hHK hK F,G⟫_ℂ :=
  ContinuousLinearMap.adjoint_inner_right _ _ _

theorem integralCoverTrace_pullback {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (F : IntegralQuotientL2 K) :
    integralCoverTrace hHK hK (integralCoverPullback hHK hK F)=(H.relIndex K:ℂ) • F := by
  apply ext_inner_left ℂ
  intro G
  rw [integralCoverTrace_pairing,integralCoverPullback_inner,inner_smul_right]

theorem integralCoverPullback_opNorm_le {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    ‖integralCoverPullback hHK hK‖≤(H.relIndex K:ℝ)^((1:ℝ)/2) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  exact integralCoverPullback_norm_le hHK hK

theorem integralCoverTrace_opNorm_le {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    ‖integralCoverTrace hHK hK‖≤(H.relIndex K:ℝ)^((1:ℝ)/2) := by
  rw [integralCoverTrace,ContinuousLinearMap.adjoint.norm_map]
  exact integralCoverPullback_opNorm_le hHK hK

def integralCoverAverage {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    IntegralQuotientL2 H→L[ℂ]IntegralQuotientL2 K :=
  (H.relIndex K:ℂ)⁻¹ • integralCoverTrace hHK hK

theorem integralCoverAverage_pullback {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (F : IntegralQuotientL2 K) :
    integralCoverAverage hHK hK (integralCoverPullback hHK hK F)=F := by
  have hn : (H.relIndex K:ℂ)≠0 := Nat.cast_ne_zero.mpr Subgroup.relIndex_ne_zero
  change (H.relIndex K:ℂ)⁻¹ • integralCoverTrace hHK hK (integralCoverPullback hHK hK F)=F
  rw [integralCoverTrace_pullback,smul_smul,inv_mul_cancel₀ hn,one_smul]

theorem integralCoverPullback_injective {H K : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (hHK : H≤K) (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K] :
    Function.Injective (integralCoverPullback hHK hK) :=
  Function.LeftInverse.injective (integralCoverAverage_pullback hHK hK)

end

local notation "O" => ActualEisensteinCubic.O

def integralCoverFiberPoint (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) : IntegralOrbitQuotient H :=
  Quotient.liftOn' q (fun r : K=>integralOrbitProjection H (r⁻¹•w)) (by
    intro a b hab
    have hh : b⁻¹*a∈H.subgroupOf K := by
      have h : a⁻¹*b∈H.subgroupOf K := QuotientGroup.leftRel_apply.mp hab
      simpa only [mul_inv_rev,inv_inv] using (H.subgroupOf K).inv_mem h
    apply Quotient.sound
    refine ⟨⟨((b⁻¹*a:K):SL(2,ActualEisensteinCubic.O)),hh⟩,?_⟩
    change (b⁻¹*a)•(a⁻¹•w)=b⁻¹•w
    simp only [mul_smul,smul_inv_smul])

lemma integralCoverFiberPoint_mk (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (r : K) (w : HyperbolicSpace) :
    integralCoverFiberPoint H K r w=integralOrbitProjection H (r⁻¹•w) := rfl

lemma integralCoverFiberPoint_rep (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (w : HyperbolicSpace) :
    integralCoverFiberPoint H K q w=
      integralOrbitProjection H ((integralCoverRep H K q)⁻¹•w) := by
  conv_lhs => rw [←QuotientGroup.out_eq' q]
  rfl

lemma integralCoverFiberPoint_smul (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) (k : K) (w : HyperbolicSpace) :
    integralCoverFiberPoint H K (k•q) (k•w)=integralCoverFiberPoint H K q w := by
  induction q using Quotient.inductionOn with
  | _ r =>
    change integralOrbitProjection H ((k*r)⁻¹•(k•w))=integralOrbitProjection H (r⁻¹•w)
    rw [mul_inv_rev,mul_smul,inv_smul_smul]

lemma integralCoverFiberPoint_measurable (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (q : IntegralCoverCosets H K) : Measurable (integralCoverFiberPoint H K q) := by
  have he : integralCoverFiberPoint H K q=fun w=>
      integralOrbitProjection H ((integralCoverRep H K q)⁻¹•w) :=
    funext (integralCoverFiberPoint_rep H K q)
  rw [he]
  exact (measurable_integralOrbitProjection H).comp (measurable_const_smul _)

def integralCoverTraceLift (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (w : HyperbolicSpace) : ℂ :=
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  ∑q : IntegralCoverCosets H K,f (integralCoverFiberPoint H K q w)

lemma integralCoverTraceLift_smul (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (k : K) (w : HyperbolicSpace) :
    integralCoverTraceLift H K f (k•w)=integralCoverTraceLift H K f w := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  unfold integralCoverTraceLift
  rw [←(MulAction.bijective k).sum_comp (fun q=>f (integralCoverFiberPoint H K q (k•w)))]
  simp only [integralCoverFiberPoint_smul]

def integralCoverTraceFunction (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) : IntegralOrbitQuotient K→ℂ :=
  Quotient.lift (integralCoverTraceLift H K f) (by
    rintro w u ⟨k,rfl⟩
    exact (integralCoverTraceLift_smul H K f k w).symm)

lemma integralCoverTraceFunction_projection (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (w : HyperbolicSpace) :
    integralCoverTraceFunction H K f (integralOrbitProjection K w)=integralCoverTraceLift H K f w := rfl

lemma integralCoverTraceFunction_measurable (H K : Subgroup (SL(2,ActualEisensteinCubic.O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (hf : Measurable f) :
    Measurable (integralCoverTraceFunction H K f) := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  apply measurable_from_quotient.mpr
  change Measurable (integralCoverTraceLift H K f)
  unfold integralCoverTraceLift
  exact Finset.measurable_sum Finset.univ (fun q _=>hf.comp (integralCoverFiberPoint_measurable H K q))

theorem integralCoverTraceFunction_cusp_decay (H K : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hK : K≤CubicKubota.levelThree) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H→ℂ) (C : ℝ)
    (hdec : ∀M : CubicKubota.levelThree,∀z : ℂ,∀v : ℝ,∀hv : 0<v,1<v→
      ‖f (integralOrbitProjection H (complexMatrix M•upperPoint z v hv))‖≤C/v^3)
    (M : CubicKubota.levelThree) (z : ℂ) (v : ℝ) (hv : 0<v) (hlarge : 1<v) :
    ‖integralCoverTraceFunction H K f
      (integralOrbitProjection K (complexMatrix M•upperPoint z v hv))‖≤
        (H.relIndex K:ℝ)*C/v^3 := by
  let : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  change ‖∑q : IntegralCoverCosets H K,
    f (integralCoverFiberPoint H K q (complexMatrix M•upperPoint z v hv))‖≤_
  calc
    _ ≤ ∑q : IntegralCoverCosets H K,
        ‖f (integralCoverFiberPoint H K q (complexMatrix M•upperPoint z v hv))‖ :=
      norm_sum_le _ _
    _ ≤ ∑_q : IntegralCoverCosets H K,C/v^3 := by
      apply Finset.sum_le_sum
      intro q _
      let r := integralCoverRep H K q
      let N : CubicKubota.levelThree :=
        ⟨(r:SL(2,ActualEisensteinCubic.O))⁻¹*(M:SL(2,ActualEisensteinCubic.O)),
          CubicKubota.levelThree.mul_mem (CubicKubota.levelThree.inv_mem (hK r.property)) M.property⟩
      have he : integralCoverFiberPoint H K q (complexMatrix M•upperPoint z v hv)=
          integralOrbitProjection H (complexMatrix N•upperPoint z v hv) := by
        rw [integralCoverFiberPoint_rep]
        change integralOrbitProjection H
          (integralComplexMatrix (r:SL(2,ActualEisensteinCubic.O))⁻¹•(complexMatrix M•upperPoint z v hv))=_
        change _=integralOrbitProjection H
          (integralComplexMatrix ((r:SL(2,ActualEisensteinCubic.O))⁻¹*(M:SL(2,ActualEisensteinCubic.O)))•upperPoint z v hv)
        rw [map_mul,mul_smul]
        rfl
      rw [he]
      exact hdec N z v hv hlarge
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      have hc : Fintype.card (IntegralCoverCosets H K)=H.relIndex K := by
        rw [Subgroup.relIndex,Subgroup.index,Nat.card_eq_fintype_card]
      rw [hc]
      ring

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal
open Finset AddChar MulChar EisensteinEmbedding

local notation "O" => ActualEisensteinCubic.O

def IntegralCoverIntertwines {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) : Prop :=
  ∀h : H,g*integralComplexMatrix (h:SL(2,ActualEisensteinCubic.O))=
    integralComplexMatrix (e h:SL(2,ActualEisensteinCubic.O))*g

lemma integralCoverIntertwines_action {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (h : H) (w : HyperbolicSpace) : g•(h•w)=(e h)•(g•w) := by
  rw [integralSubgroup_smul,integralSubgroup_smul,←mul_smul,he, mul_smul]

lemma integralCoverIntertwines_inverse {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    IntegralCoverIntertwines e.symm g⁻¹ := by
  intro j
  have hh := he (e.symm j)
  rw [e.apply_symm_apply] at hh
  have hh' := congrArg (fun A : SL(2,ℂ)=>g⁻¹*A*g⁻¹) hh
  simpa only [mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,mul_inv_cancel,mul_one] using hh'.symm

def integralConjugateMap {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    IntegralOrbitQuotient H→IntegralOrbitQuotient J :=
  Quotient.map' (fun w=>g•w) (by
    rintro w u ⟨h,rfl⟩
    exact ⟨e h,(integralCoverIntertwines_action e g he h w).symm⟩)

lemma integralConjugateMap_projection {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) (w : HyperbolicSpace) :
    integralConjugateMap e g he (integralOrbitProjection H w)=
      integralOrbitProjection J (g•w) := rfl

lemma integralConjugateMap_measurable {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    Measurable (integralConjugateMap e g he) := by
  apply measurable_from_quotient.mpr
  exact (measurable_integralOrbitProjection J).comp (measurable_const_smul g)

lemma integralConjugateMap_continuous {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    Continuous (integralConjugateMap e g he) :=
  (continuous_hyperbolic_action g).quotient_map' _

lemma integralConjugateMap_inverse {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (q : IntegralOrbitQuotient H) :
    integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
      (integralConjugateMap e g he q)=q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection H (g⁻¹•(g•w))=integralOrbitProjection H w
    rw [inv_smul_smul]

def integralConjugateHomeomorph {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g) :
    IntegralOrbitQuotient H≃ₜIntegralOrbitQuotient J where
  toFun := integralConjugateMap e g he
  invFun := integralConjugateMap e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
  left_inv := integralConjugateMap_inverse e g he
  right_inv q := by
    induction q using Quotient.inductionOn with
    | _ w =>
      change integralOrbitProjection J (g•(g⁻¹•w))=integralOrbitProjection J w
      rw [smul_inv_smul]
  continuous_toFun := integralConjugateMap_continuous e g he
  continuous_invFun := integralConjugateMap_continuous e.symm g⁻¹ _

lemma integralConjugate_fundamentalDomain {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) :
    IsFundamentalDomain J ((fun w : HyperbolicSpace=>g•w) '' hyperbolicFundamentalSet H)
      hyperbolicVolume := by
  apply (hyperbolicFundamentalSet_isFundamentalDomain H hH).image_of_equiv
    (MulAction.toPerm g)
    (show Measure.QuasiMeasurePreserving (MulAction.toPerm g).symm
      hyperbolicVolume hyperbolicVolume from
      (measurePreserving_smul g⁻¹ hyperbolicVolume).quasiMeasurePreserving)
    e.symm.toEquiv
  intro j w
  change g•(e.symm j•w)=j•(g•w)
  simpa only [e.apply_symm_apply] using integralCoverIntertwines_action e g he (e.symm j) w

theorem integralConjugateMap_measurePreserving {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree) :
    MeasurePreserving (integralConjugateMap e g he) (integralQuotientVolume H)
      (integralQuotientVolume J) := by
  refine ⟨integralConjugateMap_measurable e g he,?_⟩
  have hmap := (measurePreserving_smul g hyperbolicVolume).restrict_image_emb
    (measurableEmbedding_const_smul g) (hyperbolicFundamentalSet H)
  change Measure.map (integralConjugateMap e g he)
    (Measure.map (integralOrbitProjection H) (hyperbolicVolume.restrict (hyperbolicFundamentalSet H)))=_
  rw [Measure.map_map (integralConjugateMap_measurable e g he) (measurable_integralOrbitProjection H)]
  change Measure.map ((integralOrbitProjection J) ∘ (fun w : HyperbolicSpace=>g•w))
    (hyperbolicVolume.restrict (hyperbolicFundamentalSet H))=_
  rw [←Measure.map_map (measurable_integralOrbitProjection J) (measurable_const_smul g),hmap.map_eq]
  exact integralQuotientVolume_independent J hJ _ (integralConjugate_fundamentalDomain e g he hH)

def integralConjugatePullback {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree) :
    Lp ℂ 2 (integralQuotientVolume J)→ₗᵢ[ℂ]Lp ℂ 2 (integralQuotientVolume H) :=
  Lp.compMeasurePreservingₗᵢ ℂ (integralConjugateMap e g he)
    (integralConjugateMap_measurePreserving e g he hH hJ)

theorem integralConjugatePullback_ae {H J : Subgroup (SL(2,ActualEisensteinCubic.O))}
    (e : H≃*J) (g : SL(2,ℂ)) (he : IntegralCoverIntertwines e g)
    (hH : H≤CubicKubota.levelThree) (hJ : J≤CubicKubota.levelThree)
    (F : Lp ℂ 2 (integralQuotientVolume J)) :
    integralConjugatePullback e g he hH hJ F=ᵐ[integralQuotientVolume H]
      fun q=>F (integralConjugateMap e g he q) :=
  Lp.coeFn_compMeasurePreserving F (integralConjugateMap_measurePreserving e g he hH hJ)

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ConcreteTraceCRT CubicKubota EisensteinCuspModThree
local notation "O" => ActualEisensteinCubic.O

lemma scaled_cusp_periodic_upper
    (F : HyperbolicSpace→ℂ) (v : ℝ) (hv : 0<v)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,
      F (upperPoint (3*(z+3*eisEmbedding n)) v hv)=F (upperPoint (3*z) v hv))
    (T : SL(2,ActualEisensteinCubic.O)) (hT : T 1 0=0) (n : ActualEisensteinCubic.O) (z : ℂ) :
    F (integralComplexMatrix T • upperPoint (3*(z+3*eisEmbedding n)) v hv)=
      F (integralComplexMatrix T • upperPoint (3*z) v hv) := by
  rw [integral_upper_triangular_action T hT,integral_upper_triangular_action T hT]
  have hleft : eisEmbedding (T 0 0)^2*(3*(z+3*eisEmbedding n))+
      eisEmbedding (T 0 0*T 0 1)=
      3*((eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)/3)+
        3*eisEmbedding ((T 0 0)^2*n)) := by
    simp only [map_mul,map_pow]
    ring
  have hright : eisEmbedding (T 0 0)^2*(3*z)+eisEmbedding (T 0 0*T 0 1)=
      3*(eisEmbedding (T 0 0)^2*z+eisEmbedding (T 0 0*T 0 1)/3) := by ring
  rw [hleft,hright]
  exact hp ((T 0 0)^2*n) _

theorem sourceCusp_scaled_periodic (M : SL(2,ActualEisensteinCubic.O)) (v : ℝ) (hv : 0<v)
    (n : ActualEisensteinCubic.O) (z : ℂ) :
    cubicSourceResidualFunction (integralComplexMatrix M •
      upperPoint (3*(z+3*eisEmbedding n)) v hv)=
    cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv) := by
  obtain ⟨G,j,T,hT,_,_,hM⟩ := three_cusp_decomposition M
  have he (w : HyperbolicSpace) : cubicSourceResidualFunction (integralComplexMatrix M • w)=
      levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) • (integralComplexMatrix T • w)) := by
    rw [hM,map_mul,map_mul,mul_smul,mul_smul,cubicSourceResidualFunction_automorphy]
  calc
    _ = levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) •
          (integralComplexMatrix T • upperPoint (3*(z+3*eisEmbedding n)) v hv)) := he _
    _ = levelTwoComplexCharacter G*cubicSourceResidualFunction
        (integralComplexMatrix (cuspRepresentative j) •
          (integralComplexMatrix T • upperPoint (3*z) v hv)) :=
      congrArg (fun w : ℂ=>levelTwoComplexCharacter G*w)
        (scaled_cusp_periodic_upper
          (fun w=>cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative j) • w))
          v hv (sourceCuspRepresentative_periodic j v hv) T hT n z)
    _ = _ := (he _).symm

lemma sourceCusp_scaled_continuous (M : SL(2,ActualEisensteinCubic.O)) (v : ℝ) (hv : 0<v) :
    Continuous (fun z : ℂ=>cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*z) v hv)) := by
  let c : ℂ→UpperCoordinates := fun z=>⟨(3*z,v),hv⟩
  have hc : Continuous c := by
    apply Continuous.subtype_mk
    exact (continuous_const.mul continuous_id).prodMk continuous_const
  have ht := (continuous_translatedUpperCoordinates (integralComplexMatrix M)).comp hc
  have hh : Continuous (fun z : ℂ=>integralComplexMatrix M • upperPoint (3*z) v hv) := by
    simpa only [Function.comp_def,c] using ht
  exact cubicSourceResidualFunction_continuous.comp hh

theorem sourceCusp_average_enlarged (M : SL(2,ActualEisensteinCubic.O)) (b : ActualEisensteinCubic.O) (hb : b≠0)
    (v : ℝ) (hv : 0<v) :
    (∫z in periodDomain,cubicSourceResidualFunction
      (integralComplexMatrix M • upperPoint (3*(eisEmbedding b*z)) v hv))=
      sourceCuspConstant M*(v:ℂ)^(2/3:ℂ) := by
  exact (period_integral_eisenstein_mul
    (fun z=>cubicSourceResidualFunction (integralComplexMatrix M • upperPoint (3*z) v hv))
    (sourceCusp_scaled_continuous M v hv).measurable
    (sourceCusp_scaled_periodic M v hv) b hb).trans (sourceCusp_average_all M v hv)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

theorem period_integral_eisenstein_affine (f : ℂ→ℂ) (hf : Measurable f)
    (hp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n)=f z) (b : ActualEisensteinCubic.O) (hb : b≠0) (c : ℂ) :
    (∫z in periodDomain,f (eisEmbedding b*z+c))=∫z in periodDomain,f z := by
  have hg : Measurable (fun z : ℂ=>f (z+c)) :=
    hf.comp (continuous_id.add continuous_const).measurable
  have hgp : ∀n : ActualEisensteinCubic.O,∀z : ℂ,f (z+3*eisEmbedding n+c)=f (z+c) := by
    intro n z
    rw [show z+3*eisEmbedding n+c=(z+c)+3*eisEmbedding n by ring,hp]
  rw [period_integral_eisenstein_mul (fun z=>f (z+c)) hg hgp b hb]
  simpa only [add_comm] using period_integral_translation f hp c

lemma complex_upper_triangular_bottom_ne_zero (T : SL(2,ℂ)) (hT : T 1 0=0) : T 1 1≠0 := by
  have hdet : T 0 0*T 1 1=1 := by
    simpa only [Matrix.det_fin_two,hT,mul_zero,sub_zero] using T.property
  intro hz
  rw [hz,mul_zero] at hdet
  exact zero_ne_one hdet

lemma complex_upper_triangular_action (T : SL(2,ℂ)) (hT : T 1 0=0)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    T • upperPoint z v hv=
      upperPoint ((T 0 0*z+T 0 1)/T 1 1) (v/‖T 1 1‖^2)
        (div_pos hv (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr
          (complex_upper_triangular_bottom_ne_zero T hT)))) := by
  have hd := complex_upper_triangular_bottom_ne_zero T hT
  have hs : star (T 1 1)≠0 := by
    intro hz
    apply hd
    simpa only [star_star,star_zero] using congrArg star hz
  have hprod : T 1 1*star (T 1 1)=((‖T 1 1‖^2:ℝ):ℂ) := by
    simpa only [Complex.star_def,Complex.normSq_eq_norm_sq] using Complex.mul_conj (T 1 1)
  rw [mobius_upperPoint]
  apply upperPoint_congr
  · simp only [hT,zero_mul,zero_add,star_zero,mul_zero,add_zero,norm_zero]
    norm_num only [zero_pow,mul_zero,add_zero]
    simp only [zero_mul,add_zero]
    rw [←hprod]
    field_simp [hd,hs]
  · simp only [hT,zero_mul,zero_add,norm_zero]
    norm_num

end CubicEisenstein

end

end OAI
