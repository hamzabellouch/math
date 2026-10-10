import Mathlib
import OAI.Analysis.SymmetricDomains.CartanUniqueness
import OAI.Analysis.SymmetricDomains.ActionAutomorphismHomRange
import OAI.Analysis.SymmetricDomains.UniformLatticeHaarRight

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Topology TopologicalSpace MeasureTheory
open scoped Classical

theorem bounded_divisible_automorphism_unimodular {n : ℕ} {U : Set (Affine n)}
    (hU : IsOpen U) (hc : IsPreconnected U) (hb : Bornology.IsBounded U)
    [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    let _ : LocallyCompactSpace (Biholomorph U U) :=
      bounded_divisible_automorphism_locallyCompact hU hc hb Γ hhol p
    let _ : MeasurableSpace (Biholomorph U U) := borel (Biholomorph U U)
    let _ : BorelSpace (Biholomorph U U) := ⟨rfl⟩
    (Measure.haar : Measure (Biholomorph U U)).IsMulRightInvariant := by
  let : LocallyCompactSpace (Biholomorph U U) :=
    bounded_divisible_automorphism_locallyCompact hU hc hb Γ hhol p
  let : MeasurableSpace (Biholomorph U U) := borel (Biholomorph U U)
  let : BorelSpace (Biholomorph U U) := ⟨rfl⟩
  let H := (actionAutomorphismHom U Γ hhol).range
  obtain ⟨hclosed,hdiscrete⟩ := actionAutomorphismHom_range_discrete Γ hhol p
  let : DiscreteTopology H := hdiscrete
  obtain ⟨K,hK,hcover⟩ := bounded_divisible_automorphism_compact_cover hU hc hb Γ hhol p
  apply uniform_lattice_haar_right_invariant H hclosed K hK
  intro a
  obtain ⟨γ,b,hb,h⟩ := hcover a
  exact ⟨⟨actionAutomorphismHom U Γ hhol γ,⟨γ,rfl⟩⟩,b,hb,h⟩

end

open Set Filter Topology TopologicalSpace
open scoped Classical
namespace Biholomorph
variable {n : ℕ} {U : Set (Affine n)}

def ambientAut (a : Biholomorph U U) : Affine n → Affine n :=
  ambientExtend (fun x : U => (a.toHomeomorph x).val)

@[simp] theorem ambientAut_apply (a : Biholomorph U U) (p : U) :
    a.ambientAut p.val=(a.toHomeomorph p).val := ambientExtend_apply _ p

theorem ambientAut_analytic (hU : IsOpen U) (a : Biholomorph U U) :
    AnalyticOnNhd ℂ a.ambientAut U := a.holomorphic_toFun.analyticOnNhd_extend hU

def derivativeAt (a : Biholomorph U U) (p : U) : Affine n →L[ℂ] Affine n :=
  fderiv ℂ a.ambientAut p.val

theorem derivativeAt_mul (hU : IsOpen U) (a b : Biholomorph U U) (p : U) :
    (a*b).derivativeAt p=(a.derivativeAt (b.toHomeomorph p)).comp (b.derivativeAt p) := by
  have he : (a*b).ambientAut =ᶠ[𝓝 p.val] a.ambientAut ∘ b.ambientAut := by
    filter_upwards [hU.mem_nhds p.property] with x hx
    rw [Function.comp_apply,ambientAut_apply (a*b) ⟨x,hx⟩,
      ambientAut_apply b ⟨x,hx⟩,ambientAut_apply a (b.toHomeomorph ⟨x,hx⟩)]
    rfl
  rw [derivativeAt,he.fderiv_eq]
  have hd := fderiv_comp p.val
    (by simpa only [ambientAut_apply] using
      (a.ambientAut_analytic hU _ (b.toHomeomorph p).property).differentiableAt)
    (b.ambientAut_analytic hU _ p.property).differentiableAt
  simpa only [derivativeAt,ambientAut_apply] using hd

@[simp] theorem derivativeAt_one (hU : IsOpen U) (p : U) :
    (1 : Biholomorph U U).derivativeAt p=1 := by
  have he : (1 : Biholomorph U U).ambientAut =ᶠ[𝓝 p.val] id := by
    filter_upwards [hU.mem_nhds p.property] with x hx
    exact ambientAut_apply 1 ⟨x,hx⟩
  rw [derivativeAt,he.fderiv_eq]
  rw [fderiv_id]
  rfl

theorem eq_one_of_firstJet (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) (a : Biholomorph U U) (p : U)
    (hp : a.toHomeomorph p=p) (hd : a.derivativeAt p=1) : a=1 := by
  have he := cartan_uniqueness_bounded hU hc hb (a.ambientAut_analytic hU)
    (fun x hx => by
      rw [show a.ambientAut x=(a.toHomeomorph ⟨x,hx⟩).val from ambientAut_apply a ⟨x,hx⟩]
      exact (a.toHomeomorph ⟨x,hx⟩).property) p.property
    (by simpa only [ambientAut_apply] using congrArg Subtype.val hp)
    (by
      have h := (a.ambientAut_analytic hU _ p.property).differentiableAt.hasFDerivAt
      rwa [← derivativeAt,hd] at h)
  apply ext
  intro q
  apply Subtype.ext
  simpa only [ambientAut_apply,id_eq,one_apply] using he q.property

def firstJet (p : U) (a : Biholomorph U U) : U × (Affine n →L[ℂ] Affine n) :=
  (a.toHomeomorph p,a.derivativeAt p)

theorem firstJet_injective (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) (p : U) : Function.Injective (firstJet p) := by
  intro a b hab
  have hp : a.toHomeomorph p=b.toHomeomorph p := congrArg Prod.fst hab
  have hd : a.derivativeAt p=b.derivativeAt p := congrArg Prod.snd hab
  have he : b⁻¹*a=1 := by
    apply eq_one_of_firstJet hU hc hb (b⁻¹*a) p
    · simp only [mul_apply,inv_apply,hp,Homeomorph.symm_apply_apply]
    · rw [derivativeAt_mul hU,hp,hd]
      rw [← derivativeAt_mul hU,inv_mul_cancel,derivativeAt_one hU]
  exact (inv_mul_eq_one.mp he).symm

theorem ambientAut_tendstoLocallyUniformly {ι : Type*} [LocallyCompactSpace U]
    {a : ι → Biholomorph U U} {b : Biholomorph U U} {l : Filter ι}
    (h : Tendsto a l (𝓝 b)) :
    TendstoLocallyUniformlyOn (fun j => (a j).ambientAut) b.ambientAut l U := by
  let v : C(U,Affine n) := ⟨Subtype.val,continuous_subtype_val⟩
  have ht := (((ContinuousMap.continuous_postcomp v).comp
    continuous_compactOpenPair.fst).tendsto b).comp h
  have hu := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp ht
  change TendstoLocallyUniformly (fun j (x : U) => ((a j).toHomeomorph x).val)
    (fun x : U => (b.toHomeomorph x).val) l at hu
  apply tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr
  simpa only [Function.comp_def,ambientAut_apply] using hu

theorem derivativeAt_continuous (hU : IsOpen U) [LocallyCompactSpace U] (p : U) :
    Continuous (fun a : Biholomorph U U => a.derivativeAt p) := by
  apply continuous_iff_seqContinuous.mpr
  intro a b hab
  apply (tendstoLocallyUniformlyOn_fderiv hU (ambientAut_tendstoLocallyUniformly hab) ?_).tendsto_at
    p.property
  intro x hx
  exact ⟨U,hU.mem_nhds hx,Eventually.of_forall fun j => (a j).ambientAut_analytic hU |>.differentiableOn⟩

theorem firstJet_continuous (hU : IsOpen U) [LocallyCompactSpace U] (p : U) :
    Continuous (firstJet p) :=
  (continuous_evaluation p).prodMk (derivativeAt_continuous hU p)

theorem firstJet_isClosedEmbedding (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    IsClosedEmbedding (firstJet p) := by
  have hp : IsProperMap (firstJet p) :=
    isProperMap_of_comp_of_t2 (firstJet_continuous hU p) continuous_fst
      (bounded_divisible_automorphism_evaluation_proper hU hc hb Γ hhol p)
  exact .of_continuous_injective_isClosedMap (firstJet_continuous hU p)
    (firstJet_injective hU hc hb p) hp.isClosedMap

theorem compact_stabilizer (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    IsCompact {a : Biholomorph U U | a.toHomeomorph p=p} := by
  exact (bounded_divisible_automorphism_evaluation_proper hU hc hb Γ hhol p).isCompact_preimage
    isCompact_singleton

theorem compact_faithful_isotropy (hU : IsOpen U) (hc : IsPreconnected U)
    (hb : Bornology.IsBounded U) [LocallyCompactSpace U]
    (Γ : Type*) [Group Γ] [TopologicalSpace Γ] [DiscreteTopology Γ]
    [MulAction Γ U] [ProperSMul Γ U]
    [CompactSpace (Quotient (MulAction.orbitRel Γ U))]
    (hhol : ∀ γ : Γ, HolomorphicOnSubset U (fun p => (γ • p : U).val)) (p : U) :
    IsCompact ((fun a : Biholomorph U U => a.derivativeAt p) '' {a | a.toHomeomorph p=p}) ∧
    InjOn (fun a : Biholomorph U U => a.derivativeAt p) {a | a.toHomeomorph p=p} := by
  refine ⟨(compact_stabilizer hU hc hb Γ hhol p).image (derivativeAt_continuous hU p),?_⟩
  intro a ha b hbfix hd
  apply firstJet_injective hU hc hb p
  exact Prod.ext (ha.trans hbfix.symm) hd

end Biholomorph
end Release061

end

end OAI
