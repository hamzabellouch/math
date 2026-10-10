import Mathlib
import OAI.Analysis.SymmetricDomains.HolomorphicLocallyUniformLimit
import OAI.Analysis.SymmetricDomains.CartanUniqueness

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
open Set Filter Metric
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isolated_fixedPoint_of_neg_id [CompleteSpace E]
    {f : E → E} {p : E} (hf : AnalyticAt ℂ f p) (hp : f p = p)
    (hd : HasFDerivAt f (-1 : E →L[ℂ] E) p) :
    ∀ᶠ x in 𝓝 p, f x = x → x = p := by
  let g : E → E := fun x => (1/2 : ℂ) • (x-f x)
  have hg : AnalyticAt ℂ g p := (analyticAt_id.sub hf).const_smul
  have hgder : HasFDerivAt g (1 : E →L[ℂ] E) p := by
    have hh := ((hasFDerivAt_id p).sub hd).const_smul (1/2 : ℂ)
    convert hh using 1
    · rfl
    · change (1 : E →L[ℂ] E) = (1/2 : ℂ) • (1-(-1))
      module
  have hs : HasStrictFDerivAt g ((ContinuousLinearEquiv.refl ℂ E) : E →L[ℂ] E) p := by
    simpa only [hgder.fderiv,ContinuousLinearEquiv.coe_refl,ContinuousLinearMap.one_def]
      using hg.hasStrictFDerivAt
  have hleft := hs.eventually_left_inverse
  have hp' := hs.localInverse_apply_image
  filter_upwards [hleft] with x hx hfx
  have he : g x = g p := by simp [g,hfx,hp]
  rw [he] at hx
  exact hx.symm.trans hp'

theorem cartan_involution_of_neg_id [ProperSpace E] [SecondCountableTopology E]
    {S : Set E} (hS : IsOpen S) (hconn : IsPreconnected S)
    (hb : Bornology.IsBounded S) {f : E → E}
    (hf : AnalyticOnNhd ℂ f S) (hm : MapsTo f S S)
    {p : E} (hp : p ∈ S) (hfix : f p = p)
    (hd : HasFDerivAt f (-1 : E →L[ℂ] E) p) :
    (∀ x ∈ S, f (f x) = x) ∧ ∀ᶠ x in 𝓝 p, f x = x → x = p := by
  refine ⟨?_,isolated_fixedPoint_of_neg_id (hf p hp) hfix hd⟩
  have hdf : HasFDerivAt f (-1 : E →L[ℂ] E) (f p) := hfix.symm ▸ hd
  have hdd : HasFDerivAt (f ∘ f) (1 : E →L[ℂ] E) p := by
    have hh := hdf.comp p hd
    convert hh using 1
    ext x
    simp
  have hff : (f ∘ f) p = p := by simp [hfix]
  exact cartan_uniqueness_bounded hS hconn hb (hf.comp hf hm) (hm.comp hm) hp hff hdd

end

open Set Filter Metric
open scoped Topology

theorem Biholomorph.pointSymmetry_of_neg_id {n : ℕ} {S : Set (Affine n)}
    (hS : IsOpen S) (hconn : IsPreconnected S) (hb : Bornology.IsBounded S)
    (σ : Biholomorph S S) (p : S) (hfix : σ.toHomeomorph p = p)
    (hd : HasFDerivAt (ambientExtend (fun x => (σ.toHomeomorph x).val))
      (-1 : Affine n →L[ℂ] Affine n) p.val) :
    Function.Involutive σ.toHomeomorph ∧ σ.toHomeomorph p = p ∧
      ∃ W : Set S, IsOpen W ∧ p ∈ W ∧
        ∀ q ∈ W, σ.toHomeomorph q = q → q = p := by
  let f := ambientExtend (fun x => (σ.toHomeomorph x).val)
  have hf : AnalyticOnNhd ℂ f S := σ.holomorphic_toFun.analyticOnNhd_extend hS
  have hm : MapsTo f S S := by
    intro x hx
    rw [show f x = (σ.toHomeomorph ⟨x,hx⟩).val from ambientExtend_apply _ ⟨x,hx⟩]
    exact (σ.toHomeomorph ⟨x,hx⟩).property
  have hfp : f p.val = p.val := by
    rw [show f p.val = (σ.toHomeomorph p).val from ambientExtend_apply _ p,hfix]
  obtain ⟨hi,hiso⟩ := cartan_involution_of_neg_id hS hconn hb hf hm p.property hfp hd
  refine ⟨?_,hfix,?_⟩
  · intro q
    apply Subtype.ext
    have hh := hi q q.property
    rw [show f q.val = (σ.toHomeomorph q).val from ambientExtend_apply _ q] at hh
    rw [show f (σ.toHomeomorph q).val = (σ.toHomeomorph (σ.toHomeomorph q)).val
      from ambientExtend_apply _ _] at hh
    exact hh
  · obtain ⟨r,hr,hWsub⟩ := Metric.mem_nhds_iff.mp hiso
    refine ⟨(Subtype.val : S → Affine n) ⁻¹' ball p.val r,
      isOpen_ball.preimage continuous_subtype_val,mem_ball_self hr,?_⟩
    intro q hq hqfix
    apply Subtype.ext
    apply hWsub hq
    rw [show f q.val = (σ.toHomeomorph q).val from ambientExtend_apply _ q,hqfix]

end Release061

end

end OAI
