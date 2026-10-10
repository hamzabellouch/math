import Mathlib
import OAI.Analysis.SymmetricDomains.HolomorphicLocallyUniformLimit
import OAI.Analysis.SymmetricDomains.FiniteNashCoverVertical

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
open Set Filter Topology
open scoped Classical

theorem Biholomorph.centered_chart_germs {n m : ℕ} {V W : Set (Affine n)}
    {B : Set (Affine m)} (e : Biholomorph W B) (hWV : W ⊆ V)
    (hW : IsOpen ((Subtype.val : V → Affine n) ⁻¹' W)) (hB : IsOpen B)
    {q : Affine n} (hq : q ∈ W) :
    ∃ (F : Affine m → Affine n) (G : Affine n → Affine m),
      F 0 = q ∧ AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ G q ∧
      (G ∘ F) =ᶠ[𝓝 (0 : Affine m)] id ∧
      (∀ᶠ y in 𝓝[V] q, F (G y) = y) ∧
      (∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ V) := by
  let b : Affine m := (e.toHomeomorph ⟨q,hq⟩).val
  have hb : b ∈ B := (e.toHomeomorph ⟨q,hq⟩).property
  let f := ambientExtend (fun y : B => (e.toHomeomorph.symm y).val)
  have hf : AnalyticOnNhd ℂ f B := e.holomorphic_invFun.analyticOnNhd_extend hB
  have hfb : f b = q := by
    rw [show f b = (e.toHomeomorph.symm (e.toHomeomorph ⟨q,hq⟩)).val from ambientExtend_apply _ _]
    simp
  obtain ⟨O,hO,hqO,g,hg,hge⟩ := e.holomorphic_toFun ⟨q,hq⟩
  let F : Affine m → Affine n := fun z => f (z+b)
  let G : Affine n → Affine m := fun y => g y-b
  have hF0 : F 0 = q := by simpa only [F,zero_add] using hfb
  have hF : AnalyticAt ℂ F 0 := by
    have htr : AnalyticAt ℂ (fun z : Affine m => z+b) 0 := analyticAt_id.add analyticAt_const
    have hf' : AnalyticAt ℂ f (0+b) := by simpa only [zero_add] using hf b hb
    exact hf'.comp (f := fun z : Affine m => z+b) (x := 0) htr
  have hG : AnalyticAt ℂ G q := (hg q hqO).sub analyticAt_const
  refine ⟨F,G,hF0,hF,hG,?_,?_,?_⟩
  · have hzB : ∀ᶠ z in 𝓝 (0 : Affine m), z+b ∈ B :=
      ((continuous_id.add continuous_const).continuousAt (x := (0 : Affine m))).preimage_mem_nhds
        (by simpa using hB.mem_nhds hb)
    have hzO : ∀ᶠ z in 𝓝 (0 : Affine m), F z ∈ O :=
      hF.continuousAt.preimage_mem_nhds (by simpa only [hF0] using hO.mem_nhds hqO)
    filter_upwards [hzB,hzO] with z hz hz'
    have hfy : f (z+b) = (e.toHomeomorph.symm ⟨z+b,hz⟩).val := ambientExtend_apply (fun y : B => (e.toHomeomorph.symm y).val) ⟨z+b,hz⟩
    have hfw : F z ∈ W := by rw [show F z = f (z+b) from rfl,hfy]; exact (e.toHomeomorph.symm ⟨z+b,hz⟩).property
    have he : g (F z) = z+b := by
      rw [hge ⟨F z,hfw⟩ hz']
      have heq : (⟨F z,hfw⟩ : W) = e.toHomeomorph.symm ⟨z+b,hz⟩ := Subtype.ext hfy
      rw [heq]
      exact congrArg Subtype.val (e.toHomeomorph.apply_symm_apply ⟨z+b,hz⟩)
    change g (F z)-b = z
    rw [he,add_sub_cancel_right]
  · obtain ⟨O',hO',hWO'⟩ := isOpen_induced_iff.mp hW
    have hqO' : q ∈ O' := by
      have hh : (⟨q,hWV hq⟩ : V) ∈ (Subtype.val : V → Affine n) ⁻¹' W := hq
      rwa [← hWO'] at hh
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hO'.mem_nhds hqO'),
      mem_nhdsWithin_of_mem_nhds (hO.mem_nhds hqO)] with y hyV hyO' hyO
    have hyW : y ∈ W := by
      have hh : (⟨y,hyV⟩ : V) ∈ (Subtype.val : V → Affine n) ⁻¹' O' := hyO'
      rwa [hWO'] at hh
    have hgy := hge ⟨y,hyW⟩ hyO
    change f (g y-b+b) = y
    rw [sub_add_cancel,hgy]
    rw [show f (e.toHomeomorph ⟨y,hyW⟩).val =
      (e.toHomeomorph.symm (e.toHomeomorph ⟨y,hyW⟩)).val from ambientExtend_apply _ _]
    simp
  · have hzB : ∀ᶠ z in 𝓝 (0 : Affine m), z+b ∈ B :=
      ((continuous_id.add continuous_const).continuousAt (x := (0 : Affine m))).preimage_mem_nhds
        (by simpa using hB.mem_nhds hb)
    filter_upwards [hzB] with z hz
    change f (z+b) ∈ V
    rw [show f (z+b) = (e.toHomeomorph.symm ⟨z+b,hz⟩).val from ambientExtend_apply (fun y : B => (e.toHomeomorph.symm y).val) ⟨z+b,hz⟩]
    exact hWV (e.toHomeomorph.symm ⟨z+b,hz⟩).property

end Release061

end

end OAI
