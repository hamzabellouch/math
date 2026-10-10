import Mathlib
import OAI.Analysis.SymmetricDomains.ScalingOpenDomain

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
namespace Release061
open Set Filter Metric
open scoped Topology

noncomputable def ambientExtend {n m : ℕ} {S : Set (Affine n)}
    (f : S → Affine m) (x : Affine n) : Affine m := by
  classical
  exact if hx : x ∈ S then f ⟨x,hx⟩ else 0

lemma ambientExtend_apply {n m : ℕ} {S : Set (Affine n)}
    (f : S → Affine m) (x : S) : ambientExtend f x = f x := by
  classical
  simp only [ambientExtend,dite_eq_left x.property]

lemma continuousOn_ambientExtend {n m : ℕ} {S : Set (Affine n)}
    {f : S → Affine m} (hf : Continuous f) : ContinuousOn (ambientExtend f) S := by
  rw [continuousOn_iff_continuous_domRestrict]
  have he : S.domRestrict (ambientExtend f) = f := funext (ambientExtend_apply f)
  rwa [he]

theorem HolomorphicOnSubset.analyticOnNhd_extend {n m : ℕ} {S : Set (Affine n)}
    (hS : IsOpen S) {f : S → Affine m} (hf : HolomorphicOnSubset S f) :
    AnalyticOnNhd ℂ (ambientExtend f) S := by
  intro x hx
  obtain ⟨W,hW,hxW,F,hF,he⟩ := hf ⟨x,hx⟩
  apply (hF x hxW).congr
  filter_upwards [hW.mem_nhds hxW, hS.mem_nhds hx] with y hyW hyS
  rw [show ambientExtend f y = f ⟨y,hyS⟩ from ambientExtend_apply f ⟨y,hyS⟩]
  exact he ⟨y,hyS⟩ hyW

theorem holomorphicOnSubset_of_local {n m : ℕ} {S : Set (Affine n)}
    {f : S → Affine m}
    (hf : ∀ p : S, ∃ (W : Set (Affine n)) (hWS : W ⊆ S),
      IsOpen ((Subtype.val : S → Affine n) ⁻¹' W) ∧ p.val ∈ W ∧
      HolomorphicOnSubset W (fun x => f ⟨x.val,hWS x.property⟩)) :
    HolomorphicOnSubset S f := by
  intro p
  obtain ⟨W,hWS,hW,hpW,hh⟩ := hf p
  obtain ⟨O,hO,heO⟩ := isOpen_induced_iff.mp hW
  have hpO : p.val ∈ O := by change p ∈ (Subtype.val : S → Affine n) ⁻¹' O; rw [heO]; exact hpW
  obtain ⟨V,hV,hpV,F,hF,he⟩ := hh ⟨p.val,hpW⟩
  refine ⟨V ∩ O,hV.inter hO,⟨hpV,hpO⟩,F,hF.mono inter_subset_left,?_⟩
  intro q hq
  have hqW : q.val ∈ W := by
    change q ∈ (Subtype.val : S → Affine n) ⁻¹' W
    rw [← heO]
    exact hq.2
  exact he ⟨q.val,hqW⟩ hq.1

theorem holomorphic_chart_limit {n d m : ℕ} {W : Set (Affine n)}
    {D : Set (Affine d)} (hD : IsOpen D) (e : Biholomorph W D)
    {f : ℕ → Affine n → Affine m} {F : Affine n → Affine m}
    (hconv : TendstoLocallyUniformlyOn f F atTop W)
    (hhol : ∀ᶠ j in atTop, HolomorphicOnSubset W (fun x => f j x)) :
    HolomorphicOnSubset W (fun x => F x) := by
  let g : Affine d → Affine n := ambientExtend (fun x => (e.toHomeomorph.symm x).val)
  have hg : ∀ x : D, g x = (e.toHomeomorph.symm x).val :=
    ambientExtend_apply _
  have hgc : ContinuousOn g D := continuousOn_ambientExtend
    (continuous_subtype_val.comp e.toHomeomorph.symm.continuous)
  have hgm : MapsTo g D W := by
    intro y hy
    rw [hg ⟨y,hy⟩]
    exact (e.toHomeomorph.symm ⟨y,hy⟩).property
  have hc := hconv.comp g hgm hgc
  have hjhol : ∀ᶠ j in atTop, AnalyticOnNhd ℂ (f j ∘ g) D := by
    filter_upwards [hhol] with j hj
    have hh := (hj.comp e.holomorphic_invFun).analyticOnNhd_extend hD
    intro x hx
    apply (hh x hx).congr
    filter_upwards [hD.mem_nhds hx] with y hy
    simp only [Function.comp_def]
    rw [hg ⟨y,hy⟩]
    exact ambientExtend_apply _ ⟨y,hy⟩
  have hFd := differentiableOn_of_locally_uniform_limit hD hc
    (fun x hx => ⟨D,hD.mem_nhds hx,hjhol.mono fun _ h => h.differentiableOn⟩)
  have hFa := analyticOnNhd_of_differentiableOn_affine hD hFd
  have hlocal : HolomorphicOnSubset D (fun x => F (g x)) :=
    holomorphicOnSubset_of_analyticOnNhd_open hD hFa
  have hcomp := hlocal.comp e.holomorphic_toFun
  convert hcomp using 1
  funext x
  dsimp only [Function.comp_def]
  rw [hg (e.toHomeomorph x),e.toHomeomorph.symm_apply_apply]

theorem IsSmooth.holomorphic_locally_uniform_limit {n m : ℕ} {S : Set (Affine n)}
    (hS : IsSmooth S) {f : ℕ → Affine n → Affine m} {F : Affine n → Affine m}
    (hconv : TendstoLocallyUniformlyOn f F atTop S)
    (hhol : ∀ p : S, ∃ V : Set (Affine n), V ⊆ S ∧
      IsOpen ((Subtype.val : S → Affine n) ⁻¹' V) ∧ p.val ∈ V ∧
      ∀ᶠ j in atTop, HolomorphicOnSubset V (fun x => f j x)) :
    HolomorphicOnSubset S (fun x => F x) := by
  apply holomorphicOnSubset_of_local
  intro p
  obtain ⟨V,hVS,hVo,hpV,hVhol⟩ := hhol p
  have hsm : SmoothAtSubset V p.val :=
    smoothAtSubset_restrict_open hVS hVo hpV (hS p)
  obtain ⟨d,W,hWV,hWo,hpW,D,hD,⟨e⟩⟩ := hsm
  refine ⟨W,hWV.trans hVS,relative_open_trans hVS hWV hVo hWo,hpW,?_⟩
  exact holomorphic_chart_limit hD e (hconv.mono (hWV.trans hVS))
    (hVhol.mono fun _ hj => hj.restrict hWV)

end Release061

end

end OAI
