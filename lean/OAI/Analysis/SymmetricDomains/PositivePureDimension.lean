import Mathlib
import OAI.Analysis.SymmetricDomains.OpenDimension

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
open Set Filter
open scoped Topology

theorem Biholomorph.open_restriction {n m : ℕ} {S S' : Set (Affine n)}
    {T : Set (Affine m)} (e : Biholomorph S T) (hT : IsOpen T)
    (hSS : S' ⊆ S) (hS : IsOpen ((Subtype.val : S → Affine n) ⁻¹' S')) :
    ∃ T' : Set (Affine m), T' ⊆ T ∧ IsOpen T' ∧ Nonempty (Biholomorph S' T') := by
  let Z : Set S := Subtype.val ⁻¹' S'
  let T' := (Subtype.val : T → Affine m) '' (e.toHomeomorph '' Z)
  have hT'T : T' ⊆ T := by rintro y ⟨z,_,rfl⟩; exact z.property
  have hT'o : IsOpen T' := hT.isOpenMap_subtype_val _ (e.toHomeomorph.isOpenMap _ hS)
  have he : ∀ x : S, x.val ∈ S' ↔ (e.toHomeomorph x).val ∈ T' := by
    intro x
    constructor
    · intro hx
      exact ⟨e.toHomeomorph x,⟨x,hx,rfl⟩,rfl⟩
    · rintro ⟨y,⟨z,hz,hzy⟩,hy⟩
      have hzx : z = x := e.toHomeomorph.injective (hzy.trans (Subtype.ext hy))
      exact hzx ▸ hz
  exact ⟨T',hT'T,hT'o,⟨e.restrict hSS hT'T he⟩⟩

theorem chart_dimension_unique {N n m : ℕ} {S W V : Set (Affine N)}
    (hWS : W ⊆ S) (hVS : V ⊆ S)
    (hW : IsOpen ((Subtype.val : S → Affine N) ⁻¹' W))
    (hV : IsOpen ((Subtype.val : S → Affine N) ⁻¹' V))
    {p : Affine N} (hpW : p ∈ W) (hpV : p ∈ V)
    {D : Set (Affine n)} {E : Set (Affine m)} (hD : IsOpen D) (hE : IsOpen E)
    (e : Biholomorph W D) (f : Biholomorph V E) : n = m := by
  have hWo : IsOpen ((Subtype.val : W → Affine N) ⁻¹' (W ∩ V)) := by
    convert hV.preimage (continuous_inclusion hWS) using 1
    ext x
    simp only [mem_preimage,mem_inter_iff,x.property,true_and,Set.inclusion]
  have hVo : IsOpen ((Subtype.val : V → Affine N) ⁻¹' (W ∩ V)) := by
    convert hW.preimage (continuous_inclusion hVS) using 1
    ext x
    simp only [mem_preimage,mem_inter_iff,x.property,and_true,Set.inclusion]
  obtain ⟨D',_,hD',⟨e'⟩⟩ := e.open_restriction hD inter_subset_left hWo
  obtain ⟨E',_,hE',⟨f'⟩⟩ := f.open_restriction hE inter_subset_right hVo
  apply (e'.symm.trans f').open_dimension_eq hD' hE'
  exact ⟨(e'.toHomeomorph ⟨p,hpW,hpV⟩).val,(e'.toHomeomorph ⟨p,hpW,hpV⟩).property⟩

theorem IsSmooth.pure_dimension {N : ℕ} {S : Set (Affine N)}
    (hs : IsSmooth S) (hc : IsConnected S) :
    ∃ d : ℕ, ∀ p : S, ∃ W : Set (Affine N), W ⊆ S ∧
      IsOpen ((Subtype.val : S → Affine N) ⁻¹' W) ∧ p.val ∈ W ∧
      ∃ D : Set (Affine d), IsOpen D ∧ Nonempty (Biholomorph W D) := by
  classical
  choose d W hWS hWo hpW D hDo he using hs
  let e : ∀ p : S, Biholomorph (W p) (D p) := fun p => Classical.choice (he p)
  have hd : IsLocallyConstant d := by
    apply (IsLocallyConstant.iff_eventually_eq d).mpr
    intro p
    filter_upwards [(hWo p).mem_nhds (hpW p)] with q hq
    exact chart_dimension_unique (hWS q) (hWS p) (hWo q) (hWo p)
      (hpW q) hq (hDo q) (hDo p) (e q) (e p)
  let : PreconnectedSpace S := Subtype.preconnectedSpace hc.isPreconnected
  obtain ⟨a,ha⟩ := hc.nonempty
  refine ⟨d ⟨a,ha⟩,?_⟩
  intro p
  rw [← hd.apply_eq_of_preconnectedSpace p ⟨a,ha⟩]
  exact ⟨W p,hWS p,hWo p,hpW p,D p,hDo p,he p⟩

theorem IsSmooth.subsingleton_of_zero_chart {N : ℕ} {S W : Set (Affine N)}
    (hs : IsSmooth S) (hc : IsPreconnected S) (hWS : W ⊆ S)
    (hW : IsOpen ((Subtype.val : S → Affine N) ⁻¹' W)) (hWn : W.Nonempty)
    {D : Set (Affine 0)} (e : Biholomorph W D) : S.Subsingleton := by
  obtain ⟨p,hp⟩ := hWn
  have hsub : Subsingleton W :=
    Function.Injective.subsingleton e.toHomeomorph.injective
  let f : S → Affine N := fun q => q.val-p
  have hf : HolomorphicOnSubset S f := by
    intro q
    exact ⟨univ,isOpen_univ,mem_univ _,fun x => x-p,
      analyticOnNhd_id.sub analyticOnNhd_const,fun _ _ => rfl⟩
  have hz : f =ᶠ[𝓝 (⟨p,hWS hp⟩ : S)] 0 := by
    filter_upwards [hW.mem_nhds hp] with q hq
    have he : (⟨q.val,hq⟩ : W) = ⟨p,hp⟩ := hsub.elim _ _
    change q.val-p = 0
    rw [congrArg Subtype.val he,sub_self]
  have hh := hs.identity_principle hc hf hz
  intro x hx y hy
  have hx' : x=p := sub_eq_zero.mp (hh ⟨x,hx⟩)
  have hy' : y=p := sub_eq_zero.mp (hh ⟨y,hy⟩)
  exact hx'.trans hy'.symm

theorem IsSmooth.positive_pure_dimension {N : ℕ} {S : Set (Affine N)}
    (hs : IsSmooth S) (hc : IsConnected S) (hn : ¬ S.Subsingleton) :
    ∃ d : ℕ, 0 < d ∧ ∀ p : S, ∃ W : Set (Affine N), W ⊆ S ∧
      IsOpen ((Subtype.val : S → Affine N) ⁻¹' W) ∧ p.val ∈ W ∧
      ∃ D : Set (Affine d), IsOpen D ∧ Nonempty (Biholomorph W D) := by
  obtain ⟨d,hd⟩ := hs.pure_dimension hc
  refine ⟨d,?_,hd⟩
  by_contra! hd0
  have he : d=0 := Nat.eq_zero_of_le_zero hd0
  subst d
  obtain ⟨p,hp⟩ := hc.nonempty
  obtain ⟨W,hWS,hWo,hpW,D,_,⟨e⟩⟩ := hd ⟨p,hp⟩
  exact hn (hs.subsingleton_of_zero_chart hc.isPreconnected hWS hWo ⟨p,hpW⟩ e)

end Release061

end

end OAI
