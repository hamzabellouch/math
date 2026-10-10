import Mathlib
import OAI.Analysis.SymmetricDomains.ChartJacobianNeZero
import OAI.Analysis.SymmetricDomains.ChartLimitMapsAnchor

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

theorem scaling_biholomorph_embedded_charts {n m : ℕ}
    {S : Set (Affine n)} {O : Set (Affine m)} {y₀ : Affine m}
    (hy₀ : y₀ ∈ O) (hconn : IsPreconnected S) (hO : IsOpen O)
    {T : ℕ → Set (Affine m)}
    {f : ℕ → Affine n → Affine m} {g : ℕ → Affine m → Affine n}
    {F : Affine n → Affine m} {G : Affine m → Affine n}
    (hf : TendstoLocallyUniformlyOn f F atTop S)
    (hg : TendstoLocallyUniformlyOn g G atTop (connectedComponentIn O y₀))
    (hcharts : ∀ p : S, ∃ W : Set (Affine n), W ⊆ S ∧
      IsOpen ((Subtype.val : S → Affine n) ⁻¹' W) ∧ p.val ∈ W ∧
      ∃ D : Set (Affine m), IsOpen D ∧ IsPreconnected D ∧
      ∃ e : Biholomorph W D, ∀ᶠ j in atTop,
        HolomorphicOnSubset W (fun x => f j x) ∧
        ∀ z ∈ D, (fderiv ℂ
          (f j ∘ ambientExtend (fun x => (e.toHomeomorph.symm x).val)) z).det ≠ 0)
    (hGhol : AnalyticOnNhd ℂ G (connectedComponentIn O y₀))
    (hfmap : ∀ K : Set (Affine n), IsCompact K → K ⊆ S →
      ∀ᶠ j in atTop, MapsTo (f j) K (T j))
    (hGmap : MapsTo G (connectedComponentIn O y₀) S)
    (hgmap : ∀ y ∈ connectedComponentIn O y₀, ∀ᶠ j in atTop, g j y ∈ S)
    (hright : ∀ y ∈ connectedComponentIn O y₀, ∀ᶠ j in atTop, f j (g j y) = y)
    (hleft : ∀ x ∈ S, ∀ᶠ j in atTop, g j (f j x) = x)
    (hexcluded : ∀ y ∉ O, ∃ a : ℕ → Affine m,
      Tendsto a atTop (𝓝 y) ∧ ∀ᶠ j in atTop, a j ∉ T j) :
    Nonempty (Biholomorph S (connectedComponentIn O y₀)) := by
  have hD := hO.connectedComponentIn (x := y₀)
  have hFhol : HolomorphicOnSubset S (fun x => F x) := by
    apply holomorphicOnSubset_of_local
    intro p
    obtain ⟨W,hWS,hWo,hpW,D,hDo,_,e,he⟩ := hcharts p
    exact ⟨W,hWS,hWo,hpW,holomorphic_chart_limit hDo e
      (hf.mono hWS) (he.mono fun j hj => hj.1)⟩
  have hFc : ContinuousOn F S := continuousOn_iff_continuous_domRestrict.mpr hFhol.continuous
  have hGc := hGhol.continuousOn
  have hri : ∀ y ∈ connectedComponentIn O y₀, F (G y) = y := by
    intro y hy
    have ht : Tendsto (fun j => g j y) atTop (𝓝[S] G y) :=
      tendsto_nhdsWithin_iff.mpr ⟨hg.tendsto_at hy,hgmap y hy⟩
    exact tendsto_nhds_unique
      (hf.tendsto_comp (hFc _ (hGmap hy)) (hGmap hy) ht)
      (tendsto_const_nhds.congr' ((hright y hy).mono fun j hj => hj.symm))
  have hli : ∀ x ∈ S, F x ∈ connectedComponentIn O y₀ → G (F x) = x := by
    intro x hx hxD
    have ht : Tendsto (fun j => f j x) atTop (𝓝[connectedComponentIn O y₀] F x) :=
      tendsto_nhdsWithin_iff.mpr ⟨hf.tendsto_at hx,(hf.tendsto_at hx) (hD.mem_nhds hxD)⟩
    exact tendsto_nhds_unique (hg.tendsto_comp (hGc _ hxD) hxD ht)
      (tendsto_const_nhds.congr' ((hleft x hx).mono fun j hj => hj.symm))
  let A : Set S := {p | F p.val ∈ connectedComponentIn O y₀}
  have hAo : IsOpen A := hD.preimage hFhol.continuous
  have hAc : IsClosed A := by
    apply closure_subset_iff_isClosed.mp
    intro p hp
    obtain ⟨W,hWS,hWo,hpW,D,hDo,hDc,e,he⟩ := hcharts p
    obtain ⟨q,hqW,hqA⟩ := mem_closure_iff.mp hp _ hWo hpW
    have hFw := hFhol.restrict hWS
    have hanchor := chart_jacobian_ne_zero_of_left_inverse hDo hD e hFw hGhol
      (fun x hx => hli x (hWS hx)) (⟨q.val,hqW⟩ : W) hqA
    have hmap := chart_limit_mapsTo_of_anchor hWS hDo hDc e hf he hfmap hexcluded
      ⟨(e.toHomeomorph ⟨q.val,hqW⟩).val,(e.toHomeomorph ⟨q.val,hqW⟩).property,hanchor⟩
    let E := ambientExtend (fun x : D => (e.toHomeomorph.symm x).val)
    have hEx (x : W) : E (e.toHomeomorph x).val = x.val := by
      dsimp only [E]
      rw [ambientExtend_apply _ (e.toHomeomorph x),e.toHomeomorph.symm_apply_apply]
    have hHa : AnalyticOnNhd ℂ (F ∘ E) D := analytic_comp_chart_inverse hDo e hFw
    have himage : (F ∘ E) '' D ⊆ connectedComponentIn O (F q.val) := by
      apply (hDc.image (F ∘ E) hHa.continuousOn).subset_connectedComponentIn
      · exact ⟨(e.toHomeomorph ⟨q.val,hqW⟩).val,(e.toHomeomorph ⟨q.val,hqW⟩).property,
          congrArg F (hEx ⟨q.val,hqW⟩)⟩
      · rintro y ⟨z,hz,rfl⟩
        have hzE : E z = (e.toHomeomorph.symm ⟨z,hz⟩).val := ambientExtend_apply _ ⟨z,hz⟩
        exact hmap (hzE ▸ (e.toHomeomorph.symm ⟨z,hz⟩).property)
    rw [← connectedComponentIn_eq hqA] at himage
    exact himage ⟨(e.toHomeomorph ⟨p.val,hpW⟩).val,(e.toHomeomorph ⟨p.val,hpW⟩).property,
      congrArg F (hEx ⟨p.val,hpW⟩)⟩
  have hbase : y₀ ∈ connectedComponentIn O y₀ := mem_connectedComponentIn hy₀
  have hAn : A.Nonempty := ⟨⟨G y₀,hGmap hbase⟩,by
    change F (G y₀) ∈ connectedComponentIn O y₀
    rw [hri y₀ hbase]
    exact hbase⟩
  let : PreconnectedSpace S := isPreconnected_iff_preconnectedSpace.mp hconn
  have huniv : A = univ := IsClopen.eq_univ ⟨hAc,hAo⟩ hAn
  have hFm : MapsTo F S (connectedComponentIn O y₀) := by
    intro x hx
    exact show (⟨x,hx⟩ : S) ∈ A from huniv ▸ mem_univ _
  exact ⟨⟨homeomorphOfInverseOn hFc hGc hFm hGmap
    (fun x hx => hli x hx (hFm hx)) hri,hFhol,
    holomorphicOnSubset_of_analyticOnNhd_open hD hGhol⟩⟩

end Release061

end

end OAI
