import Mathlib
import OAI.Geometry.SplitTangent.TensorVanishing
import OAI.Geometry.SplitTangent.Basic

namespace OAI

/-! Holomorphic Manifold Product. -/

noncomputable section
open Set Filter Topology Bundle
open scoped Manifold ContDiff
universe u
namespace SplitTangent
variable {X : ComplexManifold.{u}}
namespace TangentSplitting
variable (S : TangentSplitting X)

lemma coordinateProjector_range (x : X.Carrier) {y : X.Carrier}
    (hy : y∈(chartAt (Model X) x).source) :
    Submodule.map (chartDerivative x y).toLinearMap (S.first y)=
      LinearMap.range (S.coordinateProjector x ((chartAt (Model X) x) y)).toLinearMap := by
  have hD := chartDerivative_isInvertible x hy
  ext v
  rw [S.coordinateProjector_range_iff x hy]
  constructor
  · rintro ⟨w,hw,rfl⟩
    change (chartDerivative x y).inverse ((chartDerivative x y) w) ∈ S.first y
    rw [hD.inverse_apply_self]
    exact hw
  · intro hv
    exact ⟨(chartDerivative x y).inverse v,hv,hD.self_apply_inverse v⟩

lemma coordinateProjector_kernel (x : X.Carrier) {y : X.Carrier}
    (hy : y∈(chartAt (Model X) x).source) :
    Submodule.map (chartDerivative x y).toLinearMap (S.second y)=
      LinearMap.ker (S.coordinateProjector x ((chartAt (Model X) x) y)).toLinearMap := by
  rw [← S.swap_first,S.swap.coordinateProjector_range x hy,
    S.coordinateProjector_swap x ((chartAt (Model X) x).map_source hy)]
  exact HolomorphicFrobenius.range_complementary_projector _
    (S.coordinateProjector_idempotent x ((chartAt (Model X) x).map_source hy))

abbrev FirstModel (x : X.Carrier) :=
  HolomorphicFrobenius.FirstQuotient (S.coordinateProjector x) ((chartAt (Model X) x) x)
abbrev SecondModel (x : X.Carrier) :=
  HolomorphicFrobenius.SecondQuotient (S.coordinateProjector x) ((chartAt (Model X) x) x)

 

theorem exists_local_product_chart (hI₁ : Integrable X S.first)
    (hI₂ : Integrable X S.second) (x : X.Carrier) :
    ∃ Φ : OpenPartialHomeomorph X.Carrier (S.FirstModel x × S.SecondModel x),
      x∈Φ.source ∧ Φ x=0 ∧
      ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,S.FirstModel x × S.SecondModel x) ω Φ x ∧
      ContMDiffAt 𝓘(ℂ,S.FirstModel x × S.SecondModel x) (ModelWithCorners X) ω Φ.symm 0 ∧
      ∀ᶠ y in 𝓝 x,
        Submodule.map (mfderiv (ModelWithCorners X) 𝓘(ℂ,S.FirstModel x × S.SecondModel x)
          Φ y).toLinearMap (S.first y)=
          LinearMap.ker (ContinuousLinearMap.snd ℂ (S.FirstModel x) (S.SecondModel x)).toLinearMap ∧
        Submodule.map (mfderiv (ModelWithCorners X) 𝓘(ℂ,S.FirstModel x × S.SecondModel x)
          Φ y).toLinearMap (S.second y)=
          LinearMap.ker (ContinuousLinearMap.fst ℂ (S.FirstModel x) (S.SecondModel x)).toLinearMap := by
  let c := chartAt (Model X) x
  let z := c x
  have hx : x∈c.source := mem_chart_source (Model X) x
  have hz : z∈c.target := c.map_source hx
  have hP := S.coordinateProjector_analytic x z hz
  have hPid : ∀ᶠ a in 𝓝 z, ∀v, S.coordinateProjector x a (S.coordinateProjector x a v)=
      S.coordinateProjector x a v :=
    Filter.Eventually.mono (c.open_target.mem_nhds hz) fun a ha => S.coordinateProjector_idempotent x ha
  have hPcomp : S.swap.coordinateProjector x=ᶠ[𝓝 z]
      (fun a => ContinuousLinearMap.id ℂ (Model X)-S.coordinateProjector x a) :=
    Filter.Eventually.mono (c.open_target.mem_nhds hz) fun a ha => S.coordinateProjector_swap x ha
  have hIc := (S.swap.coordinateProjector_involutive (by simpa using hI₂) x hz).congr hPcomp
  obtain ⟨ψ,hzψ,hψ0,hψ,hψs,haxes⟩ := HolomorphicFrobenius.exists_local_product_chart
    hP hPid (S.coordinateProjector_involutive hI₁ x hz) hIc
  let Φ := c.trans ψ
  have hΦx : Φ x=0 := hψ0
  have hc : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,Model X) ω c x :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X)
      (n := ω) x) hx
  have h0t : (0 : S.FirstModel x × S.SecondModel x)∈ψ.target := hψ0 ▸ ψ.map_source hzψ
  have hψs0 : ψ.symm 0=z := by simpa only [hψ0] using ψ.left_inv hzψ
  have hcs : ContMDiffAt 𝓘(ℂ,Model X) (ModelWithCorners X) ω c.symm (ψ.symm 0) := by
    rw [hψs0]
    exact contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X) (n := ω) x) hz
  refine ⟨Φ,⟨hx,hzψ⟩,hΦx,hψ.contDiffAt.contMDiffAt.comp x hc,
    hcs.comp 0 hψs.contDiffAt.contMDiffAt,?_⟩
  have ht : Tendsto c (𝓝 x) (𝓝 z) := hc.continuousAt
  filter_upwards [c.open_source.mem_nhds hx,ht.eventually haxes,
    ht.eventually hψ.eventually_analyticAt] with y hy hay hψy
  have hcy : ContMDiffAt (ModelWithCorners X) 𝓘(ℂ,Model X) ω c y :=
    contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (I := ModelWithCorners X)
      (n := ω) x) hy
  have hd : mfderiv (ModelWithCorners X) 𝓘(ℂ,S.FirstModel x × S.SecondModel x) Φ y=
      (fderiv ℂ ψ (c y)).comp (chartDerivative x y) := by
    change mfderiv (ModelWithCorners X) 𝓘(ℂ,S.FirstModel x × S.SecondModel x) (ψ ∘ c) y=_
    rw [mfderiv_comp y (hψy.differentiableAt.mdifferentiableAt)
      (hcy.mdifferentiableAt (by simp)),mfderiv_eq_fderiv]
    rfl
  constructor
  · rw [hd]
    change Submodule.map ((fderiv ℂ ψ (c y)).toLinearMap.comp
      (chartDerivative x y).toLinearMap) (S.first y)=_
    rw [Submodule.map_comp,S.coordinateProjector_range x hy]
    exact hay.1
  · rw [hd]
    change Submodule.map ((fderiv ℂ ψ (c y)).toLinearMap.comp
      (chartDerivative x y).toLinearMap) (S.second y)=_
    rw [Submodule.map_comp,S.coordinateProjector_kernel x hy]
    exact hay.2

end TangentSplitting
end SplitTangent

namespace SplitTangent
variable {X : ComplexManifold.{u}} {S : TangentSplitting X}

theorem TangentSplitting.exists_aligned_product_chart (S : TangentSplitting X)
    (hI₁ : Integrable X S.first) (hI₂ : Integrable X S.second) (x : X.Carrier) :
    ∃P : AlignedProductChart S (S.FirstModel x) (S.SecondModel x),
      x∈P.chart.source ∧ P.chart x=0 := by
  obtain ⟨φ,hx,h0,hφ,hφs,haxes⟩ := S.exists_local_product_chart hI₁ hI₂ x
  have hs : ContMDiffAt 𝓘(ℂ,S.FirstModel x × S.SecondModel x) (ModelWithCorners X) ω φ.symm (φ x) :=
    h0.symm ▸ hφs
  have hall := ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hφ).and
    ((hφ.continuousAt.eventually ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hs)).and haxes)
  obtain ⟨U,hUsub,hU,hxU⟩ := mem_nhds_iff.mp hall
  let ψ := φ.restrOpen U hU
  let P : AlignedProductChart S (S.FirstModel x) (S.SecondModel x) := {
    chart := ψ
    holomorphic := by
      intro y hy
      exact (hUsub hy.2).1.contMDiffWithinAt
    inverse_holomorphic := by
      intro y hy
      have hz : φ.symm y∈ψ.source := ψ.map_target hy
      have hh := (hUsub hz.2).2.1
      change ContMDiffWithinAt 𝓘(ℂ,S.FirstModel x × S.SecondModel x) (ModelWithCorners X)
        ω φ.symm ψ.target y
      simpa only [φ.right_inv hy.1] using hh.contMDiffWithinAt
    first := fun y hy => (hUsub hy.2).2.2.1
    second := fun y hy => (hUsub hy.2).2.2.2 }
  exact ⟨P,⟨hx,hxU⟩,h0⟩

theorem TangentSplitting.exists_aligned_product_chartAlternative (S : TangentSplitting X)
    (hI₁ : Integrable X S.first) (hI₂ : Integrable X S.second) (x : X.Carrier) :
    ∃P : AlignedProductChart S (S.FirstModel x) (S.SecondModel x),
      x∈P.chart.source ∧ P.chart x=0 := by
  obtain ⟨φ,hx,h0,hφ,hφs,haxes⟩ := S.exists_local_product_chart hI₁ hI₂ x
  have hs : ContMDiffAt 𝓘(ℂ,S.FirstModel x × S.SecondModel x) (ModelWithCorners X) ω φ.symm (φ x) :=
    h0.symm ▸ hφs
  have hall := ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hφ).and
    ((hφ.continuousAt.eventually ((contMDiffAt_iff_contMDiffAt_nhds (by simp)).mp hs)).and haxes)
  obtain ⟨U,hUsub,hU,hxU⟩ := _root_.mem_nhds_iff.mp hall
  let ψ := φ.restrOpen U hU
  let P : AlignedProductChart S (S.FirstModel x) (S.SecondModel x) := {
    chart := ψ
    holomorphic := by
      intro y hy
      exact (hUsub hy.2).1.contMDiffWithinAt
    inverse_holomorphic := by
      intro y hy
      have hz : φ.symm y∈ψ.source := ψ.map_target hy
      have hh := (hUsub hz.2).2.1
      change ContMDiffWithinAt 𝓘(ℂ,S.FirstModel x × S.SecondModel x) (ModelWithCorners X)
        ω φ.symm ψ.target y
      simpa only [φ.right_inv hy.1] using hh.contMDiffWithinAt
    first := fun y hy => (hUsub hy.2).2.2.1
    second := fun y hy => (hUsub hy.2).2.2.2 }
  exact ⟨P,⟨hx,hxU⟩,h0⟩

end SplitTangent

end

end OAI
