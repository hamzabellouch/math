import Mathlib
import OAI.Analysis.SymmetricDomains.CompactPeakRatio

namespace OAI

open Set Metric Complex
open scoped Topology
namespace Release061
open Set Filter Metric
open scoped Topology

theorem mapsTo_of_stable_balls_and_excluded_points
    {X Y : Type*} [PseudoMetricSpace Y] {S : Set X} {O : Set Y}
    {T : ℕ → Set Y} {f : X → Y}
    (hstable : ∀ x ∈ S, ∃ r > 0, ∀ᶠ j in atTop, ball (f x) r ⊆ T j)
    (hexcluded : ∀ y ∉ O, ∃ a : ℕ → Y,
      Tendsto a atTop (𝓝 y) ∧ ∀ᶠ j in atTop, a j ∉ T j) : MapsTo f S O := by
  intro x hx
  by_contra hout
  obtain ⟨r,hr,hball⟩ := hstable x hx
  obtain ⟨a,ha,houta⟩ := hexcluded (f x) hout
  have hnear : ∀ᶠ j in atTop, a j ∈ ball (f x) r := ha (ball_mem_nhds _ hr)
  have hfalse : ∀ᶠ j : ℕ in atTop, False := by
    filter_upwards [hball,houta,hnear] with j hj ho hn
    exact ho (hj hn)
  exact (Filter.Eventually.exists hfalse).choose_spec

theorem inverse_limit_component
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {S : Set X} {O : Set Y} {y₀ : Y} (hy₀ : y₀ ∈ O)
    (hS : IsPreconnected S) (hD : IsOpen (connectedComponentIn O y₀))
    {f : ℕ → X → Y} {g : ℕ → Y → X} {F : X → Y} {G : Y → X}
    (hf : TendstoLocallyUniformlyOn f F atTop S)
    (hg : TendstoLocallyUniformlyOn g G atTop (connectedComponentIn O y₀))
    (hF : ContinuousOn F S) (hG : ContinuousOn G (connectedComponentIn O y₀))
    (hGmap : MapsTo G (connectedComponentIn O y₀) S)
    (hgmap : ∀ y ∈ connectedComponentIn O y₀, ∀ᶠ j in atTop, g j y ∈ S)
    (hright : ∀ y ∈ connectedComponentIn O y₀, ∀ᶠ j in atTop, f j (g j y) = y)
    (hleft : ∀ x ∈ S, ∀ᶠ j in atTop, g j (f j x) = x)
    (hFmap : MapsTo F S O) :
    MapsTo F S (connectedComponentIn O y₀) ∧
      (∀ y ∈ connectedComponentIn O y₀, F (G y) = y) ∧
      (∀ x ∈ S, G (F x) = x) := by
  have hright' : ∀ y ∈ connectedComponentIn O y₀, F (G y) = y := by
    intro y hy
    have ht : Tendsto (fun j => g j y) atTop (𝓝[S] G y) :=
      tendsto_nhdsWithin_iff.mpr ⟨hg.tendsto_at hy,hgmap y hy⟩
    have hcomp := hf.tendsto_comp (hF (G y) (hGmap hy)) (hGmap hy) ht
    exact tendsto_nhds_unique hcomp (tendsto_const_nhds.congr' ((hright y hy).mono (fun _ h => h.symm)))
  have hbase : y₀ ∈ connectedComponentIn O y₀ := mem_connectedComponentIn hy₀
  have himage : F '' S ⊆ connectedComponentIn O y₀ := by
    apply (hS.image F hF).subset_connectedComponentIn
      ⟨G y₀,hGmap hbase,hright' y₀ hbase⟩
    exact fun y hy => by obtain ⟨x,hx,rfl⟩ := hy; exact hFmap hx
  have hmaps : MapsTo F S (connectedComponentIn O y₀) := fun x hx => himage ⟨x,hx,rfl⟩
  refine ⟨hmaps,hright',?_⟩
  intro x hx
  have ht : Tendsto (fun j => f j x) atTop (𝓝[connectedComponentIn O y₀] F x) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨hf.tendsto_at hx,(hf.tendsto_at hx) (hD.mem_nhds (hmaps hx))⟩
  have hcomp := hg.tendsto_comp (hG (F x) (hmaps hx)) (hmaps hx) ht
  exact tendsto_nhds_unique hcomp (tendsto_const_nhds.congr' ((hleft x hx).mono (fun _ h => h.symm)))

noncomputable def homeomorphOfInverseOn
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {S : Set X} {T : Set Y} {F : X → Y} {G : Y → X}
    (hF : ContinuousOn F S) (hG : ContinuousOn G T)
    (hFm : MapsTo F S T) (hGm : MapsTo G T S)
    (hleft : ∀ x ∈ S, G (F x) = x) (hright : ∀ y ∈ T, F (G y) = y) : S ≃ₜ T where
  toFun x := ⟨F x,hFm x.property⟩
  invFun y := ⟨G y,hGm y.property⟩
  left_inv x := Subtype.ext (hleft x x.property)
  right_inv y := Subtype.ext (hright y y.property)
  continuous_toFun := (continuousOn_iff_continuous_domRestrict.mp hF).subtype_mk _
  continuous_invFun := (continuousOn_iff_continuous_domRestrict.mp hG).subtype_mk _

end Release061



end OAI
