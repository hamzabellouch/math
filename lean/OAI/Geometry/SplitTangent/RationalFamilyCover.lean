import Mathlib
import OAI.Geometry.SplitTangent.RationalFamilies
import OAI.Geometry.SplitTangent.Basic
import OAI.Geometry.SplitTangent.RationalAccepted
import OAI.Geometry.SplitTangent.RationalEncoding
import OAI.Geometry.SplitTangent.RationalReparam
import OAI.Geometry.SplitTangent.ZariskiPairOpen

namespace OAI

/-! Rational Family Cover. -/

noncomputable section
open Set Filter Topology
open scoped ContDiff Manifold
universe u
namespace SplitTangent
open AnalyticZeroCover RationalParameters

lemma RationallyConnected.fixed_endpoints {X : ComplexManifold.{u}}
    {U : Set (X.Carrier × X.Carrier)}
    (hU : ∀xy∈U,∃g : RationalCurve X, ∃a b : OnePoint ℂ, g.value a=xy.1 ∧ g.value b=xy.2)
    {xy : X.Carrier × X.Carrier} (hxy : xy∈U) :
    ∃g : RationalCurve X, g.finite 0=xy.1 ∧ g.finite 1=xy.2 := by
  classical
  obtain ⟨g,a,b,ha,hb⟩ := hU xy hxy
  by_cases hab : a=b
  · have he : xy.1=xy.2 := ha.symm.trans (hab ▸ hb)
    exact ⟨⟨fun _ => xy.1,fun _ => xy.1,contMDiff_const,contMDiff_const,fun _ _ => rfl⟩,rfl,he⟩
  · obtain ⟨h,h0,h1⟩ := g.normalize_endpoints a b hab
    exact ⟨h,h0.trans ha,h1.trans hb⟩

 

theorem RationallyConnected.countable_family_cover {X : ComplexManifold.{u}}
    [CompactSpace X.Carrier] (e : ProjectiveEmbedding X) (hRC : RationallyConnected e)
    (x₀ : X.Carrier) :
    ∃C : (d : ℕ) → Set (Patch (Coeff e.N d)),
      (∀d,(C d).Countable) ∧
      (∀d, ∀P∈C d,P.image ⊆ regular e.N d ∩ accepted e d) ∧
      ∃U : Set (X.Carrier × X.Carrier), IsOpen U ∧ U.Nonempty ∧
        U ⊆ ⋃ d, ⋃P∈C d, pairEvaluation e x₀ P '' P.domain := by
  classical
  obtain ⟨U,hUz,hUn,hUd,hU⟩ := hRC
  have Hd (d : ℕ) := countable_accepted e (d := d)
  choose C hC hCP hCc using Hd
  refine ⟨C,hC,hCP,U,hUz.isOpen e,hUn,?_⟩
  intro xy hxy
  obtain ⟨g,hg0,hg1⟩ := RationallyConnected.fixed_endpoints hU hxy
  obtain ⟨d,τ,hτ,hτf,hτi⟩ := curve_encoding e g
  obtain ⟨P,hP,z,hz,hzτ⟩ := mem_iUnion₂.mp (hCc d hτ)
  refine mem_iUnion.mpr ⟨d,mem_iUnion₂.mpr ⟨P,hP,z,hz,?_⟩⟩
  apply Prod.ext
  · change e.coneLift x₀ (ev false (P.map z) 0)=xy.1
    rw [hzτ, e.coneLift_eq x₀ (regular_nonzero hτ.1 false 0) (hτf 0),hg0]
  · change e.coneLift x₀ (ev false (P.map z) 1)=xy.2
    rw [hzτ, e.coneLift_eq x₀ (regular_nonzero hτ.1 false 1) (hτf 1),hg1]

end SplitTangent

end

end OAI
