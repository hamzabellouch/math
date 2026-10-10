import Mathlib
import OAI.Geometry.HyperbolicGroups.FinitePolyhedronVoltage

namespace OAI

/-! The literal voltage cover has a free transitive deck action. This supplies
an actual quotient covering to Mathlib's monodromy theorems. -/
noncomputable section

open scoped Topology
open Set
namespace HyperbolicObstruction.FinitePolyhedron.Voltage
variable {V : Type*} [Fintype V] [DecidableEq V]
  {K : AbstractSimplicialComplex V} {G : Type*} [Group G]
  [TopologicalSpace G] [DiscreteTopology G] (v : Voltage K G)

def coordinate (e : v.TotalSpace) : G := e.snd

lemma totalSpace_ext {e f : v.TotalSpace} (h₁ : e.proj = f.proj)
    (h₂ : v.coordinate e = v.coordinate f) : e = f := by
  cases e with | mk a g =>
  cases f with | mk b h =>
  dsimp at h₁
  subst b
  congr

instance deckAction : MulAction G v.TotalSpace where
  smul g e := ⟨e.proj,g * v.coordinate e⟩
  one_smul e := v.totalSpace_ext rfl (one_mul (v.coordinate e))
  mul_smul g h e := v.totalSpace_ext rfl (mul_assoc g h (v.coordinate e))

@[simp] lemma deck_proj (g : G) (e : v.TotalSpace) : v.proj (g • e) = v.proj e := rfl
@[simp] lemma deck_coordinate (g : G) (e : v.TotalSpace) :
    v.coordinate (g • e) = g * v.coordinate e := rfl

lemma chart_deck (i : V) (g : G) (e : v.TotalSpace) :
    v.core.localTriv i (g • e) = ((v.core.localTriv i e).1,g * (v.core.localTriv i e).2) := by
  change (e.proj,(g * v.coordinate e) * v.value _ i) =
    (e.proj,g * (v.coordinate e * v.value _ i))
  rw [mul_assoc]
  rfl

instance deckContinuous : ContinuousConstSMul G v.TotalSpace where
  continuous_const_smul g := by
    apply continuous_iff_continuousAt.mpr
    intro e
    let i := v.core.indexAt e.proj
    let t := v.core.localTriv i
    have he : e.proj ∈ t.baseSet := v.core.mem_baseSet_at e.proj
    apply t.continuousAt_of_comp_left
    · exact v.core.continuous_proj.continuousAt
    · exact he
    · have ht : ContinuousAt t e := t.continuousAt (t.mem_source.mpr he)
      have hg : Continuous (fun a : G => g * a) := continuous_of_discreteTopology
      have hc := ht.fst.prodMk (hg.continuousAt.comp ht.snd)
      convert hc using 1
      funext z
      exact v.chart_deck i g z

lemma same_fiber_iff_orbit (e f : v.TotalSpace) :
    v.proj e = v.proj f ↔ e ∈ MulAction.orbit G f := by
  constructor
  · intro he
    refine ⟨v.coordinate e * (v.coordinate f)⁻¹,?_⟩
    apply v.totalSpace_ext
    · exact he.symm
    · rw [deck_coordinate,mul_assoc,inv_mul_cancel,mul_one]
  · rintro ⟨g,rfl⟩
    rfl

lemma disjoint_deck_neighborhood (e : v.TotalSpace) :
    ∃ U ∈ 𝓝 e, ∀ g : G, ((g • ·) '' U ∩ U).Nonempty → g = 1 := by
  let t := v.core.localTriv (v.core.indexAt e.proj)
  have he : e ∈ t.source := t.mem_source.mpr (v.core.mem_baseSet_at e.proj)
  let U : Set v.TotalSpace := t.source ∩ (fun z => (t z).2) ⁻¹' {(t e).2}
  have hopen : IsOpen U := t.continuousOn.snd.isOpen_inter_preimage t.open_source (isOpen_discrete _)
  refine ⟨U,hopen.mem_nhds ⟨he,rfl⟩,?_⟩
  intro g hg
  obtain ⟨z,⟨y,hy,rfl⟩,hz⟩ := hg
  have hy' : (t y).2 = (t e).2 := hy.2
  have hz' : (t (g • y)).2 = (t e).2 := hz.2
  rw [chart_deck] at hz'
  change g * (t y).2 = (t e).2 at hz'
  rw [hy'] at hz'
  exact mul_right_cancel (hz'.trans (one_mul _).symm)

lemma isQuotientCoveringMap : IsQuotientCoveringMap v.proj G where
  toIsQuotientMap := v.isCoveringMap.isQuotientMap v.proj_surjective
  continuous_const_smul g := continuous_const_smul g
  apply_eq_iff_mem_orbit := v.same_fiber_iff_orbit _ _
  disjoint := v.disjoint_deck_neighborhood

end HyperbolicObstruction.FinitePolyhedron.Voltage
end

end OAI
