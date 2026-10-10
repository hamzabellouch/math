import Mathlib
import OAI.Geometry.SplitTangent.FiniteOpenMaps

namespace OAI

/-! Generic Finite Covering. -/

noncomputable section
open Set Filter Topology
namespace FiniteOpenMaps
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] (f : X → Y) (ho : IsOpenMap f)
  (hfin : ∀ y, (f ⁻¹' {y}).Finite)

include hfin in
omit [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] in
lemma unique_in_branch {y z : Y} {U : X → Set X}
    (hdis : (f ⁻¹' {y}).PairwiseDisjoint U)
    (hz : z∈⋂x∈f ⁻¹' {y}, f '' U x)
    (hcard : fiberCard f z ≤ fiberCard f y)
    {x a b : X} (hx : f x=y) (ha : a∈U x) (hb : b∈U x)
    (hea : f a=z) (heb : f b=z) : a=b := by
  classical
  have hh (x : f ⁻¹' {y}) : ∃ a∈U x.val, f a=z :=
    Set.mem_iInter₂.mp hz x.val x.property
  choose g hgU hgf using hh
  let g' : (f ⁻¹' {y}) → (f ⁻¹' {z}) := fun x => ⟨g x,hgf x⟩
  have hg' : Function.Injective g' := by
    intro c d he
    apply Subtype.ext
    by_contra hcd
    have hcd' : Disjoint (U c.val) (U d.val) := hdis c.property d.property hcd
    have he' : g c=g d := congrArg Subtype.val he
    exact Set.disjoint_left.mp hcd' (hgU c) (he' ▸ hgU d)
  let : Finite (f ⁻¹' {z}) := (hfin z).to_subtype
  have hc : Nat.card (f ⁻¹' {z}) ≤ Nat.card (f ⁻¹' {y}) := by
    simpa only [Nat.card_coe_set_eq,fiberCard] using hcard
  have hsurj := (hg'.bijective_of_nat_card_le hc).2
  have hu (c : X) (hcu : c∈U x) (hcz : f c=z) : c=g ⟨x,hx⟩ := by
    obtain ⟨d,hd⟩ := hsurj ⟨c,hcz⟩
    have hd' : g d=c := congrArg Subtype.val hd
    have hdx : d.val=x := by
      by_contra hne
      exact Set.disjoint_left.mp (hdis d.property hx hne) (hd' ▸ hgU d) hcu
    have hde : d=(⟨x,hx⟩ : f ⁻¹' {y}) := Subtype.ext hdx
    simpa only [hde] using hd'.symm
  exact (hu a ha hea).trans (hu b hb heb).symm

include ho hfin in
lemma locally_injective_of_card_constant (hf : Continuous f) {x : X}
    (hx : f x∈constantCardLocus f) :
    ∃ U : Set X, IsOpen U ∧ x∈U ∧ Set.InjOn f U := by
  classical
  obtain ⟨N,hNs,hNo,hxN⟩ := mem_nhds_iff.mp hx
  obtain ⟨U,hU,hdis⟩ := (hfin (f x)).t2_separation
  let V : Set Y := N ∩ ⋂k∈f ⁻¹' {f x}, f '' U k
  have hVo : IsOpen V := hNo.inter
    ((hfin (f x)).isOpen_biInter (fun k _ => ho _ (hU k).2))
  have hxV : f x∈V := ⟨hxN,Set.mem_iInter₂.mpr fun k hk => ⟨k,(hU k).1,hk⟩⟩
  refine ⟨U x ∩ f ⁻¹' V,(hU x).2.inter (hVo.preimage hf),⟨(hU x).1,hxV⟩,?_⟩
  intro a ha b hb hab
  exact unique_in_branch f hfin hdis ha.2.2 (le_of_eq (hNs ha.2.1)) rfl
    ha.1 hb.1 rfl hab.symm

include ho hfin in
lemma isLocalHomeomorphOn_constantCardLocus (hf : Continuous f) :
    IsLocalHomeomorphOn f (f ⁻¹' constantCardLocus f) := by
  rw [isLocalHomeomorphOn_iff_isOpenEmbedding_restrict]
  intro x hx
  obtain ⟨U,hU,hxU,hinj⟩ := locally_injective_of_card_constant f ho hfin hf hx
  refine ⟨U,hU.mem_nhds hxU,?_⟩
  apply isOpenEmbedding_iff_continuous_injective_isOpenMap.mpr
  exact ⟨hf.comp continuous_subtype_val,Set.injOn_iff_injective.mp hinj,
    ho.comp hU.isOpenMap_subtype_val⟩

include ho hfin in
lemma isCoveringMapOn_constantCardLocus [T2Space Y] [CompactSpace X] (hf : Continuous f) :
    IsCoveringMapOn f (constantCardLocus f) :=
  IsCoveringMapOn.of_isLocalHomeomorphOn hf
    (isLocalHomeomorphOn_constantCardLocus f ho hfin hf)

include ho hfin in
lemma exists_dense_open_covering_locus [T2Space Y] [CompactSpace X] [BaireSpace Y]
    (hf : Continuous f) : ∃ U : Set Y, IsOpen U ∧ Dense U ∧ IsCoveringMapOn f U :=
  ⟨constantCardLocus f,constantCardLocus_isOpen f,constantCardLocus_dense f ho hfin,
    isCoveringMapOn_constantCardLocus f ho hfin hf⟩

end FiniteOpenMaps

end

end OAI
