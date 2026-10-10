import Mathlib

namespace OAI

/-! Finite Open Maps. -/

noncomputable section
open Set Filter Topology
namespace FiniteOpenMaps
universe u v
variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]
  [T2Space X] (f : X → Y) (ho : IsOpenMap f)
  (hfin : ∀ y, (f ⁻¹' {y}).Finite)

def fiberCard (y : Y) : ℕ := (f ⁻¹' {y}).ncard

include ho hfin in
lemma fiberCard_lower (y : Y) : ∀ᶠ z in 𝓝 y, fiberCard f y ≤ fiberCard f z := by
  classical
  obtain ⟨U,hU,hdis⟩ := (hfin y).t2_separation
  let V : Set Y := ⋂ x∈f ⁻¹' {y}, f '' U x
  have hV : V∈𝓝 y := (Filter.biInter_mem (hfin y)).mpr (fun x hx =>
    (ho _ (hU x).2).mem_nhds ⟨x,(hU x).1,hx⟩)
  filter_upwards [hV] with z hz
  have hh (x : f ⁻¹' {y}) : ∃ a∈U x.val, f a=z :=
    Set.mem_iInter₂.mp hz x.val x.property
  choose g hgU hgf using hh
  let g' : (f ⁻¹' {y}) → (f ⁻¹' {z}) := fun x => ⟨g x,hgf x⟩
  have hg' : Function.Injective g' := by
    intro a b he
    apply Subtype.ext
    by_contra hab
    have hab' : Disjoint (U a.val) (U b.val) := hdis a.property b.property hab
    have he' : g a=g b := congrArg Subtype.val he
    exact Set.disjoint_left.mp hab' (hgU a) (he' ▸ hgU b)
  let : Finite (f ⁻¹' {z}) := (hfin z).to_subtype
  simpa only [fiberCard,Nat.card_coe_set_eq] using Nat.card_le_card_of_injective g' hg'

include ho hfin in
lemma fiberCard_le_isClosed (n : ℕ) : IsClosed {y | fiberCard f y ≤ n} := by
  rw [←isOpen_compl_iff]
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  have hy' : n<fiberCard f y := Nat.lt_of_not_ge hy
  filter_upwards [fiberCard_lower f ho hfin y] with z hz
  exact Nat.not_le_of_gt (hy'.trans_le hz)

 

def constantCardLocus : Set Y := {y | ∀ᶠ z in 𝓝 y, fiberCard f z=fiberCard f y}

omit [TopologicalSpace X] [T2Space X] in
lemma constantCardLocus_isOpen : IsOpen (constantCardLocus f) := by
  apply isOpen_iff_mem_nhds.mpr
  intro y hy
  obtain ⟨U,hsub,hU,hyU⟩ := mem_nhds_iff.mp hy
  apply Filter.mem_of_superset (hU.mem_nhds hyU)
  intro z hz
  change ∀ᶠ w in 𝓝 z, fiberCard f w=fiberCard f z
  filter_upwards [hU.mem_nhds hz] with w hw
  exact (hsub hw).trans (hsub hz).symm

include ho hfin in
lemma constantCardLocus_dense [BaireSpace Y] : Dense (constantCardLocus f) := by
  classical
  have hd : Dense (⋃ n : ℕ, interior {y | fiberCard f y ≤ n}) :=
    IsGδ.dense_iUnion_interior_of_closed isOpen_univ.isGδ dense_univ
      (fiberCard_le_isClosed f ho hfin) (fun y _ => Set.mem_iUnion.mpr ⟨fiberCard f y,show fiberCard f y ≤ fiberCard f y from le_rfl⟩)
  apply dense_iff_inter_open.mpr
  intro W hW hWn
  obtain ⟨y,hyW,hy⟩ := hd.inter_open_nonempty W hW hWn
  obtain ⟨n,hn⟩ := Set.mem_iUnion.mp hy
  let V : Set Y := W ∩ interior {y | fiberCard f y ≤ n}
  have hVo : IsOpen V := hW.inter isOpen_interior
  have hVn : V.Nonempty := ⟨y,hyW,hn⟩
  have hRfin : (fiberCard f '' V).Finite := (Set.finite_Iic n).subset (by
    rintro k ⟨z,hz,rfl⟩
    exact show fiberCard f z ≤ n from
      (interior_subset (s := {y | fiberCard f y ≤ n}) hz.2))
  obtain ⟨m,hm,hmax⟩ := Set.exists_max_image (fiberCard f '' V) id hRfin (hVn.image _)
  obtain ⟨z,hz,rfl⟩ := hm
  refine ⟨z,hz.1,?_⟩
  change ∀ᶠ w in 𝓝 z, fiberCard f w=fiberCard f z
  filter_upwards [hVo.mem_nhds hz,fiberCard_lower f ho hfin z] with w hw hlow
  exact Nat.le_antisymm (hmax _ ⟨w,hw,rfl⟩) hlow

end FiniteOpenMaps

end

end OAI
