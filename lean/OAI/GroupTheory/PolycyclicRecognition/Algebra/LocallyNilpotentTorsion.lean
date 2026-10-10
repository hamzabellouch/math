import OAI.GroupTheory.PolycyclicRecognition.Algebra.NilpotentTorsionSubgroup
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedLocallyFiniteKernel
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FinitelyGeneratedLift

namespace OAI

/-! # The finite torsion kernel of a locally nilpotent group with bounded torsion -/
noncomputable section
namespace PolycyclicRecognition
variable {G : Type} [Group G]

theorem locallyNilpotent_subgroup (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H)
    (K : Subgroup G) (H : Subgroup K) (hH : H.FG) : Group.IsNilpotent H := by
  let := hlocal (H.map K.subtype) (fg_subgroup_map hH K.subtype)
  exact Group.nilpotent_of_mulEquiv (H.equivMapOfInjective K.subtype Subtype.val_injective).symm

theorem locallyNilpotent_torsion_mul
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H)
    {a b : G} (ha : IsOfFinOrder a) (hb : IsOfFinOrder b) : IsOfFinOrder (a * b) := by
  let H : Subgroup G := Subgroup.closure {a, b}
  have hH : H.FG := (Subgroup.fg_iff H).mpr ⟨{a, b}, rfl, Set.toFinite _⟩
  let := hlocal H hH
  let aH : H := ⟨a, Subgroup.subset_closure (by simp)⟩
  let bH : H := ⟨b, Subgroup.subset_closure (by simp)⟩
  have haH : IsOfFinOrder aH := by
    obtain ⟨n, hn, he⟩ := ha.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext he⟩
  have hbH : IsOfFinOrder bH := by
    obtain ⟨n, hn, he⟩ := hb.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext he⟩
  obtain ⟨n, hn, he⟩ := (nilpotent_torsion_mul haH hbH).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, congrArg Subtype.val he⟩

def locallyNilpotentTorsionSubgroup
    (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H) : Subgroup G where
  carrier := {g | IsOfFinOrder g}
  one_mem' := isOfFinOrder_iff_pow_eq_one.mpr ⟨1, Nat.zero_lt_one, one_pow 1⟩
  mul_mem' := locallyNilpotent_torsion_mul hlocal
  inv_mem' := IsOfFinOrder.inv

variable (hlocal : ∀ H : Subgroup G, H.FG → Group.IsNilpotent H)

instance locallyNilpotentTorsionSubgroup_characteristic :
    (locallyNilpotentTorsionSubgroup hlocal).Characteristic := by
  apply Subgroup.characteristic_iff_map_le.mpr
  intro e g hg
  obtain ⟨a, ha, rfl⟩ := hg
  obtain ⟨n, hn, he⟩ := ha.exists_pow_eq_one
  apply isOfFinOrder_iff_pow_eq_one.mpr
  exact ⟨n, hn, by rw [← map_pow, he, map_one]⟩

theorem locallyNilpotentTorsionSubgroup_locallyFinite
    (H : Subgroup (locallyNilpotentTorsionSubgroup hlocal)) (hH : H.FG) : Finite H := by
  let : Group.FG H := (Group.fg_iff_subgroup_fg _).mpr hH
  let := locallyNilpotent_subgroup hlocal _ H hH
  apply finitelyGenerated_torsion_nilpotent_finite
  intro g
  obtain ⟨n, hn, he⟩ := g.val.property.exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, Subtype.ext (Subtype.ext he)⟩

theorem locallyNilpotentTorsionSubgroup_finite (hb : HasBoundedFiniteSubgroupOrders G) :
    Finite (locallyNilpotentTorsionSubgroup hlocal) :=
  finite_locallyFinite_normal_subgroup _
    (locallyNilpotentTorsionSubgroup_locallyFinite hlocal) hb

theorem locallyNilpotentTorsionQuotient_torsionFree :
    HasNoNontrivialTorsion (G ⧸ locallyNilpotentTorsionSubgroup hlocal) := by
  intro a n hn ha
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (locallyNilpotentTorsionSubgroup hlocal) a
  apply (QuotientGroup.eq_one_iff g).mpr
  have hg : g ^ n ∈ locallyNilpotentTorsionSubgroup hlocal :=
    (QuotientGroup.eq_one_iff _).mp (by
      change (QuotientGroup.mk' (locallyNilpotentTorsionSubgroup hlocal)) (g ^ n) = 1
      rw [map_pow]
      exact ha)
  obtain ⟨m, hm, he⟩ := hg.exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr
    ⟨n * m, Nat.mul_pos (Nat.pos_of_ne_zero hn) hm, by simpa only [pow_mul] using he⟩

include hlocal in
theorem locallyNilpotent_quotient {Q : Type} [Group Q]
    (q : G →* Q) (hq : Function.Surjective q) (K : Subgroup Q) (hK : K.FG) :
    Group.IsNilpotent K := by
  let P := K.comap q
  let p : P →* K := (q.comp P.subtype).codRestrict K (fun x => x.property)
  have hp : Function.Surjective p := by
    intro k
    obtain ⟨g, hg⟩ := hq k
    exact ⟨⟨g, by change q g ∈ K; rw [hg]; exact k.property⟩, Subtype.ext hg⟩
  let : Group.FG K := (Group.fg_iff_subgroup_fg K).mpr hK
  obtain ⟨H, hH, hs⟩ := exists_fg_subgroup_surjective p hp
  let := locallyNilpotent_subgroup hlocal P H hH
  exact Group.nilpotent_of_surjective (p.comp H.subtype) hs

end PolycyclicRecognition

end

end OAI
