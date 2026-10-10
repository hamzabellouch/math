import Mathlib
import OAI.Probability.CriticalPercolation.LinearGroups.SelbergCongruence
import OAI.Probability.CriticalPercolation.LinearGroups.FgMatrixRing

namespace OAI

section
noncomputable section
open Set Function
open scoped Classical

namespace CriticalPercolation.LinearGrowth
variable {G R : Type*} [Group G] [CommRing R] [IsDomain R] [CharZero R]
variable {n : Type*} [Fintype n] [DecidableEq n]

theorem finiteIndex_no_finite_order_of_faithful [Group.FG G]
    (ρ : G →* GL n R) (hρ : Injective ρ) :
    ∃ H : Subgroup G, H.Normal ∧ H.FiniteIndex ∧
      ∀ h : H, IsOfFinOrder h → h=1 := by
  obtain ⟨D,hD,hm⟩ := exists_finiteType_matrix_ring ρ
  let : Algebra.FiniteType ℤ D := hD
  let φ := liftMatrixGroup ρ D hm
  have hφ : Injective φ := liftMatrixGroup_injective ρ D hm hρ
  obtain ⟨K,hKn,hKi,hKt⟩ := exists_finiteIndex_no_finite_order (R:=D) (n:=n)
  let : K.Normal := hKn
  let H := K.comap φ
  have hHi : H.FiniteIndex := by
    constructor
    rw [Subgroup.index_comap]
    intro hz
    exact hKi.index_ne_zero (Nat.eq_zero_of_zero_dvd (hz ▸ K.relIndex_dvd_index_of_normal φ.range))
  let ψ : H →* K := (φ.comp H.subtype).codRestrict K (fun h => h.property)
  refine ⟨H,inferInstance,hHi,?_⟩
  intro h hh
  have hψ : IsOfFinOrder (ψ h) := by
    obtain ⟨m,hm,he⟩ := hh.exists_pow_eq_one
    exact isOfFinOrder_iff_pow_eq_one.mpr ⟨m,hm,by rw [←map_pow,he,map_one]⟩
  have he : ψ h=1 := hKt _ hψ
  apply Subtype.ext
  apply hφ
  exact (congrArg Subtype.val he).trans φ.map_one.symm

theorem finite_of_torsion_faithful [Group.FG G] (ρ : G →* GL n R) (hρ : Injective ρ)
    (ht : ∀ g : G, IsOfFinOrder g) : Finite G := by
  obtain ⟨H,hHn,hHi,hHt⟩ := finiteIndex_no_finite_order_of_faithful ρ hρ
  have hsub : Subsingleton H := by
    constructor
    intro x y
    have htx : IsOfFinOrder x := H.subtype_injective.isOfFinOrder_iff.mp (ht x)
    have hty : IsOfFinOrder y := H.subtype_injective.isOfFinOrder_iff.mp (ht y)
    exact (hHt _ htx).trans (hHt _ hty).symm
  let : Subsingleton H := hsub
  exact H.finite_iff_finite_and_finiteIndex.mpr ⟨inferInstance,hHi⟩

theorem finite_range_of_torsion [Group.FG G] (ρ : G →* GL n R)
    (ht : ∀ g : G, IsOfFinOrder (ρ g)) : Finite ρ.range := by
  let : Group.FG ρ.range := Group.fg_of_surjective ρ.rangeRestrict_surjective
  apply finite_of_torsion_faithful ρ.range.subtype ρ.range.subtype_injective
  intro g
  obtain ⟨x,hx⟩ := g.property
  apply ρ.range.subtype_injective.isOfFinOrder_iff.mp
  change IsOfFinOrder (g : GL n R)
  rw [←hx]
  exact ht x

theorem exists_infinite_order_of_infinite_linear_range [Group.FG G]
    (ρ : G →* GL n R) (hρ : (Set.range ρ).Infinite) :
    ∃ g : G, ¬IsOfFinOrder (ρ g) := by
  by_contra hc
  push Not at hc
  let : Finite ρ.range := finite_range_of_torsion ρ hc
  exact hρ (by simpa only [MonoidHom.coe_range] using (Set.toFinite (ρ.range : Set (GL n R))))

end CriticalPercolation.LinearGrowth
end
end

end OAI
