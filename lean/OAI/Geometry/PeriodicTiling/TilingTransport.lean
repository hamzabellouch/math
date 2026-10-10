import OAI.Geometry.PeriodicTiling.TilingBasic
import Mathlib.Logic.Equiv.Set

namespace OAI

universe uG uH uK

namespace PeriodicTilingThree

section AdditiveEquivalence

variable {G : Type uG} {H : Type uH} [AddCommGroup G] [AddCommGroup H]

theorem Tiles.image_addEquiv [DecidableEq H] {F : Finset G} {A : Set G}
    (e : G ≃+ H) (h : Tiles F A) : Tiles (F.image e) (e '' A) := by
  classical
  apply tiles_iff_unique_tile.mpr
  intro x
  obtain ⟨f, hf, huniq⟩ := tiles_iff_unique_tile.mp h (e.symm x)
  refine ⟨⟨e (f : G), Finset.mem_image.mpr ⟨(f : G), f.property, rfl⟩⟩, ?_, ?_⟩
  · refine ⟨e.symm x - (f : G), hf, ?_⟩
    change e (e.symm x - (f : G)) = x - e (f : G)
    rw [map_sub, e.apply_symm_apply]
  · intro g hg
    obtain ⟨y, hyF, hey⟩ := Finset.mem_image.mp g.property
    obtain ⟨a, ha, hea⟩ := hg
    have hyA : e.symm x - y ∈ A := by
      have heq : e.symm x - y = a := by
        apply e.injective
        rw [map_sub, e.apply_symm_apply, hey]
        exact hea.symm
      rw [heq]
      exact ha
    have hyf : (⟨y, hyF⟩ : ↥F) = f := huniq ⟨y, hyF⟩ hyA
    apply Subtype.ext
    calc
      (g : H) = e y := hey.symm
      _ = e (f : G) := congrArg e (congrArg Subtype.val hyf)

theorem tiles_image_addEquiv_iff [DecidableEq H] (e : G ≃+ H)
    {F : Finset G} {A : Set G} :
    Tiles (F.image e) (e '' A) ↔ Tiles F A := by
  classical
  constructor
  · intro h
    simpa only [Finset.image_image, Set.image_image, Function.comp_def,
      e.symm_apply_apply, Finset.image_id', Set.image_id']
      using Tiles.image_addEquiv e.symm h
  · exact Tiles.image_addEquiv e

theorem addEquiv_image_symm_eq_preimage (e : G ≃+ H) (A : Set H) :
    e.symm '' A = e ⁻¹' A := by
  exact e.toEquiv.image_symm_eq_preimage A

theorem Tiles.preimage_addEquiv [DecidableEq G] (e : G ≃+ H)
    {F : Finset H} {A : Set H} (h : Tiles F A) :
    Tiles (F.image e.symm) (e ⁻¹' A) := by
  rw [← addEquiv_image_symm_eq_preimage e A]
  exact Tiles.image_addEquiv e.symm h

theorem tiles_preimage_addEquiv_iff [DecidableEq G] (e : G ≃+ H)
    {F : Finset H} {A : Set H} :
    Tiles (F.image e.symm) (e ⁻¹' A) ↔ Tiles F A := by
  rw [← addEquiv_image_symm_eq_preimage e A]
  exact tiles_image_addEquiv_iff e.symm

end AdditiveEquivalence

section PeriodImages

variable {G : Type uG} {H : Type uH} [AddCommGroup G] [AddCommGroup H]

theorem Period.image {A : Set G} {v : G} (hv : Period A v) (f : G →+ H) :
    Period (f '' A) (f v) := by
  intro y
  constructor
  · rintro ⟨x, hx, hxy⟩
    refine ⟨x - v, ?_, ?_⟩
    · apply (hv (x - v)).mp
      simpa only [sub_add_cancel] using hx
    · rw [map_sub, hxy, add_sub_cancel_right]
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x + v, (hv x).mpr hx, f.map_add x v⟩

theorem finiteIndex_map_of_surjective (P : AddSubgroup G) (hP : P.FiniteIndex)
    (f : G →+ H) (hf : Function.Surjective f) : (P.map f).FiniteIndex := by
  constructor
  intro hz
  have hd := P.index_map_dvd hf
  rw [hz] at hd
  exact hP.index_ne_zero (Nat.eq_zero_of_zero_dvd hd)

theorem FullyPeriodic.image_of_surjective (f : G →+ H)
    (hf : Function.Surjective f) {A : Set G} (h : FullyPeriodic A) :
    FullyPeriodic (f '' A) := by
  obtain ⟨P, hP, hperiod⟩ := h
  refine ⟨P.map f, finiteIndex_map_of_surjective P hP f hf, ?_⟩
  intro w hw
  obtain ⟨v, hv, rfl⟩ := AddSubgroup.mem_map.mp hw
  exact (hperiod v hv).image f

theorem fullyPeriodic_image_addEquiv_iff (e : G ≃+ H) {A : Set G} :
    FullyPeriodic (e '' A) ↔ FullyPeriodic A := by
  constructor
  · intro h
    have h' := FullyPeriodic.image_of_surjective e.symm.toAddMonoidHom
      e.symm.surjective h
    change FullyPeriodic (e.symm '' (e '' A)) at h'
    simpa only [Set.image_image, Function.comp_def, e.symm_apply_apply,
      Set.image_id'] using h'
  · exact FullyPeriodic.image_of_surjective e.toAddMonoidHom e.surjective

theorem FullyPeriodic.preimage_addEquiv (e : G ≃+ H) {A : Set H}
    (h : FullyPeriodic A) : FullyPeriodic (e ⁻¹' A) := by
  rw [← addEquiv_image_symm_eq_preimage e A]
  exact FullyPeriodic.image_of_surjective e.symm.toAddMonoidHom e.symm.surjective h

theorem fullyPeriodic_preimage_addEquiv_iff (e : G ≃+ H) {A : Set H} :
    FullyPeriodic (e ⁻¹' A) ↔ FullyPeriodic A := by
  rw [← addEquiv_image_symm_eq_preimage e A]
  exact fullyPeriodic_image_addEquiv_iff e.symm

end PeriodImages

section FiniteCoordinate

variable {G : Type uG} {K : Type uK} [AddCommGroup G] [AddCommGroup K] [Finite K]

theorem finiteIndex_prod_bot (P : AddSubgroup G) (hP : P.FiniteIndex) :
    (P.prod (⊥ : AddSubgroup K)).FiniteIndex := by
  constructor
  rw [AddSubgroup.index_prod, AddSubgroup.index_bot]
  exact mul_ne_zero hP.index_ne_zero (ne_of_gt (Nat.card_pos : 0 < Nat.card K))

theorem FullyPeriodic.prod_singleton_zero {A : Set G} (h : FullyPeriodic A) :
    FullyPeriodic (A ×ˢ ({0} : Set K)) := by
  obtain ⟨P, hP, hperiod⟩ := h
  refine ⟨P.prod (⊥ : AddSubgroup K), finiteIndex_prod_bot P hP, ?_⟩
  intro v hv x
  obtain ⟨hp, hz⟩ := AddSubgroup.mem_prod.mp hv
  have hzero : v.2 = 0 := AddSubgroup.mem_bot.mp hz
  change (x.1 + v.1 ∈ A ∧ x.2 + v.2 ∈ ({0} : Set K)) ↔
    (x.1 ∈ A ∧ x.2 ∈ ({0} : Set K))
  rw [hzero, add_zero]
  exact and_congr (hperiod v.1 hp x.1) Iff.rfl

end FiniteCoordinate

end PeriodicTilingThree

end OAI
