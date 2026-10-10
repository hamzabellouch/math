import Mathlib
import OAI.GroupTheory.SimpleAmenable.Configurations.TrackPoint

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section PolygonFullGroup
attribute [local instance] Classical.propDecidable

private noncomputable def tupleChartDomain {a m n : ℕ}
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (cs : Fin n → TableChart a m) : polygonAlgebra a := by
  classical
  refine ⟨⋂ i, if (slots i).1 = (cs i).source then
    translate a (slots i).2 ⁻¹' (cs i).domain.val else ∅, ?_⟩
  apply BooleanSubalgebra.iInf_mem
  intro i
  split_ifs
  · exact polygon_preimage_translate _ (cs i).domain.property
  · exact BooleanSubalgebra.bot_mem

private theorem mem_tupleChartDomain {a m n : ℕ}
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (cs : Fin n → TableChart a m) (x : GenericSquare a) :
    x ∈ (tupleChartDomain slots cs).val ↔
      ∀ i, (cs i).Contains ((slots i).1, translate a (slots i).2 x) := by
  classical
  simp only [tupleChartDomain, Set.mem_iInter, TableChart.Contains]
  apply forall_congr'
  intro i
  by_cases h : (slots i).1 = (cs i).source <;> simp [h]

def trackCycle {m : ℕ} (ι : Fin 3 ↪ Fin m) : Equiv.Perm (Fin m) :=
  Equiv.swap (ι 0) (ι 1) * Equiv.swap (ι 1) (ι 2)

theorem trackCycle_apply {m : ℕ} (ι : Fin 3 ↪ Fin m) (i : Fin 3) :
    trackCycle ι (ι i) = ι (i+1) := by
  fin_cases i <;> simp [trackCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
    ι.injective.eq_iff]

theorem trackCycle_apply_of_notMem {m : ℕ} (ι : Fin 3 ↪ Fin m)
    {j : Fin m} (hj : j ∉ Set.range ι) : trackCycle ι j = j := by
  have hne (i : Fin 3) : j ≠ ι i := by
    intro h
    exact hj ⟨i,h.symm⟩
  simp [trackCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hne]

theorem slotHom_cycle_isThreeSlotCycle {a m n : ℕ} (U : polygonAlgebra a)
    (hU : U.val.Nonempty) (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots)) (ι : Fin 3 ↪ Fin n) :
    IsThreeSlotCycle (slotHom U slots hinj (trackCycle ι)) := by
  let subslots : Fin 3 → Fin m × (CutRing × CutRing) := slots ∘ ι
  have he (i : Fin 3) (x : U.val) :
      SlotMap a m U subslots (i,x) = SlotMap a m U slots (ι i,x) := rfl
  refine ⟨U,subslots,hU,?_,?_,?_⟩
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    rw [he, he] at h
    have hi := hinj h
    exact Prod.ext (ι.injective (congrArg Prod.fst hi)) (congrArg (fun z : Fin n × U.val => z.2) hi)
  · intro i x
    rw [he,he]
    change slotPerm U slots hinj (trackCycle ι) (SlotMap a m U slots (ι i,x)) = _
    rw [slotPerm_apply,trackCycle_apply]
  · intro p hp
    change slotPerm U slots hinj (trackCycle ι) p = p
    by_cases h : p ∈ Set.range (SlotMap a m U slots)
    · obtain ⟨⟨j,x⟩, rfl⟩ := h
      rw [slotPerm_apply]
      have hj : j ∉ Set.range ι := by
        rintro ⟨i,rfl⟩
        exact hp ⟨(i,x),rfl⟩
      rw [trackCycle_apply_of_notMem ι hj]
    · exact slotPerm_apply_of_notMem U slots hinj _ h

def threeInFive : Fin 3 ↪ Fin 5 := ⟨![0,1,2], by decide⟩
def leftThreeInFive : Fin 3 ↪ Fin 5 := ⟨![0,1,3], by decide⟩
def rightThreeInFive : Fin 3 ↪ Fin 5 := ⟨![0,2,4], by decide⟩

open scoped commutatorElement in
theorem five_cycle_commutator :
    ⁅trackCycle leftThreeInFive, trackCycle rightThreeInFive⁆ = trackCycle threeInFive := by
  decide

theorem two_spare_tracks {m : ℕ} (hm : 5 ≤ m) (s : Fin 3 → Fin m) :
    ∃ k l : Fin m, k ≠ l ∧ (∀ i, s i ≠ k) ∧ (∀ i, s i ≠ l) := by
  classical
  let used := Finset.univ.image s
  have hc : used.card ≤ 3 := by
    exact Finset.card_image_le.trans (by simp)
  have hleft : 1 < usedᶜ.card := by
    rw [Finset.card_compl]
    simp only [Fintype.card_fin]
    omega
  obtain ⟨k,hk⟩ := Finset.card_pos.mp (by omega : 0 < usedᶜ.card)
  obtain ⟨l,hl,hlk⟩ := Finset.exists_mem_ne hleft k
  refine ⟨k,l,Ne.symm hlk,?_,?_⟩
  · intro i he
    have hi : k ∈ used := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩
    exact Finset.mem_compl.mp hk hi
  · intro i he
    have hi : l ∈ used := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,he⟩
    exact Finset.mem_compl.mp hl hi

noncomputable def extendSlots {m : ℕ}
    (s : Fin 3 → Fin m × (CutRing × CutRing)) (k l : Fin m) (i : Fin 5) :
    Fin m × (CutRing × CutRing) :=
  if h : i.val < 3 then s ⟨i.val,h⟩ else if i.val = 3 then (k,0) else (l,0)

theorem extendSlots_three {m : ℕ}
    (s : Fin 3 → Fin m × (CutRing × CutRing)) (k l : Fin m) (i : Fin 3) :
    extendSlots s k l (threeInFive i) = s i := by
  fin_cases i <;> simp [extendSlots, threeInFive]

theorem extendSlots_injective {a m : ℕ} (U : polygonAlgebra a)
    (s : Fin 3 → Fin m × (CutRing × CutRing))
    (hs : Function.Injective (SlotMap a m U s)) (k l : Fin m)
    (hkl : k ≠ l) (hk : ∀ i, (s i).1 ≠ k) (hl : ∀ i, (s i).1 ≠ l) :
    Function.Injective (SlotMap a m U (extendSlots s k l)) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  have htrack := congrArg Prod.fst he
  change (extendSlots s k l i).1 = (extendSlots s k l j).1 at htrack
  have hij : i = j := by
    by_cases hi : i.val < 3
    · by_cases hj : j.val < 3
      · have hh : SlotMap a m U s (⟨i.val,hi⟩,x) =
            SlotMap a m U s (⟨j.val,hj⟩,y) := by
          simpa [SlotMap, extendSlots, hi, hj] using he
        have hh' := congrArg (fun z : Fin 3 × U.val => z.1.val) (hs hh)
        exact Fin.ext hh'
      · by_cases hj3 : j.val = 3
        · exact False.elim (hk ⟨i.val,hi⟩ (by simpa [extendSlots,hi,hj,hj3] using htrack))
        · exact False.elim (hl ⟨i.val,hi⟩ (by simpa [extendSlots,hi,hj,hj3] using htrack))
    · by_cases hj : j.val < 3
      · by_cases hi3 : i.val = 3
        · exact False.elim (hk ⟨j.val,hj⟩ (by simpa [extendSlots,hi,hj,hi3] using htrack.symm))
        · exact False.elim (hl ⟨j.val,hj⟩ (by simpa [extendSlots,hi,hj,hi3] using htrack.symm))
      · by_cases hi3 : i.val = 3 <;> by_cases hj3 : j.val = 3
        · exact Fin.ext (hi3.trans hj3.symm)
        · exact False.elim (hkl (by simpa [extendSlots,hi,hj,hi3,hj3] using htrack))
        · exact False.elim (hkl (by simpa [extendSlots,hi,hj,hi3,hj3] using htrack.symm))
        · apply Fin.ext
          omega
  subst j
  refine Prod.ext rfl ?_
  apply Subtype.ext
  exact (translation a (extendSlots s k l i).2).injective (congrArg Prod.snd he)

open scoped commutatorElement in

theorem threeSlotCycle_is_commutator {a m : ℕ} (hm : 5 ≤ m)
    {g : polygonFullGroup a m} (hg : IsThreeSlotCycle g) :
    ∃ b c : polygonFullGroup a m,
      IsThreeSlotCycle b ∧ IsThreeSlotCycle c ∧ ⁅b,c⁆ = g := by
  obtain ⟨U,s,hU,hs,hgact,hgfix⟩ := hg
  obtain ⟨k,l,hkl,hk,hl⟩ := two_spare_tracks hm (fun i => (s i).1)
  let S := extendSlots s k l
  have hS := extendSlots_injective U s hs k l hkl hk hl
  let φ := slotHom U S hS
  refine ⟨φ (trackCycle leftThreeInFive), φ (trackCycle rightThreeInFive),
    slotHom_cycle_isThreeSlotCycle U hU S hS _,
    slotHom_cycle_isThreeSlotCycle U hU S hS _, ?_⟩
  rw [← map_commutatorElement, five_cycle_commutator]
  have he (i : Fin 3) (x : U.val) :
      SlotMap a m U S (threeInFive i,x) = SlotMap a m U s (i,x) := by
    simp only [SlotMap, S, extendSlots_three]
  apply Subtype.ext
  apply Equiv.ext
  intro p
  change slotPerm U S hS (trackCycle threeInFive) p = g.val p
  by_cases hp : p ∈ Set.range (SlotMap a m U s)
  · obtain ⟨⟨i,x⟩,rfl⟩ := hp
    rw [← he i x, slotPerm_apply, trackCycle_apply, he, he, hgact]
  · rw [hgfix p hp]
    by_cases hP : p ∈ Set.range (SlotMap a m U S)
    · obtain ⟨⟨j,x⟩,rfl⟩ := hP
      rw [slotPerm_apply]
      have hj : j ∉ Set.range threeInFive := by
        rintro ⟨i,rfl⟩
        exact hp ⟨(i,x),(he i x).symm⟩
      rw [trackCycle_apply_of_notMem threeInFive hj]
    · exact slotPerm_apply_of_notMem U S hS _ hP

theorem polygonAlternatingGroup_perfect (a m : ℕ) (hm : 5 ≤ m) :
    Group.IsPerfect (polygonAlternatingGroup a m) := by
  apply Subgroup.isPerfect_iff.mpr
  apply le_antisymm (Subgroup.commutator_le_self _)
  change Subgroup.closure _ ≤ _
  apply (Subgroup.closure_le _).mpr
  intro g hg
  obtain ⟨b,c,hb,hc,rfl⟩ := threeSlotCycle_is_commutator hm hg
  exact Subgroup.commutator_mem_commutator (Subgroup.subset_closure hb)
    (Subgroup.subset_closure hc)

theorem conditional_isThreeSlotCycle {a m : ℕ} (U : polygonAlgebra a)
    (hU : U.val.Nonempty) (ι : Fin 3 ↪ Fin m) :
    IsThreeSlotCycle (conditionalHom U (trackCycle ι)) := by
  classical
  let slots : Fin 3 → Fin m × (CutRing × CutRing) := fun i => (ι i, 0)
  have hslot (i : Fin 3) (x : U.val) :
      SlotMap a m U slots (i,x) = (ι i,x.val) := by
    simp [SlotMap, slots]
  refine ⟨U, slots, hU, ?_, ?_, ?_⟩
  · rintro ⟨i,x⟩ ⟨j,y⟩ h
    simp only [hslot, Prod.mk.injEq] at h
    exact Prod.ext (ι.injective h.1) (Subtype.ext h.2)
  · intro i x
    rw [hslot, hslot]
    change conditionalPerm U (trackCycle ι) (ι i, x.val) = _
    simp [x.property, trackCycle_apply]
  · intro p hp
    have hn (i : Fin 3) (hx : p.2 ∈ U.val) : p.1 ≠ ι i := by
      intro h
      apply hp
      exact ⟨(i,⟨p.2,hx⟩), by rw [hslot]; exact Prod.ext h.symm rfl⟩
    change conditionalPerm U (trackCycle ι) p = p
    by_cases hx : p.2 ∈ U.val
    · simp [hx, trackCycle, Equiv.Perm.mul_apply, Equiv.swap_apply_def, hn _ hx]
    · simp [hx]

theorem conditional_cycle_mem {a m : ℕ} (U : polygonAlgebra a)
    (ι : Fin 3 ↪ Fin m) : conditionalHom U (trackCycle ι) ∈ polygonAlternatingGroup a m := by
  classical
  by_cases hU : U.val.Nonempty
  · exact Subgroup.subset_closure (conditional_isThreeSlotCycle U hU ι)
  · have hz : conditionalHom U (trackCycle ι) = 1 := by
      apply Subtype.ext
      apply Equiv.ext
      intro p
      have hp : p.2 ∉ U.val := fun h => hU ⟨p.2,h⟩
      change conditionalPerm U (trackCycle ι) p = p
      simp [hp]
    rw [hz]
    exact (polygonAlternatingGroup a m).one_mem

theorem conditional_cycle_injective {a m : ℕ} (ι : Fin 3 ↪ Fin m) :
    Function.Injective (fun U : polygonAlgebra a => conditionalHom U (trackCycle ι)) := by
  classical
  intro U V h
  apply Subtype.ext
  ext x
  have he := congrArg (fun g : polygonFullGroup a m => g.val (ι 0,x)) h
  change conditionalPerm U (trackCycle ι) (ι 0,x) =
    conditionalPerm V (trackCycle ι) (ι 0,x) at he
  have h01 : ι 0 ≠ ι 1 := ι.injective.ne (by decide)
  by_cases hu : x ∈ U.val <;> by_cases hv : x ∈ V.val <;>
    simp [hu, hv, trackCycle_apply] at he ⊢

noncomputable def shrinkingLevel (n : ℕ) : CutRing := (cutTau - 1) ^ (n+1)

@[simp] theorem ordinary_shrinkingLevel (n : ℕ) :
    ordinary (shrinkingLevel n) = (Real.goldenRatio - 1) ^ (n+1) := by
  simp [shrinkingLevel]

theorem shrinkingLevel_bounds (n : ℕ) :
    0 < ordinary (shrinkingLevel n) ∧ ordinary (shrinkingLevel n) < 1 := by
  have hpos : 0 < Real.goldenRatio - 1 := sub_pos.mpr Real.one_lt_goldenRatio
  have hlt : Real.goldenRatio - 1 < 1 := by linarith [Real.goldenRatio_lt_two]
  simpa using And.intro (pow_pos hpos (n+1)) (pow_lt_one₀ hpos.le hlt (Nat.succ_ne_zero n))

theorem shrinkingLevel_strictAnti : StrictAnti (fun n => ordinary (shrinkingLevel n)) := by
  intro n k hnk
  simp only [ordinary_shrinkingLevel]
  exact pow_lt_pow_right_of_lt_one₀ (sub_pos.mpr Real.one_lt_goldenRatio)
    (by linarith [Real.goldenRatio_lt_two]) (by omega)

noncomputable def shrinkingPolygon (a n : ℕ) : polygonAlgebra a :=
  ⟨halfPlane a 0 (shrinkingLevel n), BooleanSubalgebra.subset_closure ⟨0,shrinkingLevel n,rfl⟩⟩

theorem shrinkingPolygon_injective (a : ℕ) : Function.Injective (shrinkingPolygon a) := by
  suffices h : ∀ n k : ℕ, n < k → shrinkingPolygon a n ≠ shrinkingPolygon a k by
    intro n k he
    rcases lt_trichotomy n k with hlt | heq | hgt
    · exact False.elim (h n k hlt he)
    · exact heq
    · exact False.elim (h k n hgt he.symm)
  intro n k hnk he
  obtain ⟨p,hx,_⟩ := generic_rectangle a (ordinary (shrinkingLevel k))
    (ordinary (shrinkingLevel n)) 0 1 (shrinkingLevel_bounds k).1.le
    (shrinkingLevel_bounds n).2.le (shrinkingLevel_strictAnti hnk)
    le_rfl le_rfl zero_lt_one
  have hn : p ∈ (shrinkingPolygon a n).val := by
    exact hx.2
  have hk : p ∉ (shrinkingPolygon a k).val := by
    change ¬ p.val.1 < ordinary (shrinkingLevel k)
    linarith [hx.1]
  exact hk (he ▸ hn)

theorem polygonAlternatingGroup_infinite (a m : ℕ) (hm : 3 ≤ m) :
    Infinite (polygonAlternatingGroup a m) := by
  let ι := Fin.castLEEmb hm
  let f : ℕ → polygonAlternatingGroup a m := fun n =>
    ⟨conditionalHom (shrinkingPolygon a n) (trackCycle ι),
      conditional_cycle_mem (shrinkingPolygon a n) ι⟩
  apply Infinite.of_injective f
  intro n k h
  apply shrinkingPolygon_injective a
  apply conditional_cycle_injective ι
  exact congrArg Subtype.val h

theorem conjugate_threeSlot_mem {a m : ℕ} (g h : polygonFullGroup a m)
    (hh : IsThreeSlotCycle h) : g * h * g⁻¹ ∈ polygonAlternatingGroup a m := by
  classical
  obtain ⟨U,slots,hne,hinj,hcycle,hfix⟩ := hh
  let σ := trackCycle (Function.Embedding.refl (Fin 3))
  have heq : h = slotHom U slots hinj σ := by
    apply Subtype.ext
    apply Equiv.ext
    intro p
    by_cases hp : p ∈ Set.range (SlotMap a m U slots)
    · obtain ⟨⟨i,x⟩,rfl⟩ := hp
      change h.val (SlotMap a m U slots (i,x)) = slotPerm U slots hinj σ _
      rw [hcycle, slotPerm_apply]
      exact (congrArg (fun j => SlotMap a m U slots (j,x))
        (trackCycle_apply (Function.Embedding.refl (Fin 3)) i)).symm
    · exact (hfix p hp).trans (slotPerm_apply_of_notMem U slots hinj σ hp).symm
  rw [heq]
  let N := (polygonAlternatingGroup a m).comap (MulAut.conj g).toMonoidHom
  change slotHom U slots hinj σ ∈ N
  obtain ⟨s,hs,hcover⟩ := g.property
  let β := Fin 3 → {c // c ∈ s}
  let cover : β → polygonAlgebra a := fun cs => tupleChartDomain slots (fun i => (cs i).val)
  apply slotHom_of_finite_cover (Finset.univ : Finset β) cover U slots hinj σ N
  · intro x hx
    have hc (i : Fin 3) : ∃ c : {c // c ∈ s}, c.val.Contains ((slots i).1,translate a (slots i).2 x) := by
      obtain ⟨c,hc,hcp⟩ := hcover ((slots i).1,translate a (slots i).2 x)
      exact ⟨⟨c,hc⟩,hcp⟩
    choose cs hcs using hc
    exact ⟨cs,Finset.mem_univ _,(mem_tupleChartDomain slots _ x).mpr hcs⟩
  · intro cs _ V hVU hVC
    let targets : Fin 3 → Fin m × (CutRing × CutRing) :=
      fun i => ((cs i).val.target, (cs i).val.shift + (slots i).2)
    have htrans (i : Fin 3) (x : V.val) :
        g.val (SlotMap a m V slots (i,x)) = SlotMap a m V targets (i,x) := by
      have hx := (mem_tupleChartDomain slots _ x.val).mp (hVC x.property) i
      change g.val ((slots i).1,translate a (slots i).2 x.val) =
        ((cs i).val.target,translate a ((cs i).val.shift + (slots i).2) x.val)
      rw [hx.1, hs (cs i).val (cs i).property _ hx.2, translate_add]
    have hinjV := SlotMap_injective_mono slots hVU hinj
    have hinjT : Function.Injective (SlotMap a m V targets) := by
      rintro ⟨i,x⟩ ⟨j,y⟩ he
      rw [← htrans, ← htrans] at he
      exact hinjV (g.val.injective he)
    change g * slotHom V slots hinjV σ * g⁻¹ ∈ polygonAlternatingGroup a m
    rw [slotHom_conjugate V slots targets hinjV hinjT g htrans σ]
    by_cases hV : V.val.Nonempty
    · apply Subgroup.subset_closure
      exact slotHom_cycle_isThreeSlotCycle V hV targets hinjT (Function.Embedding.refl (Fin 3))
    · rw [slotHom_empty V targets hinjT σ (Set.not_nonempty_iff_eq_empty.mp hV)]
      exact Subgroup.one_mem _

theorem polygonAlternatingGroup_normal (a m : ℕ) : (polygonAlternatingGroup a m).Normal := by
  constructor
  intro h hh g
  change h ∈ Subgroup.closure {h | IsThreeSlotCycle h} at hh
  have hc : Subgroup.closure {h : polygonFullGroup a m | IsThreeSlotCycle h} ≤
      (polygonAlternatingGroup a m).comap (MulAut.conj g).toMonoidHom := by
    apply (Subgroup.closure_le _).mpr
    intro h hh
    exact conjugate_threeSlot_mem g h hh
  exact hc hh

theorem isThreeCycle_eq_trackCycle {m : ℕ} {σ : Equiv.Perm (Fin m)}
    (hσ : σ.IsThreeCycle) : ∃ ι : Fin 3 ↪ Fin m, σ = trackCycle ι := by
  classical
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < σ.support.card by rw [hσ.card_support]; decide)
  have hn := hσ.nodup_iff_mem_support.mpr hi
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or,
    List.nodup_nil, not_false_eq_true, and_true] at hn
  have h01 : i ≠ σ i := hn.1.1
  have h02 : i ≠ σ (σ i) := hn.1.2
  have h12 : σ i ≠ σ (σ i) := hn.2
  let ι : Fin 3 ↪ Fin m := ⟨![i,σ i,σ (σ i)], by
    intro j k h
    fin_cases j <;> fin_cases k <;> simp_all⟩
  exact ⟨ι,hσ.eq_swap_mul_swap_iff_mem_support.mpr hi⟩

theorem slotHom_alternating_mem {a m n : ℕ} (U : polygonAlgebra a)
    (slots : Fin n → Fin m × (CutRing × CutRing))
    (hinj : Function.Injective (SlotMap a m U slots))
    {σ : Equiv.Perm (Fin n)} (hσ : σ ∈ alternatingGroup (Fin n)) :
    slotHom U slots hinj σ ∈ polygonAlternatingGroup a m := by
  have hle : alternatingGroup (Fin n) ≤
      (polygonAlternatingGroup a m).comap (slotHom U slots hinj) := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    apply (Subgroup.closure_le _).mpr
    intro ρ hρ
    obtain ⟨ι,rfl⟩ := isThreeCycle_eq_trackCycle hρ
    change slotHom U slots hinj (trackCycle ι) ∈ polygonAlternatingGroup a m
    by_cases hU : U.val.Nonempty
    · exact Subgroup.subset_closure (slotHom_cycle_isThreeSlotCycle U hU slots hinj ι)
    · rw [slotHom_empty U slots hinj _ (Set.not_nonempty_iff_eq_empty.mp hU)]
      exact Subgroup.one_mem _
  exact hle hσ

theorem conditionalHom_alternating_mem {a m : ℕ} (U : polygonAlgebra a)
    {σ : Equiv.Perm (Fin m)} (hσ : σ ∈ alternatingGroup (Fin m)) :
    conditionalHom U σ ∈ polygonAlternatingGroup a m := by
  have hle : alternatingGroup (Fin m) ≤
      (polygonAlternatingGroup a m).comap (conditionalHom U) := by
    rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
    apply (Subgroup.closure_le _).mpr
    intro ρ hρ
    obtain ⟨ι,rfl⟩ := isThreeCycle_eq_trackCycle hρ
    exact conditional_cycle_mem U ι
  exact hle hσ

noncomputable def trackTranslationPerm {a m : ℕ}
    (d : Fin m → CutRing × CutRing) : Equiv.Perm (TrackPoint a m) where
  toFun p := (p.1, translate a (d p.1) p.2)
  invFun p := (p.1, translate a (-d p.1) p.2)
  left_inv p := by simp only [← translate_add, neg_add_cancel, translate_zero]
  right_inv p := by simp only [← translate_add, add_neg_cancel, translate_zero]

end PolygonFullGroup
end SimpleAmenable
end
end

end OAI
