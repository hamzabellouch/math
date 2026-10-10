import Mathlib
import OAI.GroupTheory.SimpleAmenable.PolygonGeometry.Supported

namespace OAI

section
section
open scoped symmDiff
namespace SimpleAmenable
section LocalDisplacement

theorem supported_inv {α : Type*} {g : Equiv.Perm α} {U : Set α}
    (h : SupportedIn g U) : SupportedIn g⁻¹ U := by
  intro p hp
  apply g.injective
  change g (g.symm p) = g p
  rw [g.apply_symm_apply,h p hp]

theorem slotHom_supported {a m n : ℕ} (U : polygonAlgebra a)
    (s : Fin n → Fin m × (CutRing × CutRing)) (hs : Function.Injective (SlotMap a m U s))
    (σ : Equiv.Perm (Fin n)) :
    SupportedIn (slotHom U s hs σ).val (Set.range (SlotMap a m U s)) := by
  intro p hp
  exact slotPerm_apply_of_notMem U s hs σ hp

theorem SupportedIn.mono {α : Type*} {g : Equiv.Perm α} {U V : Set α}
    (h : SupportedIn g U) (hUV : U ⊆ V) : SupportedIn g V :=
  fun p hp => h p (fun hu => hp (hUV hu))

theorem subslots_injective {a m n : ℕ} (U : polygonAlgebra a)
    (s : Fin n → Fin m × (CutRing × CutRing)) (hs : Function.Injective (SlotMap a m U s))
    (ι : Fin 3 ↪ Fin n) : Function.Injective (SlotMap a m U (s ∘ ι)) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  change SlotMap a m U s (ι i,x) = SlotMap a m U s (ι j,y) at he
  have he' := hs he
  exact Prod.ext (ι.injective (congrArg Prod.fst he')) (congrArg (fun p : Fin n × U.val => p.2) he')

theorem slotHom_subcycle {a m n : ℕ} (U : polygonAlgebra a)
    (s : Fin n → Fin m × (CutRing × CutRing)) (hs : Function.Injective (SlotMap a m U s))
    (ι : Fin 3 ↪ Fin n) :
    slotHom U s hs (trackCycle ι) =
      slotHom U (s ∘ ι) (subslots_injective U s hs ι) (trackCycle (Function.Embedding.refl _)) := by
  apply Subtype.ext
  apply Equiv.ext
  intro p
  by_cases hp : p ∈ Set.range (SlotMap a m U (s ∘ ι))
  · obtain ⟨⟨i,x⟩,rfl⟩ := hp
    change slotPerm U s hs _ (SlotMap a m U s (ι i,x)) =
      slotPerm U (s ∘ ι) _ _ (SlotMap a m U (s ∘ ι) (i,x))
    rw [slotPerm_apply,slotPerm_apply,trackCycle_apply]
    have hi : trackCycle (Function.Embedding.refl (Fin 3)) i = i+1 :=
      trackCycle_apply (Function.Embedding.refl _) i
    rw [hi]
    rfl
  · rw [slotHom_supported U (s ∘ ι) _ _ p hp]
    by_cases hP : p ∈ Set.range (SlotMap a m U s)
    · obtain ⟨⟨j,x⟩,rfl⟩ := hP
      change slotPerm U s hs _ _ = _
      rw [slotPerm_apply]
      have hj : j ∉ Set.range ι := by
        rintro ⟨i,rfl⟩
        exact hp ⟨(i,x),rfl⟩
      rw [trackCycle_apply_of_notMem ι hj]
    · exact slotHom_supported U s hs _ p hP

open scoped commutatorElement in
theorem relative_normal_commutator_mem {G : Type*} [Group G]
    (N A : Subgroup G)
    (hN : ∀ n ∈ N, ∀ g ∈ A, g*n*g⁻¹ ∈ N)
    {n g : G} (hn : n ∈ N) (hg : g ∈ A) : ⁅n,g⁆ ∈ N := by
  have h := N.mul_mem hn (hN n⁻¹ (N.inv_mem hn) g hg)
  simpa only [commutatorElement_def,mul_assoc] using h

open scoped commutatorElement in

theorem displaced_five_slot_cycle_mem {a m : ℕ}
    (N : Subgroup (polygonFullGroup a m))
    (hN : ∀ n ∈ N, ∀ g ∈ polygonAlternatingGroup a m, g*n*g⁻¹ ∈ N)
    (n : polygonFullGroup a m) (hn : n ∈ N)
    (D : Set (TrackPoint a m)) (hD : Disjoint D (n.val '' D))
    (U : polygonAlgebra a) (hU : U.val.Nonempty)
    (s : Fin 5 → Fin m × (CutRing × CutRing)) (hs : Function.Injective (SlotMap a m U s))
    (hUD : Set.range (SlotMap a m U s) ⊆ D) :
    slotHom U s hs (trackCycle threeInFive) ∈ N := by
  let B := slotHom U s hs (trackCycle leftThreeInFive)
  let C := slotHom U s hs (trackCycle rightThreeInFive)
  have hB : B ∈ polygonAlternatingGroup a m :=
    Subgroup.subset_closure (slotHom_cycle_isThreeSlotCycle U hU s hs _)
  have hC : C ∈ polygonAlternatingGroup a m :=
    Subgroup.subset_closure (slotHom_cycle_isThreeSlotCycle U hU s hs _)
  have hBs : SupportedIn B.val D := (slotHom_supported U s hs _).mono hUD
  have hCs : SupportedIn C.val D := (slotHom_supported U s hs _).mono hUD
  have he : ⁅⁅n,B⁻¹⁆,C⁆ = ⁅B,C⁆ := by
    apply Subtype.ext
    change ⁅⁅n.val,B.val⁻¹⁆,C.val⁆ = ⁅B.val,C.val⁆
    simpa only [inv_inv] using supported_double_commutator n.val B.val⁻¹ C.val D
      (supported_inv hBs) hCs hD
  have hh := relative_normal_commutator_mem N _ hN
    (relative_normal_commutator_mem N _ hN hn ((polygonAlternatingGroup a m).inv_mem hB)) hC
  rw [he] at hh
  change ⁅slotHom U s hs (trackCycle leftThreeInFive),
    slotHom U s hs (trackCycle rightThreeInFive)⁆ ∈ N at hh
  rwa [← map_commutatorElement,five_cycle_commutator] at hh

theorem polygon_separates {a : ℕ} (p q : GenericSquare a) (hpq : p ≠ q) :
    ∃ U : polygonAlgebra a, p ∈ U.val ∧ q ∉ U.val := by
  have hs (j : Fin 4) (hl : cutForm a j p.val < cutForm a j q.val) :
      ∃ U : polygonAlgebra a, p ∈ U.val ∧ q ∉ U.val := by
    obtain ⟨c,hpc,hcq⟩ := exists_cut_between hl
    exact ⟨⟨halfPlane a j c,halfPlane_mem a j c⟩,hpc,not_lt.mpr hcq.le⟩
  have hr (j : Fin 4) (hl : cutForm a j q.val < cutForm a j p.val) :
      ∃ U : polygonAlgebra a, p ∈ U.val ∧ q ∉ U.val := by
    obtain ⟨c,hqc,hcp⟩ := exists_cut_between hl
    exact ⟨⟨(halfPlane a j c)ᶜ,BooleanSubalgebra.compl_mem (halfPlane_mem a j c)⟩,
      not_lt.mpr hcp.le,fun h => h hqc⟩
  by_cases hx : p.val.1 = q.val.1
  · have hy : p.val.2 ≠ q.val.2 := by
      intro h
      exact hpq (Subtype.ext (Prod.ext hx h))
    rcases lt_or_gt_of_ne hy with hy | hy
    · exact hs 1 hy
    · exact hr 1 hy
  · rcases lt_or_gt_of_ne hx with hx | hx
    · exact hs 0 hx
    · exact hr 0 hx

theorem exists_displaced_polygon {a m : ℕ} (n : polygonFullGroup a m) (hn : n ≠ 1) :
    ∃ (t : Fin m) (U : polygonAlgebra a), U.val.Nonempty ∧
      Disjoint {p : TrackPoint a m | p.1 = t ∧ p.2 ∈ U.val}
        (n.val '' {p : TrackPoint a m | p.1 = t ∧ p.2 ∈ U.val}) := by
  have hex : ∃ p, n.val p ≠ p := by
    by_contra! h
    apply hn
    apply Subtype.ext
    exact Equiv.ext h
  obtain ⟨p,hp⟩ := hex
  obtain ⟨cs,hcs,hcover⟩ := n.property
  obtain ⟨c,hc,hcp⟩ := hcover p
  have hscene : n.val p = (c.target,translate a c.shift p.2) := by
    have h := hcs c hc p.2 hcp.2
    simpa only [← hcp.1] using h
  by_cases htrack : c.target = c.source
  · have hneq : p.2 ≠ translate a c.shift p.2 := by
      intro h
      apply hp
      rw [hscene]
      exact Prod.ext (htrack.trans hcp.1.symm) h.symm
    obtain ⟨V,hpV,hqV⟩ := polygon_separates p.2 (translate a c.shift p.2) hneq
    let U : polygonAlgebra a :=
      ⟨c.domain.val ∩ V.val ∩ translate a c.shift ⁻¹' V.valᶜ,
       BooleanSubalgebra.inf_mem (BooleanSubalgebra.inf_mem c.domain.property V.property)
         (polygon_preimage_translate _ (BooleanSubalgebra.compl_mem V.property))⟩
    refine ⟨c.source,U,⟨p.2,⟨hcp.2,hpV⟩,hqV⟩,?_⟩
    apply Set.disjoint_left.mpr
    rintro z hz ⟨y,hy,rfl⟩
    have he : n.val y = (c.target,translate a c.shift y.2) := by
      simpa only [← hy.1] using hcs c hc y.2 hy.2.1.1
    rw [he] at hz
    exact hy.2.2 hz.2.1.2
  · refine ⟨c.source,c.domain,⟨p.2,hcp.2⟩,?_⟩
    apply Set.disjoint_left.mpr
    rintro z hz ⟨y,hy,rfl⟩
    have he : n.val y = (c.target,translate a c.shift y.2) := by
      simpa only [← hy.1] using hcs c hc y.2 hy.2
    rw [he] at hz
    exact htrack hz.1

noncomputable def shiftedSlots {m n : ℕ} (u : CutRing × CutRing)
    (s : Fin n → Fin m × (CutRing × CutRing)) : Fin n → Fin m × (CutRing × CutRing) :=
  fun i => ((s i).1,(s i).2-u)

private theorem untranslate_mem {a : ℕ} {U V : polygonAlgebra a}
    (u : CutRing × CutRing) (hVU : V.val ⊆ (translatedPolygon u U).val)
    (x : V.val) : translate a (-u) x.val ∈ U.val := by
  obtain ⟨y,hy,he⟩ := hVU x.property
  change translate a u y = x.val at he
  rw [← he,← translate_add,neg_add_cancel,translate_zero]
  exact hy

private theorem slotMap_shifted {a m n : ℕ} {U V : polygonAlgebra a}
    (u : CutRing × CutRing) (hVU : V.val ⊆ (translatedPolygon u U).val)
    (s : Fin n → Fin m × (CutRing × CutRing)) (i : Fin n) (x : V.val) :
    SlotMap a m V (shiftedSlots u s) (i,x) =
      SlotMap a m U s (i,⟨translate a (-u) x.val,untranslate_mem u hVU x⟩) := by
  simp only [SlotMap,shiftedSlots,sub_eq_add_neg,translate_add]

private theorem shiftedSlots_injective {a m n : ℕ} {U V : polygonAlgebra a}
    (u : CutRing × CutRing) (hVU : V.val ⊆ (translatedPolygon u U).val)
    (s : Fin n → Fin m × (CutRing × CutRing))
    (hs : Function.Injective (SlotMap a m U s)) :
    Function.Injective (SlotMap a m V (shiftedSlots u s)) := by
  rintro ⟨i,x⟩ ⟨j,y⟩ he
  rw [slotMap_shifted u hVU,slotMap_shifted u hVU] at he
  have hh := hs he
  refine Prod.ext (congrArg (fun p : Fin n × U.val => p.1) hh) (Subtype.ext ?_)
  exact (translation a (-u)).injective (congrArg (fun p => p.2.val) hh)

theorem threeSlot_eq_slotHom {a m : ℕ} {g : polygonFullGroup a m}
    (hg : IsThreeSlotCycle g) :
    ∃ (U : polygonAlgebra a) (s : Fin 3 → Fin m × (CutRing × CutRing))
      (hs : Function.Injective (SlotMap a m U s)),
      g = slotHom U s hs (trackCycle (Function.Embedding.refl _)) := by
  obtain ⟨U,s,hU,hs,hact,hfix⟩ := hg
  refine ⟨U,s,hs,?_⟩
  apply Subtype.ext
  apply Equiv.ext
  intro p
  by_cases hp : p ∈ Set.range (SlotMap a m U s)
  · obtain ⟨⟨i,x⟩,rfl⟩ := hp
    change g.val (SlotMap a m U s (i,x)) = slotPerm U s hs _ _
    rw [hact,slotPerm_apply]
    exact (congrArg (fun j => SlotMap a m U s (j,x))
      (trackCycle_apply (Function.Embedding.refl (Fin 3)) i)).symm
  · exact (hfix p hp).trans (slotPerm_apply_of_notMem U s hs _ hp).symm

theorem alternating_le_of_nontrivial_relative_normal {a m : ℕ} (hm : 15 ≤ m)
    (N : Subgroup (polygonFullGroup a m))
    (hN : ∀ n ∈ N, ∀ g ∈ polygonAlternatingGroup a m, g*n*g⁻¹ ∈ N)
    (n : polygonFullGroup a m) (hn : n ∈ N) (hne : n ≠ 1) :
    polygonAlternatingGroup a m ≤ N := by
  obtain ⟨t,U,hU,hdis⟩ := exists_displaced_polygon n hne
  obtain ⟨d,hd,hd1,s,hs,hD⟩ := five_slots_in_polygon U hU t
  obtain ⟨cover,hcover⟩ := smallSquare_finite_translated_cover a d hd hd1
  apply (Subgroup.closure_le _).mpr
  intro f hf
  obtain ⟨V,v,hv,rfl⟩ := threeSlot_eq_slotHom hf
  apply slotHom_of_finite_cover cover (fun u => translatedPolygon u (smallSquare a d))
    V v hv _ N
  · intro x _
    exact hcover x
  · intro u _ W hWV hWu
    by_cases hW : W.val.Nonempty
    · let s' := shiftedSlots u s
      have hs' : Function.Injective (SlotMap a m W s') := shiftedSlots_injective u hWu s hs
      have hD' : Set.range (SlotMap a m W s') ⊆ {p | p.1 = t ∧ p.2 ∈ U.val} := by
        rintro p ⟨⟨i,x⟩,rfl⟩
        rw [slotMap_shifted u hWu]
        exact hD ⟨_,rfl⟩
      have hlocal := displaced_five_slot_cycle_mem N hN n hn _ hdis W hW s' hs' hD'
      rw [slotHom_subcycle] at hlocal
      let targets := s' ∘ threeInFive
      have ht := subslots_injective W s' hs' threeInFive
      have hvW := SlotMap_injective_mono v hWV hv
      obtain ⟨g,hg,hgact⟩ := transport_three_slots hm W v targets hvW ht
      have heq := slotHom_conjugate W v targets hvW ht g hgact
        (trackCycle (Function.Embedding.refl (Fin 3)))
      have hc := hN _ hlocal g⁻¹ ((polygonAlternatingGroup a m).inv_mem hg)
      rw [← heq] at hc
      simpa only [inv_inv,mul_assoc,inv_mul_cancel_left,mul_inv_cancel_right,inv_mul_cancel,mul_one] using hc
    · rw [slotHom_empty W v _ _ (Set.not_nonempty_iff_eq_empty.mp hW)]
      exact N.one_mem

theorem polygonAlternatingGroup_simple (a m : ℕ) (hm : 15 ≤ m) :
    IsSimpleGroup (polygonAlternatingGroup a m) := by
  rw [Subgroup.isSimpleGroup_iff]
  have hinf := polygonAlternatingGroup_infinite a m (by omega)
  let : Infinite (polygonAlternatingGroup a m) := hinf
  refine ⟨(polygonAlternatingGroup a m).nontrivial_iff_ne_bot.mp inferInstance,?_⟩
  intro N hNA hnormal
  by_cases hN : N = ⊥
  · exact Or.inl hN
  · right
    apply le_antisymm hNA
    have hex : ∃ n ∈ N, n ≠ 1 := by
      by_contra! h
      exact hN ((Subgroup.eq_bot_iff_forall N).mpr h)
    obtain ⟨n,hn,hne⟩ := hex
    apply alternating_le_of_nontrivial_relative_normal hm N ?_ n hn hne
    intro x hx g hg
    have hh := hnormal.conj_mem (⟨x,hNA hx⟩ : polygonAlternatingGroup a m) hx
      (⟨g,hg⟩ : polygonAlternatingGroup a m)
    exact hh

end LocalDisplacement

end SimpleAmenable
end
end

end OAI
