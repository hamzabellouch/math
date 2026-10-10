import OAI.Combinatorics.ListHadwiger.Separators

namespace OAI

namespace LinearListHadwiger

open scoped Classical

lemma exists_injective_neighborPairs {V : Type} [DecidableEq V]
    {t : ℕ} (G : SimpleGraph V) (X S : Finset V)
    (hminor : ¬HasCliqueMinor G t)
    (hSX : Disjoint S X)
    (hdeg : ∀ v ∈ S, t ≤ (X.filter (G.Adj v)).card) :
    ∃ f : V → Sym2 V, Set.InjOn f (↑S : Set V) ∧
      ∀ v ∈ S, f v ∈ neighborPairs G X v := by
  classical
  revert hSX hdeg
  induction S using Finset.induction_on with
  | empty =>
    intro _ _
    exact ⟨fun v => s(v, v), by simp [Set.InjOn], by simp⟩
  | @insert v S hv ih =>
    intro hSX hdeg
    obtain ⟨f, hfi, hfp⟩ := ih
      (hSX.mono_left (Finset.subset_insert _ _))
      (fun w hw => hdeg w (Finset.mem_insert_of_mem hw))
    by_cases hex : ∃ p ∈ neighborPairs G X v, p ∉ S.image f
    · obtain ⟨p, hp, hnp⟩ := hex
      let g : V → Sym2 V := fun w => if w = v then p else f w
      have hgv : g v = p := by simp [g]
      have hgS : ∀ w ∈ S, g w = f w := by
        intro w hw
        have hn : w ≠ v := by
          intro he
          subst w
          exact hv hw
        simp only [g, ite_eq_right hn]
      refine ⟨g, ?_, ?_⟩
      · intro a ha b hb hab
        by_cases hav : a = v
        · subst a
          by_cases hbv : b = v
          · exact hbv.symm
          · have hbS := (Finset.mem_insert.mp hb).resolve_left hbv
            rw [hgv, hgS b hbS] at hab
            exact (hnp (Finset.mem_image.mpr ⟨b, hbS, hab.symm⟩)).elim
        · have haS := (Finset.mem_insert.mp ha).resolve_left hav
          by_cases hbv : b = v
          · subst b
            rw [hgS a haS, hgv] at hab
            exact (hnp (Finset.mem_image.mpr ⟨a, haS, hab⟩)).elim
          · have hbS := (Finset.mem_insert.mp hb).resolve_left hbv
            rw [hgS a haS, hgS b hbS] at hab
            exact hfi haS hbS hab
      · intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · rwa [hgv]
        · rw [hgS w hw]
          exact hfp w hw
    · exfalso
      apply hminor
      apply cliqueMinor_of_saturated_pairs G X S (X.filter (G.Adj v))
        (hSX.mono_left (Finset.subset_insert _ _)) (Finset.filter_subset _ _)
        (hdeg v (Finset.mem_insert_self _ _)) f
      · intro w hw a ha
        exact (mem_neighborPairs (hfp w hw) a ha).2
      · intro a ha b hb hab
        have hpair : s(a, b) ∈ neighborPairs G X v :=
          Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr ⟨ha, hb, hab⟩, rfl⟩
        have himage : s(a, b) ∈ S.image f := by
          by_contra hn
          exact hex ⟨s(a, b), hpair, hn⟩
        exact Finset.mem_image.mp himage

theorem high_neighbor_count {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {t : ℕ} (_ht : 2 ≤ t)
    (hminor : hadwigerNumber G < t) (X : Finset V) :
    (Finset.univ.filter (fun v => v ∉ X ∧ t ≤ (X.filter (G.Adj v)).card)).card
      ≤ X.card.choose 2 := by
  classical
  let S := Finset.univ.filter (fun v => v ∉ X ∧ t ≤ (X.filter (G.Adj v)).card)
  have hSX : Disjoint S X := Finset.disjoint_left.mpr fun v hv hx =>
    (Finset.mem_filter.mp hv).2.1 hx
  have hdeg : ∀ v ∈ S, t ≤ (X.filter (G.Adj v)).card :=
    fun _ hv => (Finset.mem_filter.mp hv).2.2
  obtain ⟨f, hfi, hfp⟩ := exists_injective_neighborPairs G X S
    (fun h => (Nat.not_le_of_lt hminor) (cliqueMinor_le_hadwigerNumber h)) hSX hdeg
  have hsub : S.image f ⊆ X.offDiag.image Sym2.mk.uncurry := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hp
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp (hfp v hv)
    obtain ⟨ha, hb, hne⟩ := Finset.mem_offDiag.mp hab
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_offDiag.mpr
      ⟨(Finset.mem_filter.mp ha).1, (Finset.mem_filter.mp hb).1, hne⟩, heq⟩
  calc
    S.card = (S.image f).card := (Finset.card_image_of_injOn hfi).symm
    _ ≤ (X.offDiag.image Sym2.mk.uncurry).card := Finset.card_le_card hsub
    _ = X.card.choose 2 := Sym2.card_image_offDiag X

theorem choosable_add_deleted_card {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Z : Finset V) {s : ℕ}
    (hR : Choosable (G.induce (↑(Finset.univ \ Z) : Set V)) s) :
    Choosable G (s + Z.card) := by
  classical
  intro Color L hL
  have hZ : Choosable (G.induce (↑Z : Set V)) Z.card := by
    have hh := choosable_card (G.induce (↑Z : Set V))
    change Choosable _ (Fintype.card ↥Z) at hh
    simpa only [Fintype.card_coe] using hh
  obtain ⟨cZ, hcZ, hpZ⟩ := hZ Color (fun v => L v.val)
    (fun v => (Nat.le_add_left _ _).trans (hL v.val))
  let used : Finset Color := Finset.univ.image cZ
  have hused : used.card ≤ Z.card := by
    calc
      used.card ≤ (Finset.univ : Finset (↑Z : Set V)).card := Finset.card_image_le
      _ = Z.card := by change Fintype.card ↥Z = Z.card; exact Fintype.card_coe Z
  let LR : (↑(Finset.univ \ Z) : Set V) → Finset Color := fun v => L v.val \ used
  have hs : ∀ v, s ≤ (LR v).card := by
    intro v
    have hh := Finset.card_le_card_sdiff_add_card (s := L v.val) (t := used)
    have hl := hL v.val
    dsimp [LR]
    omega
  obtain ⟨cR, hcR, hpR⟩ := hR Color LR hs
  let c : V → Color := fun v =>
    if hv : v ∈ Z then cZ ⟨v, hv⟩ else cR ⟨v, by simp [hv]⟩
  have hcr : ∀ v (hv : v ∉ Z), c v ∈ L v ∧ c v ∉ used := by
    intro v hv
    have hh := hcR ⟨v, by simp [hv]⟩
    simpa only [c, dite_eq_right hv, LR, Finset.mem_sdiff] using hh
  have hcz : ∀ v (hv : v ∈ Z), c v = cZ ⟨v, hv⟩ :=
    fun v hv => dite_eq_left hv
  have hzr : ∀ v (hv : v ∈ Z), c v ∈ used := by
    intro v hv
    rw [hcz v hv]
    exact Finset.mem_image.mpr ⟨⟨v, hv⟩, Finset.mem_univ _, rfl⟩
  refine ⟨c, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ Z
    · rw [hcz v hv]
      exact hcZ ⟨v, hv⟩
    · exact (hcr v hv).1
  · intro v w hadj
    by_cases hv : v ∈ Z <;> by_cases hw : w ∈ Z
    · rw [hcz v hv, hcz w hw]
      exact hpZ hadj
    · intro heq
      exact (hcr w hw).2 (heq ▸ hzr v hv)
    · intro heq
      exact (hcr v hv).2 (heq.symm ▸ hzr w hw)
    · simp only [c, dite_eq_right hv, dite_eq_right hw]
      exact hpR hadj

theorem listChromaticNumber_deleted {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (Z : Finset V) :
    listChromaticNumber G - Z.card ≤
      listChromaticNumber (G.induce (↑(Finset.univ \ Z) : Set V)) := by
  have hh := choosable_add_deleted_card G Z
    (choosable_listChromaticNumber (G.induce (↑(Finset.univ \ Z) : Set V)))
  have hb := (listChromaticNumber_le_iff G _).mpr hh
  omega

def DegenerateOn {V : Type} (G : SimpleGraph V) (S : Finset V) (d : ℕ) : Prop :=
  ∀ T ⊆ S, T.Nonempty → ∃ v ∈ T, (T.filter (G.Adj v)).card ≤ d

theorem degenerate_coloring_on {V Color : Type} [DecidableEq V]
    (G : SimpleGraph V) (S : Finset V) (L : V → Finset Color) (φ : V → Color)
    {d : ℕ} (hdeg : DegenerateOn G S d) (hL : ∀ v ∈ S, d + 1 ≤ (L v).card) :
    ∃ c, ValidOn G S L c := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    obtain rfl | hS := S.eq_empty_or_nonempty
    · exact ⟨φ, by simp [ValidOn, ProperOn]⟩
    obtain ⟨v, hv, hvd⟩ := hdeg S (Finset.Subset.refl _) hS
    have herase : S.erase v ⊂ S := Finset.erase_ssubset hv
    obtain ⟨c, hc⟩ := ih (S.erase v) herase
      (fun T hT => hdeg T (hT.trans (Finset.erase_subset _ _)))
      (fun w hw => hL w (Finset.mem_of_mem_erase hw))
    let forbidden := (S.filter (G.Adj v)).image c
    have hfc : forbidden.card ≤ d := Finset.card_image_le.trans hvd
    have hpos : (L v \ forbidden).Nonempty := by
      apply Finset.card_pos.mp
      have hh := Finset.card_le_card_sdiff_add_card (s := L v) (t := forbidden)
      have hl := hL v hv
      omega
    obtain ⟨a, ha⟩ := hpos
    obtain ⟨haL, haF⟩ := Finset.mem_sdiff.mp ha
    let c' : V → Color := fun w => if w = v then a else c w
    have hcv : c' v = a := by simp [c']
    have hcw : ∀ w, w ≠ v → c' w = c w := fun w hw => ite_eq_right hw
    refine ⟨c', ?_, ?_⟩
    · intro w hw
      by_cases hwv : w = v
      · subst w
        rwa [hcv]
      · rw [hcw w hwv]
        exact hc.1 w (Finset.mem_erase.mpr ⟨hwv, hw⟩)
    · intro w hw z hz hadj
      by_cases hwv : w = v
      · subst w
        have hzv : z ≠ v := hadj.ne.symm
        rw [hcv, hcw z hzv]
        intro heq
        exact haF (Finset.mem_image.mpr
          ⟨z, Finset.mem_filter.mpr ⟨hz, hadj⟩, heq.symm⟩)
      · by_cases hzv : z = v
        · subst z
          rw [hcw w hwv, hcv]
          intro heq
          exact haF (Finset.mem_image.mpr
            ⟨w, Finset.mem_filter.mpr ⟨hw, hadj.symm⟩, heq⟩)
        · rw [hcw w hwv, hcw z hzv]
          exact hc.2 (Finset.mem_erase.mpr ⟨hwv, hw⟩)
            (Finset.mem_erase.mpr ⟨hzv, hz⟩) hadj

theorem choosable_of_degenerate {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d : ℕ} (hdeg : DegenerateOn G Finset.univ d) :
    Choosable G (d + 1) := by
  classical
  intro Color L hL
  have hn : ∀ v, (L v).Nonempty := by
    intro v
    apply Finset.card_pos.mp
    have hh := hL v
    omega
  choose φ hφ using hn
  obtain ⟨c, hc⟩ := degenerate_coloring_on G Finset.univ L φ hdeg (fun v _ => hL v)
  exact ⟨c, fun v => hc.1 v (Finset.mem_univ _),
    fun _ _ h => hc.2 (Finset.mem_univ _) (Finset.mem_univ _) h⟩

theorem listChromaticNumber_le_of_degenerate {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) {d : ℕ} (hdeg : DegenerateOn G Finset.univ d) :
    listChromaticNumber G ≤ d + 1 :=
  (listChromaticNumber_le_iff G _).mpr (choosable_of_degenerate G hdeg)

end LinearListHadwiger

end OAI
