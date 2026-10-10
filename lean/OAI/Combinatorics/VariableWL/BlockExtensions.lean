import OAI.Combinatorics.VariableWL.BlockCoordinates

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E)

def SupportConnected (hn : 0 < n) (C : Finset (Block (n := n) J)) : Prop :=
  ∀ t ∈ supportTypes J C, ∀ u ∈ supportTypes J C,
    (supportGraph hn J.source J.target (supportLinks J C)).Reachable t u

def NoReal (C : Finset (Block (n := n) J)) : Prop :=
  ∀ p, (.inl p : Vertex P E n) ∉ supportTypes J C

def Avoids (cut : E → Fin (n+1)) (C : Finset (Block (n := n) J)) : Prop :=
  ∀ l ∈ supportLinks J C, l.2 ≠ cut l.1

theorem supportLinks_mono {C D : Finset (Block (n := n) J)} (h : C ⊆ D) :
    supportLinks J C ⊆ supportLinks J D := by
  classical
  exact Finset.biUnion_subset_biUnion_of_subset_left _ h

theorem supportTypes_mono {C D : Finset (Block (n := n) J)} (h : C ⊆ D) :
    supportTypes J C ⊆ supportTypes J D := by
  classical
  exact Finset.biUnion_subset_biUnion_of_subset_left _ h

theorem avoids_mono {C D : Finset (Block (n := n) J)} (h : C ⊆ D)
    {cut : E → Fin (n+1)} (ha : Avoids J cut D) : Avoids J cut C :=
  fun l hl => ha l (supportLinks_mono J h hl)

theorem supportTypes_nonempty {C : Finset (Block (n := n) J)} (hC : C.Nonempty) :
    (supportTypes J C).Nonempty := by
  classical
  obtain ⟨b,hb⟩ := hC
  exact ⟨(anchor J b.val).2.1, Finset.mem_biUnion.mpr ⟨b,hb,anchor_mem_types J b.val⟩⟩

theorem support_noReal_reach (hn : 0 < n) (C : Finset (Block (n := n) J))
    (hnr : NoReal J C) {t : Vertex P E n} (ht : t ∈ supportTypes J C) :
    ∀ p, ¬ (supportGraph hn J.source J.target (supportLinks J C)).Reachable t (.inl p) :=
  fun p hp => hnr p (support_reachable_mem J hn C ht hp)

theorem component_support_connected (hr : 2 ≤ r) (hn : 0 < n)
    (U : Finset (Block (n := n) J)) (c : (diagram J hr hn U).ConnectedComponent) :
    SupportConnected J hn (componentBlocks J hr hn U c) := by
  intro t ht u hu
  exact support_types_connected J hr hn _
    (fun _ hb _ hb' => component_anchors_connected J hr hn U c hb hb') ht hu

theorem internal_same_address (hn : 0 < n) (C : Finset (Block (n := n) J))
    (hC : SupportConnected J hn C) (hnr : NoReal J C)
    (cut : E → Fin (n+1)) (hc : Avoids J cut C) (a : Address r)
    {q q' : E × Fin n} (hq : Sum.inr q ∈ supportTypes J C)
    (hq' : Sum.inr q' ∈ supportTypes J C) :
    q.1 = q'.1 ∧ addressAt J cut a (.inr q) = addressAt J cut a (.inr q') := by
  have hp := hC _ hq _ hq'
  have hnq := support_noReal_reach J hn C hnr hq
  obtain ⟨j,he⟩ := realFree_reachable_wire hn J.source J.target (supportLinks J C) q hnq hp
  have heP : q' = (q.1,j) := Sum.inr.inj he
  have hqq := congrArg Prod.fst heP
  refine ⟨hqq.symm, ?_⟩
  funext i
  have hh := J.alignment_internal_reachable hn (supportLinks J C) cut hc q hnq
    (he ▸ hp) i
  have hh' : J.alignment cut (.inr q) i = J.alignment cut (.inr q') i := by
    simpa only [he] using hh
  simp only [addressAt, hh']

theorem wrapping_address_allowed_superset (hr : 3 ≤ r) (hn : 0 < n)
    (C W : Finset (Block (n := n) J)) (hW : W ⊆ C)
    (hC : SupportConnected J hn C) (hnr : NoReal J C)
    (cut : E → Fin (n+1)) (hc : Avoids J cut C)
    {marked : Fin r} (hw : (rowDiagram J hr hn W).Wraps marked) (hcard : W.card = r)
    {a : Address r} (ha : Recovers J cut W a) {q : E × Fin n}
    (hq : Sum.inr q ∈ supportTypes J C) : J.Allowed q.1 (addressAt J cut a (.inr q)) := by
  have hne : W.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨t,ht⟩ := supportTypes_nonempty J hne
  obtain ⟨q',rfl⟩ : ∃ q', t = Sum.inr q' := by
    cases t with
    | inl p => exact (hnr p (supportTypes_mono J hW ht)).elim
    | inr q' => exact ⟨q',rfl⟩
  have had := wrapping_address_allowed J hr hn W cut (avoids_mono J hW hc)
    hw hcard q' ht (fun p hp => hnr p (supportTypes_mono J hW hp)) ha
  obtain ⟨he,he'⟩ := internal_same_address J hn C hC hnr cut hc a hq
    (supportTypes_mono J hW ht)
  rw [he,he']
  exact had

def AddressCondition (Q : J.Witness) (cut : E → Fin (n+1))
    (C : Finset (Block (n := n) J)) (a : Address r) (h : J.Shifts n) : Prop :=
  (∀ p, Sum.inl p ∈ supportTypes J C → h.1 p ∈ Q.values p (addressAt J cut a (.inl p))) ∧
  (NoReal J C → ∀ q, Sum.inr q ∈ supportTypes J C →
    h.2 q ∈ Q.wireValues q.1 (addressAt J cut a (.inr q)))

def Admissible (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (cut : E → Fin (n+1)) (C : Finset (Block (n := n) J)) (h : J.Shifts n) : Prop :=
  J.ShiftSystem (supportLinks J C) h ∧
  ∀ W ⊆ C, W.card = r → (rowDiagram J hr hn W).Wraps marked →
    ∀ a, Recovers J cut W a → AddressCondition J Q cut C a h

@[simp] theorem addressAt_real (cut : E → Fin (n+1)) (a : Address r) (p : P) :
    addressAt J cut a (.inl p) = a := rfl

theorem admissible_of_one (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (cut : E → Fin (n+1)) (C W : Finset (Block (n := n) J)) (hC : C.card ≤ r+1)
    (hW : W ⊆ C) (hcard : W.card = r) (hw : (rowDiagram J hr hn W).Wraps marked)
    (a : Address r) (ha : Recovers J cut W a) (h : J.Shifts n)
    (hs : J.ShiftSystem (supportLinks J C) h) (had : AddressCondition J Q cut C a h) :
    Admissible J hr hn marked Q cut C h := by
  refine ⟨hs, ?_⟩
  intro W' hW' hcW' hw' a' ha'
  have he := recovered_overlap J hr hn C W W' cut hW hW' hC hcard hcW' hw ha ha'
  subst a'
  exact had

theorem addressCondition_exists (hn : 0 < n) (Q : J.Witness)
    (C : Finset (Block (n := n) J)) (hC : SupportConnected J hn C)
    (cut : E → Fin (n+1)) (hc : Avoids J cut C) (a : Address r) :
    ∃ h : J.Shifts n, J.ShiftSystem (supportLinks J C) h ∧ AddressCondition J Q cut C a h := by
  classical
  choose v hv using Q.nonempty
  let h := J.cutShifts cut (fun p => v p a)
  have hh : J.ShiftSystem (supportLinks J C) h :=
    fun l hl => J.cutShifts_equation hn cut _ l (hc l hl)
  by_cases hnr : NoReal J C
  · by_cases he : (supportTypes J C).Nonempty
    · obtain ⟨t,ht⟩ := he
      obtain ⟨q,rfl⟩ : ∃ q, t = Sum.inr q := by
        cases t with
        | inl p => exact (hnr p ht).elim
        | inr q => exact ⟨q,rfl⟩
      obtain ⟨b,hb⟩ := Q.wireValues_nonempty q.1 (addressAt J cut a (.inr q))
      obtain ⟨g,hg,hgb⟩ := J.exists_scalar_shift hn (supportLinks J C) (.inr q) b h hh
        (support_noReal_reach J hn C hnr ht)
      refine ⟨g,hg,⟨fun p hp => (hnr p hp).elim, fun _ q' hq' => ?_⟩⟩
      rw [hgb q' (hC _ ht _ hq')]
      obtain ⟨he,ha⟩ := internal_same_address J hn C hC hnr cut hc a ht hq'
      simpa only [he,ha] using hb
    · refine ⟨h,hh,⟨?_, fun _ q hq => (he ⟨.inr q,hq⟩).elim⟩⟩
      intro p hp
      exact (he ⟨.inl p,hp⟩).elim
  · refine ⟨h,hh,⟨?_,fun hh => (hnr hh).elim⟩⟩
    intro p _
    exact hv p a

theorem admissible_exists (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (C : Finset (Block (n := n) J)) (hC : SupportConnected J hn C) (hcard : C.card ≤ r+1)
    (cut : E → Fin (n+1)) (hc : Avoids J cut C) :
    ∃ h : J.Shifts n, Admissible J hr hn marked Q cut C h := by
  classical
  by_cases hw : ∃ W ⊆ C, W.card = r ∧ (rowDiagram J hr hn W).Wraps marked
  · obtain ⟨W,hW,hcW,hw⟩ := hw
    obtain ⟨a,ha⟩ := recovered_address J hr hn W cut (avoids_mono J hW hc) hw hcW
    obtain ⟨h,hs,had⟩ := addressCondition_exists J hn Q C hC cut hc a
    exact ⟨h, admissible_of_one J hr hn marked Q cut C W hcard hW hcW hw a ha h hs had⟩
  · refine ⟨J.cutShifts cut (fun _ => 0), ⟨?_,?_⟩⟩
    · exact fun l hl => J.cutShifts_equation hn cut _ l (hc l hl)
    · intro W hW hcW hwW
      exact (hw ⟨W,hW,hcW,hwW⟩).elim
end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : ProductImages.Instance r P E)

theorem addressAt_cut_independent_superset (hr : 3 ≤ r) (hn : 0 < n)
    (C W : Finset (Block (n := n) J)) (hW : W ⊆ C) (hC : SupportConnected J hn C)
    (cut cut' : E → Fin (n+1)) (hc : Avoids J cut C) (hc' : Avoids J cut' C)
    {marked : Fin r} (hw : (rowDiagram J hr hn W).Wraps marked)
    {a a' : Address r} (ha : Recovers J cut W a) (ha' : Recovers J cut' W a')
    {t : Vertex P E n} (ht : t ∈ supportTypes J C) :
    addressAt J cut a t = addressAt J cut' a' t := by
  classical
  have : NeZero r := ⟨by omega⟩
  funext i
  obtain ⟨b,hb,hi⟩ := Finset.mem_image.mp ((rowDiagram J hr hn W).covers_rows W
    (fun b => row b.val) (fun _ _ h _ hi => row_cover J hr hn W h hi)
    Wrapping.RowDiagram.finRotate_orbit hw i)
  have ht' : (anchor J b.val).2.1 ∈ supportTypes J C :=
    Finset.mem_biUnion.mpr ⟨b,hW hb,anchor_mem_types J b.val⟩
  have hrel := J.relativeAlignment_reachable hn (supportLinks J C) cut cut' hc hc'
    (hC _ ht _ ht') i
  have hp := permutation_coordinates (J.alignment cut t i) (J.alignment cut' t i)
    (J.alignment cut (anchor J b.val).2.1 i) (J.alignment cut' (anchor J b.val).2.1 i)
    hrel (anchor J b.val).2.2
  change (J.alignment cut t i).symm (a i) = (J.alignment cut' t i).symm (a' i)
  rw [← hi, ← (ha b hb).1, ← (ha' b hb).1, firstLabel_anchor, firstLabel_anchor]
  simpa only [hi] using hp

theorem admissible_cut_change (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (C : Finset (Block (n := n) J)) (hC : SupportConnected J hn C)
    (cut cut' : E → Fin (n+1)) (hc : Avoids J cut C) (hc' : Avoids J cut' C)
    {h : J.Shifts n} (hh : Admissible J hr hn marked Q cut C h) :
    Admissible J hr hn marked Q cut' C h := by
  refine ⟨hh.1, ?_⟩
  intro W hW hcW hw a' ha'
  obtain ⟨a,ha⟩ := recovered_address J hr hn W cut (avoids_mono J hW hc) hw hcW
  obtain ⟨hreal,hscalar⟩ := hh.2 W hW hcW hw a ha
  refine ⟨?_,?_⟩
  · intro p hp
    rw [← addressAt_cut_independent_superset J hr hn C W hW hC cut cut' hc hc' hw ha ha' hp]
    exact hreal p hp
  · intro hnr q hq
    rw [← addressAt_cut_independent_superset J hr hn C W hW hC cut cut' hc hc' hw ha ha' hq]
    exact hscalar hnr q hq

theorem admissible_restrict (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (C D : Finset (Block (n := n) J)) (hD : D ⊆ C)
    (hC : SupportConnected J hn C) (hDc : SupportConnected J hn D)
    (hsize : (supportLinks J C).card < n+1)
    (cut : E → Fin (n+1)) (hc : Avoids J cut C)
    {h : J.Shifts n} (hh : Admissible J hr hn marked Q cut C h) :
    Admissible J hr hn marked Q cut D h := by
  classical
  refine ⟨fun l hl => hh.1 l (supportLinks_mono J hD hl), ?_⟩
  intro W hW hcW hw a ha
  obtain ⟨hreal,hscalar⟩ := hh.2 W (hW.trans hD) hcW hw a ha
  refine ⟨fun p hp => hreal p (supportTypes_mono J hD hp), ?_⟩
  intro hnrD q hq
  by_cases hnr : NoReal J C
  · exact hscalar hnr q (supportTypes_mono J hD hq)
  · have hex : ∃ p, Sum.inl p ∈ supportTypes J C := by
      simpa only [NoReal, not_forall, not_not] using hnr
    obtain ⟨p,hp⟩ := hex
    have had := wrapping_address_allowed_superset J hr hn D W hW hDc hnrD cut
      (avoids_mono J hD hc) hw hcW ha hq
    apply J.scalar_image_of_real hn Q (supportLinks J C) hsize cut hc h hh.1 q p
      (hC _ (supportTypes_mono J hD hq) _ hp) (addressAt J cut a (.inr q)) had
    simpa only [addressAt, Equiv.apply_symm_apply, addressAt_real] using hreal p hp
end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} (J : ProductImages.Instance r P E)

theorem admissible_lift (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (C D : Finset (Block (n := n) J)) (hD : D ⊆ C)
    (hC : SupportConnected J hn C) (hDc : SupportConnected J hn D)
    (hcard : C.card ≤ r+1) (hsize : (supportLinks J C).card < n+1)
    (hcardD : D.card = r) (hw : (rowDiagram J hr hn D).Wraps marked)
    (cut : E → Fin (n+1)) (hc : Avoids J cut C)
    {h : J.Shifts n} (hh : Admissible J hr hn marked Q cut D h) :
    ∃ g : J.Shifts n, Admissible J hr hn marked Q cut C g ∧
      ∀ t ∈ supportTypes J D, J.AgreeAt h g t := by
  classical
  obtain ⟨a,ha⟩ := recovered_address J hr hn D cut (avoids_mono J hD hc) hw hcardD
  have had := hh.2 D (Finset.Subset.refl _) hcardD hw a ha
  have hsizeD : (supportLinks J D).card < n+1 :=
    lt_of_le_of_lt (Finset.card_le_card (supportLinks_mono J hD)) hsize
  by_cases hnrD : NoReal J D
  · obtain ⟨t,ht⟩ := supportTypes_nonempty J
      (show D.Nonempty from Finset.card_pos.mp (by omega))
    obtain ⟨q,rfl⟩ : ∃ q, t = Sum.inr q := by
      cases t with
      | inl p => exact (hnrD p ht).elim
      | inr q => exact ⟨q,rfl⟩
    have hqa : J.Allowed q.1 (addressAt J cut a (.inr q)) :=
      wrapping_address_allowed_superset J hr hn D D (Finset.Subset.refl _) hDc hnrD
        cut (avoids_mono J hD hc) hw hcardD ha ht
    obtain ⟨g,hg,hgq,hgreal⟩ := J.lift_scalar_to_cut hn Q (supportLinks J C) cut hc q
      (addressAt J cut a (.inr q)) hqa (had.2 hnrD q ht)
    have hcond : AddressCondition J Q cut C a g := by
      refine ⟨?_,?_⟩
      · intro p hp
        simpa only [addressAt, Equiv.apply_symm_apply, addressAt_real] using
          hgreal p (hC _ (supportTypes_mono J hD ht) _ hp)
      · intro hnrC q' hq'
        have hqC := supportTypes_mono J hD ht
        have he := J.scalar_constant hn (supportLinks J C) g hg q
          (support_noReal_reach J hn C hnrC hqC) (hC _ hqC _ hq')
        rw [← he,hgq]
        obtain ⟨hwire,haddr⟩ := internal_same_address J hn C hC hnrC cut hc a hqC hq'
        simpa only [hwire,haddr] using had.2 hnrD q ht
    refine ⟨g,admissible_of_one J hr hn marked Q cut C D hcard hD hcardD hw a ha g hg hcond,?_⟩
    intro t ht'
    exact J.agree_from_internal hn (supportLinks J D) hh.1
      (fun l hl => hg l (supportLinks_mono J hD hl)) q hgq.symm
      (support_noReal_reach J hn D hnrD ht) (hDc _ ht _ ht')
  · obtain ⟨p,hp⟩ : ∃ p, Sum.inl p ∈ supportTypes J D := by
      simpa only [NoReal, not_forall, not_not] using hnrD
    let g := J.cutShifts cut h.1
    have hg : J.ShiftSystem (supportLinks J C) g :=
      fun l hl => J.cutShifts_equation hn cut h.1 l (hc l hl)
    have hcond : AddressCondition J Q cut C a g := by
      refine ⟨?_,?_⟩
      · intro p' hp'
        have hpp := at_most_one_real hn J.source J.target (supportLinks J C) hsize
          (hC _ (supportTypes_mono J hD hp) _ hp')
        subst p'
        exact had.1 p hp
      · intro hnrC
        exact (hnrC p (supportTypes_mono J hD hp)).elim
    refine ⟨g,admissible_of_one J hr hn marked Q cut C D hcard hD hcardD hw a ha g hg hcond,?_⟩
    intro t ht
    exact J.agree_from_real hn (supportLinks J D) hsizeD hh.1
      (fun l hl => hg l (supportLinks_mono J hD hl)) p rfl (hDc _ hp _ ht)
end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance
variable {r n : ℕ} {P : Type uVariable7} {E : Type uVariable8} (J : ProductImages.Instance r P E)

def componentMap (hr : 2 ≤ r) (hn : 0 < n)
    {V U : Finset (Block (n := n) J)} (h : V ⊆ U) :
    (diagram J hr hn V).ConnectedComponent → (diagram J hr hn U).ConnectedComponent :=
  SimpleGraph.ConnectedComponent.map (SimpleGraph.Hom.ofLE (diagram_mono J hr hn h))

@[simp] theorem componentMap_mk (hr : 2 ≤ r) (hn : 0 < n)
    {V U : Finset (Block (n := n) J)} (h : V ⊆ U) (v : Corner r n P E) :
    componentMap J hr hn h ((diagram J hr hn V).connectedComponentMk v) =
      (diagram J hr hn U).connectedComponentMk v := rfl

theorem componentBlocks_map_subset (hr : 2 ≤ r) (hn : 0 < n)
    {V U : Finset (Block (n := n) J)} (h : V ⊆ U)
    (d : (diagram J hr hn V).ConnectedComponent) :
    componentBlocks J hr hn V d ⊆
      componentBlocks J hr hn U (componentMap J hr hn h d) := by
  intro b hb
  obtain ⟨hb,he⟩ := (mem_componentBlocks J hr hn V d b).mp hb
  apply (mem_componentBlocks J hr hn U _ b).mpr
  exact ⟨h hb, (congrArg (componentMap J hr hn h) he)⟩

theorem wrapping_component_all (hr : 3 ≤ r) (hn : 0 < n)
    (V : Finset (Block (n := n) J)) (hV : V.card ≤ r) (marked : Fin r)
    (d : (diagram J (by omega) hn V).ConnectedComponent)
    (hw : (rowDiagram J hr hn (componentBlocks J (by omega) hn V d)).Wraps marked) :
    componentBlocks J (by omega) hn V d = V ∧ V.card = r := by
  have hsub := componentBlocks_subset J (by omega) hn V d
  have hge := wrapping_card_ge J hr hn _ hw
  have hle := Finset.card_le_card hsub
  exact ⟨Finset.eq_of_subset_of_card_le hsub (by omega), by omega⟩

theorem wrapping_component_unique (hr : 3 ≤ r) (hn : 0 < n)
    (V : Finset (Block (n := n) J)) (hV : V.card ≤ r) (marked : Fin r)
    {d d' : (diagram J (by omega) hn V).ConnectedComponent}
    (hw : (rowDiagram J hr hn (componentBlocks J (by omega) hn V d)).Wraps marked)
    (hw' : (rowDiagram J hr hn (componentBlocks J (by omega) hn V d')).Wraps marked) : d = d' := by
  obtain ⟨he,hc⟩ := wrapping_component_all J hr hn V hV marked d hw
  obtain ⟨he',_⟩ := wrapping_component_all J hr hn V hV marked d' hw'
  obtain ⟨b,hb⟩ := Finset.card_pos.mp (show 0 < V.card by omega)
  have hbd : b ∈ componentBlocks J (by omega) hn V d := (Finset.ext_iff.mp he b).mpr hb
  have hbd' : b ∈ componentBlocks J (by omega) hn V d' := (Finset.ext_iff.mp he' b).mpr hb
  exact ((mem_componentBlocks J (by omega) hn V d b).mp hbd).2.symm.trans
    ((mem_componentBlocks J (by omega) hn V d' b).mp hbd').2

theorem vectorShift_agree {h g : J.Shifts n} {t : Vertex P E n}
    (he : J.AgreeAt h g t) : vectorShift J h t = vectorShift J g t := by
  cases t with
  | inl p => exact he
  | inr q => exact congrArg (fun b : Affine.Bit => fun _ : Fin 1 => b) he

theorem potentialValues_shift_agree (marked : Fin r) (h g : J.Shifts n)
    (M : Potentials (n := n) J) (a : Readout r n P E)
    (ha : J.AgreeAt h g (end0 J a).2.1) :
    potentialValues J marked h M a = potentialValues J marked g M a := by
  cases a with
  | inl x =>
    change J.AgreeAt h g x.type at ha
    simp only [potentialValues, vectorShift_agree J ha]
  | inr _ => rfl

theorem potentialValues_potentials_agree (marked : Fin r) (h : J.Shifts n)
    (M N : Potentials (n := n) J) (a : Readout r n P E)
    (he0 : M (end0 J a) = N (end0 J a)) (he1 : M (end1 J a) = N (end1 J a)) :
    potentialValues J marked h M a = potentialValues J marked h N a := by
  cases a with
  | inl x => simp only [potentialValues, end0, end1] at he0 he1 ⊢; rw [he0,he1]
  | inr y => simp only [potentialValues, end0, end1] at he0 he1 ⊢; rw [he0,he1]

theorem readout_type_mem {b : RawBlock r n P E} {a : Readout r n P E}
    (ha : HasReadout J b a) : (end0 J a).2.1 ∈ typesOf J b := by
  classical
  cases b with
  | inl h => cases ha; simp [typesOf, end0]
  | inr s =>
    rcases ha with rfl | rfl | rfl | rfl <;>
      simp [typesOf, end0, squareLeft, squareRight, squareBottom, squareTop]

abbrev ReadoutValues := ∀ a : Readout r n P E, ReadoutValue J a

def OffsetFamily (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (U : Finset (Block (n := n) J)) (F : ReadoutValues (n := n) J) : Prop :=
  ∃ cut : E → Fin (n+1), Avoids J cut U ∧
  ∃ h : (diagram J (by omega) hn U).ConnectedComponent → J.Shifts n,
  ∃ M : Potentials (n := n) J,
    (∀ c, Admissible J hr hn marked Q cut (componentBlocks J (by omega) hn U c) (h c)) ∧
    ∀ b ∈ U, ∀ a, HasReadout J b.val a →
      F a = potentialValues J marked (h ((diagram J (by omega) hn U).connectedComponentMk
        (anchor J b.val))) M a

def representedValues (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
    (U : Finset (Block (n := n) J))
    (h : (diagram J hr hn U).ConnectedComponent → J.Shifts n)
    (M : Potentials (n := n) J) : ReadoutValues (n := n) J :=
  fun a => potentialValues J marked (h ((diagram J hr hn U).connectedComponentMk (end0 J a))) M a

theorem representedValues_on_block (hr : 2 ≤ r) (hn : 0 < n) (marked : Fin r)
    (U : Finset (Block (n := n) J))
    (h : (diagram J hr hn U).ConnectedComponent → J.Shifts n)
    (M : Potentials (n := n) J) {b : Block (n := n) J} (hb : b ∈ U)
    {a : Readout r n P E} (ha : HasReadout J b.val a) :
    representedValues J hr hn marked U h M a =
      potentialValues J marked (h ((diagram J hr hn U).connectedComponentMk (anchor J b.val))) M a := by
  unfold representedValues
  rw [← (readout_component J hr hn U hb ha).1]

theorem offsetFamily_nonempty (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U : Finset (Block (n := n) J)) (hU : U.card ≤ r+1) :
    ∃ F : ReadoutValues (n := n) J, OffsetFamily J hr hn marked Q U F := by
  classical
  obtain ⟨cut,hcut⟩ := exists_unused_cut (supportLinks J U)
    (lt_of_le_of_lt ((supportLinks_card J U).trans hU) hlarge)
  have hc : Avoids J cut U := by
    intro l hl he
    exact hcut l.1 (by simpa only [← he,Prod.eta] using hl)
  have hex (c : (diagram J (by omega) hn U).ConnectedComponent) :=
    admissible_exists J hr hn marked Q (componentBlocks J (by omega) hn U c)
      (component_support_connected J (by omega) hn U c)
      ((Finset.card_le_card (componentBlocks_subset J (by omega) hn U c)).trans hU)
      cut (avoids_mono J (componentBlocks_subset J (by omega) hn U c) hc)
  choose h hh using hex
  refine ⟨representedValues J (by omega) hn marked U h (fun _ => 0), cut,hc,h,(fun _ => 0),hh,?_⟩
  exact fun b hb a ha => representedValues_on_block J (by omega) hn marked U h _ hb ha
end VariableWL.Blocks

end OAI
