import OAI.Combinatorics.VariableWL.BlockExtensions

namespace OAI

universe uVariable1 uVariable2 uVariable3 uVariable4 uVariable5 uVariable6 uVariable7 uVariable8 uVariable9 uVariable10

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance
variable {r n : ℕ} {P : Type uVariable1} {E : Type uVariable2} (J : ProductImages.Instance r P E)

theorem component_links_small (hr : 2 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (U : Finset (Block (n := n) J)) (hU : U.card ≤ r+1)
    (c : (diagram J hr hn U).ConnectedComponent) :
    (supportLinks J (componentBlocks J hr hn U c)).card < n+1 :=
  lt_of_le_of_lt ((supportLinks_card J _).trans
    ((Finset.card_le_card (componentBlocks_subset J hr hn U c)).trans hU)) hlarge

theorem offsetFamily_restrict (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U V : Finset (Block (n := n) J))
    (hU : U.card ≤ r+1) (hVU : V ⊆ U) {F : ReadoutValues (n := n) J}
    (hF : OffsetFamily J hr hn marked Q U F) : OffsetFamily J hr hn marked Q V F := by
  classical
  obtain ⟨cut,hc,h,M,hh,hF⟩ := hF
  refine ⟨cut,avoids_mono J hVU hc, fun d => h (componentMap J (by omega) hn hVU d),M,?_,?_⟩
  · intro d
    apply admissible_restrict J hr hn marked Q
      (componentBlocks J (by omega) hn U (componentMap J (by omega) hn hVU d))
      (componentBlocks J (by omega) hn V d)
      (componentBlocks_map_subset J (by omega) hn hVU d)
      (component_support_connected J (by omega) hn U _)
      (component_support_connected J (by omega) hn V d)
      (component_links_small J (by omega) hn hlarge U hU _) cut
      (avoids_mono J (componentBlocks_subset J (by omega) hn U _) hc)
    exact hh _
  · intro b hb a ha
    exact hF b (hVU hb) a ha

theorem choose_extension_shifts (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U V : Finset (Block (n := n) J))
    (hU : U.card ≤ r+1) (hV : V.card ≤ r) (hVU : V ⊆ U)
    (cut : E → Fin (n+1)) (hc : Avoids J cut U)
    (h : (diagram J (by omega) hn V).ConnectedComponent → J.Shifts n)
    (hh : ∀ d, Admissible J hr hn marked Q cut (componentBlocks J (by omega) hn V d) (h d)) :
    ∃ g : (diagram J (by omega) hn U).ConnectedComponent → J.Shifts n,
      (∀ c, Admissible J hr hn marked Q cut (componentBlocks J (by omega) hn U c) (g c)) ∧
      ∀ d, (rowDiagram J hr hn (componentBlocks J (by omega) hn V d)).Wraps marked →
        ∀ t ∈ supportTypes J (componentBlocks J (by omega) hn V d),
          J.AgreeAt (h d) (g (componentMap J (by omega) hn hVU d)) t := by
  classical
  have hex (c : (diagram J (by omega) hn U).ConnectedComponent) :
      ∃ g : J.Shifts n, Admissible J hr hn marked Q cut
          (componentBlocks J (by omega) hn U c) g ∧
        ∀ d : (diagram J (by omega) hn V).ConnectedComponent, componentMap J (by omega) hn hVU d = c →
          (rowDiagram J hr hn (componentBlocks J (by omega) hn V d)).Wraps marked →
          ∀ t ∈ supportTypes J (componentBlocks J (by omega) hn V d), J.AgreeAt (h d) g t := by
    by_cases he : ∃ d : (diagram J (by omega) hn V).ConnectedComponent, componentMap J (by omega) hn hVU d = c ∧
        (rowDiagram J hr hn (componentBlocks J (by omega) hn V d)).Wraps marked
    · obtain ⟨d,hd,hw⟩ := he
      have hsub : componentBlocks J (by omega) hn V d ⊆ componentBlocks J (by omega) hn U c := by
        rw [← hd]
        exact componentBlocks_map_subset J (by omega) hn hVU d
      obtain ⟨hall,hcard⟩ := wrapping_component_all J hr hn V hV marked d hw
      obtain ⟨g,hg,hagree⟩ := admissible_lift J hr hn marked Q
        (componentBlocks J (by omega) hn U c) (componentBlocks J (by omega) hn V d)
        hsub (component_support_connected J (by omega) hn U c)
        (component_support_connected J (by omega) hn V d)
        ((Finset.card_le_card (componentBlocks_subset J (by omega) hn U c)).trans hU)
        (component_links_small J (by omega) hn hlarge U hU c)
        ((congrArg Finset.card hall).trans hcard) hw cut
        (avoids_mono J (componentBlocks_subset J (by omega) hn U c) hc) (hh d)
      refine ⟨g,hg,?_⟩
      intro d' _ hw'
      have hdd := wrapping_component_unique J hr hn V hV marked hw hw'
      subst d'
      exact hagree
    · obtain ⟨g,hg⟩ := admissible_exists J hr hn marked Q
        (componentBlocks J (by omega) hn U c) (component_support_connected J (by omega) hn U c)
        ((Finset.card_le_card (componentBlocks_subset J (by omega) hn U c)).trans hU)
        cut (avoids_mono J (componentBlocks_subset J (by omega) hn U c) hc)
      exact ⟨g,hg, fun d hd hw => (he ⟨d,hd,hw⟩).elim⟩
  choose g hg hagree using hex
  exact ⟨g,hg,fun d hw => hagree _ d rfl hw⟩

theorem offsetFamily_extend_strict (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U V : Finset (Block (n := n) J))
    (hU : U.card ≤ r+1) (hV : V.card ≤ r) (hVU : V ⊆ U)
    {F : ReadoutValues (n := n) J} (hF : OffsetFamily J hr hn marked Q V F) :
    ∃ G : ReadoutValues (n := n) J, OffsetFamily J hr hn marked Q U G ∧
      ∀ b ∈ V, ∀ a, HasReadout J b.val a → G a = F a := by
  classical
  obtain ⟨cut₀,hc₀,h,M,hh,hF⟩ := hF
  obtain ⟨cut,hcut⟩ := exists_unused_cut (supportLinks J U)
    (lt_of_le_of_lt ((supportLinks_card J U).trans hU) hlarge)
  have hc : Avoids J cut U := by
    intro l hl he
    exact hcut l.1 (by simpa only [← he,Prod.eta] using hl)
  have hh' (d) : Admissible J hr hn marked Q cut (componentBlocks J (by omega) hn V d) (h d) :=
    admissible_cut_change J hr hn marked Q _ (component_support_connected J (by omega) hn V d)
      cut₀ cut (avoids_mono J (componentBlocks_subset J (by omega) hn V d) hc₀)
      (avoids_mono J ((componentBlocks_subset J (by omega) hn V d).trans hVU) hc) (hh d)
  obtain ⟨g,hg,hagree⟩ := choose_extension_shifts J hr hn hlarge marked Q U V hU hV hVU cut hc h hh'
  have hex (d : (diagram J (by omega) hn V).ConnectedComponent) :
      ∃ M' : Potentials (n := n) J, ∀ b ∈ componentBlocks J (by omega) hn V d,
        ∀ a, HasReadout J b.val a →
          potentialValues J marked (g (componentMap J (by omega) hn hVU d)) M' a =
            potentialValues J marked (h d) M a := by
    by_cases hw : (rowDiagram J hr hn (componentBlocks J (by omega) hn V d)).Wraps marked
    · refine ⟨M,?_⟩
      intro b hb a ha
      exact (potentialValues_shift_agree J marked (h d) (g (componentMap J (by omega) hn hVU d)) M a
        (hagree d hw _ (Finset.mem_biUnion.mpr ⟨b,hb,readout_type_mem J ha⟩))).symm
    · apply gauge_nonwrapping J hr hn _ marked (h d) (g (componentMap J (by omega) hn hVU d)) M
        (hh' d).1 _ hw
      intro l hl
      exact (hg _).1 l (supportLinks_mono J (componentBlocks_map_subset J (by omega) hn hVU d) hl)
  choose Ms hMs using hex
  let N : Potentials (n := n) J := fun v => Ms ((diagram J (by omega) hn V).connectedComponentMk v) v
  let G := representedValues J (by omega) hn marked U g N
  refine ⟨G,⟨cut,hc,g,N,hg,?_⟩,?_⟩
  · exact fun b hb a ha => representedValues_on_block J (by omega) hn marked U g N hb ha
  · intro b hb a ha
    let d := (diagram J (by omega) hn V).connectedComponentMk (anchor J b.val)
    have hb' : b ∈ componentBlocks J (by omega) hn V d :=
      (mem_componentBlocks J (by omega) hn V d b).mpr ⟨hb,rfl⟩
    obtain ⟨he0,he1⟩ := readout_component J (by omega) hn V hb ha
    have hN := potentialValues_potentials_agree J marked
      (g (componentMap J (by omega) hn hVU d)) N (Ms d) a
      (show N (end0 J a) = Ms d (end0 J a) by dsimp only [N,d]; rw [← he0])
      (show N (end1 J a) = Ms d (end1 J a) by dsimp only [N,d]; rw [← he1])
    change representedValues J (by omega) hn marked U g N a = F a
    rw [representedValues_on_block J (by omega) hn marked U g N (hVU hb) ha]
    exact hN.trans ((hMs d b hb' a ha).trans (hF b hb a ha).symm)

theorem offsetFamily_exact_projection (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U V : Finset (Block (n := n) J))
    (hU : U.card ≤ r+1) (hVU : V ⊆ U) {F : ReadoutValues (n := n) J} :
    OffsetFamily J hr hn marked Q V F ↔
      ∃ G : ReadoutValues (n := n) J, OffsetFamily J hr hn marked Q U G ∧
        ∀ b ∈ V, ∀ a, HasReadout J b.val a → G a = F a := by
  classical
  constructor
  · intro hF
    by_cases he : V = U
    · subst U
      exact ⟨F,hF,fun _ _ _ _ => rfl⟩
    · apply offsetFamily_extend_strict J hr hn hlarge marked Q U V hU _ hVU hF
      have hc := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hVU,he⟩)
      omega
  · rintro ⟨G,hG,hGF⟩
    obtain ⟨cut,hc,h,M,hh,hrep⟩ := offsetFamily_restrict J hr hn hlarge marked Q U V hU hVU hG
    exact ⟨cut,hc,h,M,hh,fun b hb a ha => (hGF b hb a ha).symm.trans (hrep b hb a ha)⟩
end VariableWL.Blocks

namespace VariableWL.Blocks
open scoped CharTwo
open Subdivision ProductImages.Instance VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable3} {E : Type uVariable4} (J : ProductImages.Instance r P E)

def RawValue : RawBlock r n P E → Type
  | .inl h => Value J h.type
  | .inr s => SquareVal (dimension J (left J.source s.link)) (dimension J (right J.target s.link))

instance rawValueAddCommGroup (b : RawBlock r n P E) : AddCommGroup (RawValue J b) := by
  cases b <;> dsimp only [RawValue] <;> infer_instance

noncomputable instance rawValueFintype (b : RawBlock r n P E) : Fintype (RawValue J b) := by
  cases b <;> dsimp only [RawValue] <;> infer_instance

def boundaryMap (b : RawBlock r n P E) : RawValue J b →+ Bit := by
  cases b with
  | inl h => exact 0
  | inr s =>
    exact { toFun := boundary (linkLeft J s.link) (linkRight J s.link)
            map_zero' := boundary_zero _ _
            map_add' := boundary_add _ _ }

def inhomogeneity (marked : Fin r) : RawBlock r n P E → Bit
  | .inl _ => 0
  | .inr s => marker marked s.row * linkConstant J s.link

def LegalValue (marked : Fin r) (ε : Bit) (b : RawBlock r n P E) (z : RawValue J b) : Prop :=
  boundaryMap J b z = ε * inhomogeneity J marked b

abbrev Valuation (marked : Fin r) (ε : Bit) (b : Block (n := n) J) :=
  {z : RawValue J b.val // LegalValue J marked ε b.val z}

noncomputable instance valuationFintype (marked : Fin r) (ε : Bit) (b : Block (n := n) J) :
    Fintype (Valuation J marked ε b) := Fintype.ofFinite _

theorem legal_zero (marked : Fin r) (b : RawBlock r n P E) :
    LegalValue J marked 0 b 0 := by simp [LegalValue]

theorem legal_nonempty (marked : Fin r) (ε : Bit) (b : RawBlock r n P E) :
    ∃ z : RawValue J b, LegalValue J marked ε b z := by
  cases b with
  | inl h => exact ⟨0,by simp [LegalValue, inhomogeneity, boundaryMap]⟩
  | inr s =>
    exact fiber_nonempty (linkLeft J s.link) (linkRight J s.link)
      (ε * (marker marked s.row * linkConstant J s.link))

def translateValuation (marked : Fin r) (b : Block (n := n) J)
    (ξ : Valuation J marked 1 b) : Valuation J marked 0 b ≃ Valuation J marked 1 b where
  toFun z := ⟨z.val + ξ.val, by
    change boundaryMap J b.val (z.val + ξ.val) = 1 * inhomogeneity J marked b.val
    rw [map_add,z.property,ξ.property,zero_mul,zero_add]⟩
  invFun z := ⟨z.val - ξ.val, by
    change boundaryMap J b.val (z.val - ξ.val) = 0 * inhomogeneity J marked b.val
    rw [map_sub,z.property,ξ.property,sub_self,zero_mul]⟩
  left_inv z := Subtype.ext (add_sub_cancel_right _ _)
  right_inv z := Subtype.ext (sub_add_cancel _ _)

def valueOfReadouts (F : ReadoutValues (n := n) J) : (b : RawBlock r n P E) → RawValue J b
  | .inl h => F (.inl h)
  | .inr s => ((F (.inl (squareLeft J s)), F (.inl (squareRight J s))),
      (F (.inr (squareBottom s)), F (.inr (squareTop s))))

def Carries (b : RawBlock r n P E) (z : RawValue J b)
    (a : Readout r n P E) (v : ReadoutValue J a) : Prop :=
  match b with
  | .inl h => a = .inl h ∧ HEq v z
  | .inr s =>
      (a = .inl (squareLeft J s) ∧ HEq v z.1.1) ∨
      (a = .inl (squareRight J s) ∧ HEq v z.1.2) ∨
      (a = .inr (squareBottom s) ∧ HEq v z.2.1) ∨
      (a = .inr (squareTop s) ∧ HEq v z.2.2)

theorem valueOfReadouts_carries (F : ReadoutValues (n := n) J)
    {b : RawBlock r n P E} {a : Readout r n P E} (ha : HasReadout J b a) :
    Carries J b (valueOfReadouts J F b) a (F a) := by
  cases b with
  | inl h => cases ha; exact ⟨rfl,HEq.rfl⟩
  | inr s =>
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inl ⟨rfl,HEq.rfl⟩
    · exact Or.inr (Or.inl ⟨rfl,HEq.rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl,HEq.rfl⟩))

theorem carries_hasReadout {b : RawBlock r n P E} {z : RawValue J b}
    {a : Readout r n P E} {v : ReadoutValue J a} (h : Carries J b z a v) : HasReadout J b a := by
  cases b with
  | inl _ => exact h.1
  | inr _ =>
    exact h.elim (fun h => Or.inl h.1)
      (fun h => h.elim (fun h => Or.inr (Or.inl h.1))
        (fun h => h.elim (fun h => Or.inr (Or.inr (Or.inl h.1)))
          (fun h => Or.inr (Or.inr (Or.inr h.1)))))

theorem carries_exists {b : RawBlock r n P E} (z : RawValue J b)
    {a : Readout r n P E} (ha : HasReadout J b a) : ∃ v, Carries J b z a v := by
  cases b with
  | inl h => cases ha; exact ⟨z,rfl,HEq.rfl⟩
  | inr s =>
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨z.1.1,Or.inl ⟨rfl,HEq.rfl⟩⟩
    · exact ⟨z.1.2,Or.inr (Or.inl ⟨rfl,HEq.rfl⟩)⟩
    · exact ⟨z.2.1,Or.inr (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩))⟩
    · exact ⟨z.2.2,Or.inr (Or.inr (Or.inr ⟨rfl,HEq.rfl⟩))⟩

theorem offsetFamily_legal (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (U : Finset (Block (n := n) J)) {F : ReadoutValues (n := n) J}
    (hF : OffsetFamily J hr hn marked Q U F) {b : Block (n := n) J} (hb : b ∈ U) :
    LegalValue J marked 1 b.val (valueOfReadouts J F b.val) := by
  obtain ⟨cut,hc,h,M,hh,hrep⟩ := hF
  let c := (diagram J (by omega) hn U).connectedComponentMk (anchor J b.val)
  have hbC : b ∈ componentBlocks J (by omega) hn U c :=
    (mem_componentBlocks J (by omega) hn U c b).mpr ⟨hb,rfl⟩
  have hsys := (hh c).1
  obtain ⟨b,hvalid⟩ := b
  cases b with
  | inl x => simp [LegalValue, boundaryMap, inhomogeneity]
  | inr s =>
    have hl := square_link_mem J (componentBlocks J (by omega) hn U c) hbC rfl
    have h0 := hrep ⟨.inr s,hvalid⟩ hb (.inl (squareLeft J s)) (Or.inl rfl)
    have h1 := hrep ⟨.inr s,hvalid⟩ hb (.inl (squareRight J s)) (Or.inr (Or.inl rfl))
    have h2 := hrep ⟨.inr s,hvalid⟩ hb (.inr (squareBottom s)) (Or.inr (Or.inr (Or.inl rfl)))
    have h3 := hrep ⟨.inr s,hvalid⟩ hb (.inr (squareTop s)) (Or.inr (Or.inr (Or.inr rfl)))
    change linkLeft J s.link (F (.inl (squareLeft J s))) +
      linkRight J s.link (F (.inl (squareRight J s))) + F (.inr (squareBottom s)) +
        F (.inr (squareTop s)) = 1 * (marker marked s.row * linkConstant J s.link)
    rw [h0,h1,h2,h3,one_mul]
    exact potential_square J marked (h c) M s (hsys s.link hl)

noncomputable def familyList (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (U : Finset (Block (n := n) J)) {F : ReadoutValues (n := n) J}
    (hF : OffsetFamily J hr hn marked Q U F) : ∀ b : ↑U, Valuation J marked 1 b.val :=
  fun b => ⟨valueOfReadouts J F b.val.val, offsetFamily_legal J hr hn marked Q U hF b.property⟩
end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable5} {E : Type uVariable6} (J : ProductImages.Instance r P E)

theorem valueOfReadouts_congr {b : RawBlock r n P E} {F G : ReadoutValues (n := n) J}
    (he : ∀ a, HasReadout J b a → F a = G a) : valueOfReadouts J F b = valueOfReadouts J G b := by
  cases b with
  | inl h => exact he _ rfl
  | inr s =>
    dsimp only [valueOfReadouts]
    rw [he _ (Or.inl rfl), he _ (Or.inr (Or.inl rfl)),
      he _ (Or.inr (Or.inr (Or.inl rfl))), he _ (Or.inr (Or.inr (Or.inr rfl)))]

def OffsetLists (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (U : Finset (Block (n := n) J)) : Set (∀ b : ↑U, Valuation J marked 1 b.val) :=
  {ξ | ∃ F : ReadoutValues (n := n) J, OffsetFamily J hr hn marked Q U F ∧
    ∀ b : ↑U, (ξ b).val = valueOfReadouts J F b.val.val}

def restrictList (marked : Fin r) {U V : Finset (Block (n := n) J)} (hVU : V ⊆ U)
    (ξ : ∀ b : ↑U, Valuation J marked 1 b.val) : ∀ b : ↑V, Valuation J marked 1 b.val :=
  fun b => ξ ⟨b.val,hVU b.property⟩

theorem offsetLists_nonempty (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U : Finset (Block (n := n) J)) (hU : U.card ≤ r+1) :
    (OffsetLists J hr hn marked Q U).Nonempty := by
  obtain ⟨F,hF⟩ := offsetFamily_nonempty J hr hn hlarge marked Q U hU
  exact ⟨familyList J hr hn marked Q U hF,F,hF,fun _ => rfl⟩

theorem exact_projection (hr : 3 ≤ r) (hn : 0 < n) (hlarge : r+1 < n+1)
    (marked : Fin r) (Q : J.Witness) (U V : Finset (Block (n := n) J))
    (hU : U.card ≤ r+1) (hVU : V ⊆ U) :
    restrictList J marked hVU '' OffsetLists J hr hn marked Q U = OffsetLists J hr hn marked Q V := by
  ext ξ
  constructor
  · rintro ⟨η,⟨F,hF,hη⟩,rfl⟩
    exact ⟨F,offsetFamily_restrict J hr hn hlarge marked Q U V hU hVU hF,
      fun b => hη ⟨b.val,hVU b.property⟩⟩
  · rintro ⟨F,hF,hξ⟩
    obtain ⟨G,hG,hGF⟩ := (offsetFamily_exact_projection J hr hn hlarge marked Q U V hU hVU).mp hF
    refine ⟨familyList J hr hn marked Q U hG, ⟨G,hG,fun _ => rfl⟩,?_⟩
    funext b
    apply Subtype.ext
    exact (valueOfReadouts_congr J (fun a ha => hGF b.val b.property a ha)).trans (hξ b).symm
end VariableWL.Blocks

namespace VariableWL.Blocks
open Subdivision ProductImages.Instance VariableWL.Affine
variable {r n : ℕ} {P : Type uVariable7} {E : Type uVariable8} (J : ProductImages.Instance r P E)

instance readoutValueAddCommGroup (a : Readout r n P E) : AddCommGroup (ReadoutValue J a) := by
  cases a <;> dsimp only [ReadoutValue] <;> infer_instance

noncomputable instance readoutValueFintype (a : Readout r n P E) : Fintype (ReadoutValue J a) := by
  cases a <;> dsimp only [ReadoutValue] <;> infer_instance

theorem squareLeft_ne_right (hn : 0 < n) (s : Square r n E) :
    squareLeft J s ≠ squareRight J s := by
  intro h
  exact endpoints_ne hn J.source J.target s.link (congrArg Horizontal.type h)

theorem squareBottom_ne_top (hr : 2 ≤ r) (s : Square r n E) :
    squareBottom s ≠ squareTop s := by
  intro h
  exact Wrapping.finRotate_no_fixed hr s.row (congrArg Vertical.row h).symm

theorem carries_unique (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {z : RawValue J b} {a : Readout r n P E} {v w : ReadoutValue J a}
    (hv : Carries J b z a v) (hw : Carries J b z a w) : v = w := by
  cases b with
  | inl h => exact eq_of_heq (hv.2.trans hw.2.symm)
  | inr s =>
    have hlr := squareLeft_ne_right J hn s
    have hbt := squareBottom_ne_top hr s
    rcases hv with ⟨hv,hv'⟩ | ⟨hv,hv'⟩ | ⟨hv,hv'⟩ | ⟨hv,hv'⟩ <;>
      rcases hw with ⟨hw,hw'⟩ | ⟨hw,hw'⟩ | ⟨hw,hw'⟩ | ⟨hw,hw'⟩
    all_goals first | exact eq_of_heq (hv'.trans hw'.symm) | exfalso; aesop

noncomputable def readout {b : RawBlock r n P E} (z : RawValue J b)
    {a : Readout r n P E} (ha : HasReadout J b a) : ReadoutValue J a :=
  (carries_exists J z ha).choose

theorem readout_carries {b : RawBlock r n P E} (z : RawValue J b)
    {a : Readout r n P E} (ha : HasReadout J b a) : Carries J b z a (readout J z ha) :=
  (carries_exists J z ha).choose_spec

theorem readout_eq (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {z : RawValue J b} {a : Readout r n P E} (ha : HasReadout J b a)
    {v : ReadoutValue J a} (hv : Carries J b z a v) : readout J z ha = v :=
  carries_unique J hr hn (readout_carries J z ha) hv

theorem carries_add (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {z z' : RawValue J b} {a : Readout r n P E} {v v' : ReadoutValue J a}
    (hv : Carries J b z a v) (hv' : Carries J b z' a v') :
    Carries J b (z+z') a (v+v') := by
  cases b with
  | inl h =>
    obtain ⟨rfl,hv⟩ := hv
    have h₁ := eq_of_heq hv
    have h₂ := eq_of_heq hv'.2
    subst v; subst v'
    exact ⟨rfl,HEq.rfl⟩
  | inr s =>
    rcases hv with ⟨rfl,hv⟩ | ⟨rfl,hv⟩ | ⟨rfl,hv⟩ | ⟨rfl,hv⟩
    · have h₁ := eq_of_heq hv
      have h₂ := carries_unique J hr hn hv' (Or.inl ⟨rfl,HEq.rfl⟩)
      subst v; subst v'
      exact Or.inl ⟨rfl,HEq.rfl⟩
    · have h₁ := eq_of_heq hv
      have h₂ := carries_unique J hr hn hv' (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩))
      subst v; subst v'
      exact Or.inr (Or.inl ⟨rfl,HEq.rfl⟩)
    · have h₁ := eq_of_heq hv
      have h₂ := carries_unique J hr hn hv' (Or.inr (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩)))
      subst v; subst v'
      exact Or.inr (Or.inr (Or.inl ⟨rfl,HEq.rfl⟩))
    · have h₁ := eq_of_heq hv
      have h₂ := carries_unique J hr hn hv' (Or.inr (Or.inr (Or.inr ⟨rfl,HEq.rfl⟩)))
      subst v; subst v'
      exact Or.inr (Or.inr (Or.inr ⟨rfl,HEq.rfl⟩))

theorem readout_add (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    (z z' : RawValue J b) {a : Readout r n P E} (ha : HasReadout J b a) :
    readout J (z+z') ha = readout J z ha + readout J z' ha :=
  readout_eq J hr hn ha (carries_add J hr hn (readout_carries J z ha) (readout_carries J z' ha))

theorem readout_valueOfReadouts (hr : 2 ≤ r) (hn : 0 < n)
    (F : ReadoutValues (n := n) J) {b : RawBlock r n P E} {a : Readout r n P E}
    (ha : HasReadout J b a) : readout J (valueOfReadouts J F b) ha = F a :=
  readout_eq J hr hn ha (valueOfReadouts_carries J F ha)

theorem readout_zero (hr : 2 ≤ r) (hn : 0 < n) {b : RawBlock r n P E}
    {a : Readout r n P E} (ha : HasReadout J b a) : readout J 0 ha = 0 := by
  have h := readout_add J hr hn (0 : RawValue J b) 0 ha
  have hh : readout J 0 ha + readout J 0 ha = readout J 0 ha := by simpa using h.symm
  exact add_eq_left.mp hh

theorem offsetLists_agree (hr : 3 ≤ r) (hn : 0 < n) (marked : Fin r) (Q : J.Witness)
    (U : Finset (Block (n := n) J)) {ξ : ∀ b : ↑U, Valuation J marked 1 b.val}
    (hξ : ξ ∈ OffsetLists J hr hn marked Q U) (b c : ↑U)
    (a : Readout r n P E) (hb : HasReadout J b.val.val a) (hc : HasReadout J c.val.val a) :
    readout J (ξ b).val hb = readout J (ξ c).val hc := by
  obtain ⟨F,hF,hξ⟩ := hξ
  rw [hξ b, hξ c, readout_valueOfReadouts J (by omega) hn,
    readout_valueOfReadouts J (by omega) hn]
end VariableWL.Blocks

namespace VariableWL.Blocks
variable {r n : ℕ} {P : Type uVariable9} {E : Type uVariable10} [Fintype P] [Fintype E]

noncomputable instance horizontalFintype : Fintype (Horizontal r n P E) := by
  classical
  refine Fintype.ofInjective (fun h => (h.row,h.type,h.first,h.last)) ?_
  rintro ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩ h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  rfl

noncomputable instance verticalFintype : Fintype (Vertical r n E) := by
  classical
  refine Fintype.ofInjective (fun h => (h.row,h.link,h.label)) ?_
  rintro ⟨a,b,c⟩ ⟨a',b',c'⟩ h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl⟩
  rfl

noncomputable instance squareFintype : Fintype (Square r n E) := by
  classical
  refine Fintype.ofInjective (fun h => (h.row,h.link,h.first,h.last)) ?_
  rintro ⟨a,b,c,d⟩ ⟨a',b',c',d'⟩ h
  simp only [Prod.mk.injEq] at h
  rcases h with ⟨rfl,rfl,rfl,rfl⟩
  rfl

noncomputable instance blockFintype (J : ProductImages.Instance r P E) : Fintype (Block (n := n) J) :=
  Fintype.ofFinite _
end VariableWL.Blocks

end OAI
