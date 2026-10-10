import Mathlib

namespace OAI

/-!
# Ordered exhaustion of anchor groups

Once one mode is known, identical host rows within each group and distinct
pattern rows prevent repeated groups. The group order then forces the
selected group map to be the identity.
-/

universe uI uJ uR uC uG uL uT

namespace Problem348.AnchorGroups

/-- Distinct pattern rows force distinct selected group labels whenever equal
labels give identical rows against the selected columns. -/
theorem labels_injective {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC} {G : Type uG}
    (S : I → J → Bool) (A : R → C → Bool)
    (r : I → R) (c : J → C) (g : I → G)
    (hrows : Function.Injective S)
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (htwin : ∀ i i', g i = g i' → ∀ j,
      A (r i) (c j) = A (r i') (c j)) :
    Function.Injective g := by
  intro i i' h
  apply hrows
  funext j
  rw [← hcopy i j, ← hcopy i' j]
  exact htwin i i' h j

/-- Equal host rows belonging to a fixed twin class cannot both be selected
by a pattern with distinct rows. This applies both to anchor groups and to the
dummy block, even before a common mode has been established. -/
theorem same_twin_class_index_eq {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC}
    (S : I → J → Bool) (A : R → C → Bool)
    (r : I → R) (c : J → C) (P : R → Prop)
    (hrows : Function.Injective S)
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (htwin : ∀ x y, P x → P y → ∀ z, A x z = A y z)
    {i i' : I} (hi : P (r i)) (hi' : P (r i')) : i = i' := by
  apply hrows
  funext j
  rw [← hcopy i j, ← hcopy i' j]
  exact htwin (r i) (r i') hi hi' (c j)

/-- Before all selected positions are pinned, the partial anchor label is
already injective on the selected anchor positions. Nonanchor labels are not
required to be injective. -/
theorem partial_labels_injOn {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC} {L : Type uL}
    (S : I → J → Bool) (A : R → C → Bool)
    (r : I → R) (c : J → C) (label : R → Option L)
    (hrows : Function.Injective S)
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (htwin : ∀ x y l, label x = some l → label y = some l →
      ∀ z, A x z = A y z) :
    Set.InjOn (fun i => label (r i)) {i | ∃ l, label (r i) = some l} := by
  intro i hi i' _ heq
  obtain ⟨l, hl⟩ := hi
  have hl' : label (r i') = some l := heq.symm.trans hl
  apply hrows
  funext j
  rw [← hcopy i j, ← hcopy i' j]
  exact htwin (r i) (r i') l hl hl' (c j)

/-- At most one selected position belongs to any host row twin class. -/
theorem selected_twin_class_card_le_one {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC} [Fintype I]
    (S : I → J → Bool) (A : R → C → Bool)
    (r : I → R) (c : J → C) (P : R → Prop) [DecidablePred P]
    (hrows : Function.Injective S)
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (htwin : ∀ x y, P x → P y → ∀ z, A x z = A y z) :
    (Finset.univ.filter (fun i => P (r i))).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi i' hi'
  exact same_twin_class_index_eq S A r c P hrows hcopy htwin
    (Finset.mem_filter.mp hi).2 (Finset.mem_filter.mp hi').2

/-- Unit-vector incidences contribute at most one true entry per participating
mode after selected anchor groups have been shown distinct. This is the
counting bridge from the concrete mode-support bound to rigidity's sparsity
hypothesis. -/
theorem true_entries_le_supported_modes {I : Type uI} {T : Type uT} {G : Type uG}
    (selected : Finset I) (mode : I → T) (group : I → G)
    (entry : I → Bool) (support : Finset T)
    (hgroups : Set.InjOn (fun i => (mode i, group i)) (↑selected : Set I))
    (hunit : ∀ i ∈ selected, ∀ j ∈ selected,
      entry i = true → entry j = true → mode i = mode j → group i = group j)
    (hsupport : ∀ i ∈ selected, entry i = true → mode i ∈ support) :
    (selected.filter (fun i => entry i = true)).card ≤ support.card := by
  classical
  apply Finset.card_le_card_of_injOn mode
  · intro i hi
    obtain ⟨his, hie⟩ := Finset.mem_filter.mp hi
    exact hsupport i his hie
  · intro i hi j hj hij
    obtain ⟨his, hie⟩ := Finset.mem_filter.mp hi
    obtain ⟨hjs, hje⟩ := Finset.mem_filter.mp hj
    apply hgroups his hjs
    exact Prod.ext hij (hunit i his j hjs hie hje hij)

/-- An increasing injective enumeration of a finite ordered set is its
prescribed enumeration. -/
theorem monotone_injective_eq_id {I : Type uI} [LinearOrder I] [Finite I]
    (g : I → I) (hmono : Monotone g) (hinj : Function.Injective g) :
    ∀ i, g i = i := by
  let f : I →o I := ⟨g, hmono⟩
  have hf : f = OrderHom.id := OrderHom.eq_id_of_injective f hinj
  intro i
  exact congrArg (fun q : I →o I => q i) hf

/-- Ordered group exhaustion for a copied pattern with distinct rows. -/
theorem group_eq_index {I : Type uI} {J : Type uJ} {R : Type uR} {C : Type uC} [LinearOrder I] [Finite I]
    (S : I → J → Bool) (A : R → C → Bool)
    (r : I → R) (c : J → C) (g : I → I)
    (hrows : Function.Injective S)
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (htwin : ∀ i i', g i = g i' → ∀ j,
      A (r i) (c j) = A (r i') (c j))
    (hmono : Monotone g) : ∀ i, g i = i :=
  monotone_injective_eq_id g hmono
    (labels_injective S A r c g hrows hcopy htwin)

/-- Host-facing formulation: anchor labels record a mode and a group. Once
all selected rows are anchors of one mode, their group labels equal their
pattern indices. The column version follows by transposition. -/
theorem row_labels_eq {k : ℕ} {J : Type uJ} {R : Type uR} {C : Type uC} {T : Type uT} [LinearOrder R]
    (S : Fin k → J → Bool) (A : R → C → Bool)
    (label : R → Option (T × Fin k))
    (r : Fin k → R) (c : J → C) (t : T)
    (hr : StrictMono r)
    (hrows : Function.Injective S)
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (hmode : ∀ i, ∃ u, label (r i) = some (t, u))
    (htwin : ∀ x y u, label x = some (t, u) →
      label y = some (t, u) → ∀ z, A x z = A y z)
    (horder : ∀ x y u v, x < y → label x = some (t, u) →
      label y = some (t, v) → u ≤ v) :
    ∀ i, label (r i) = some (t, i) := by
  classical
  choose g hg using hmode
  have hmono : Monotone g := by
    intro i j hij
    rcases eq_or_lt_of_le hij with h | h
    · subst j
      exact le_rfl
    · exact horder (r i) (r j) (g i) (g j) (hr h) (hg i) (hg j)
  have heq : ∀ i, g i = i := group_eq_index S A r c g hrows hcopy
    (by
      intro i j hij z
      exact htwin (r i) (r j) (g i) (hg i) (hij ▸ hg j) (c z)) hmono
  intro i
  simpa only [heq i] using hg i

/-- Transposed host-facing formulation for the selected columns. -/
theorem column_labels_eq {k : ℕ} {I : Type uI} {R : Type uR} {C : Type uC} {T : Type uT} [LinearOrder C]
    (S : I → Fin k → Bool) (A : R → C → Bool)
    (label : C → Option (T × Fin k))
    (r : I → R) (c : Fin k → C) (t : T)
    (hc : StrictMono c)
    (hcols : Function.Injective (fun j i => S i j))
    (hcopy : ∀ i j, A (r i) (c j) = S i j)
    (hmode : ∀ j, ∃ v, label (c j) = some (t, v))
    (htwin : ∀ x y v, label x = some (t, v) →
      label y = some (t, v) → ∀ z, A z x = A z y)
    (horder : ∀ x y u v, x < y → label x = some (t, u) →
      label y = some (t, v) → u ≤ v) :
    ∀ j, label (c j) = some (t, j) := by
  exact row_labels_eq (fun j i => S i j) (fun y x => A x y)
    label c r t hc hcols (fun j i => hcopy i j) hmode htwin horder

end Problem348.AnchorGroups

end OAI
