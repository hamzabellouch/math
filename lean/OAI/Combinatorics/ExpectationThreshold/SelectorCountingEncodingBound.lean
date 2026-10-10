import OAI.Combinatorics.ExpectationThreshold.SelectorCountingEncoding
import OAI.Combinatorics.ExpectationThreshold.SelectorCountingEncodingRows
import OAI.Combinatorics.ExpectationThreshold.SelectorProfile

namespace OAI

/-!
# The fixed-profile encoding bound

Each actual coloring maps to the tuple of its changed row subsets and the
original colors on them. Reconstruction proves this map injective. The row
record permits arbitrary subsets of the fixed ambient sets, so overlap between
those ambient sets can only enlarge the number of records.
-/

noncomputable section
open scoped BigOperators

namespace TalagrandThreshold.Selector

variable {α : Type*} [Fintype α] [DecidableEq α] {s : ℕ}

omit [Fintype α] [DecidableEq α] in
/-- Restricting a labeling to a finite set counts exactly its fibers there. -/
theorem wordProfile_restrict_finset {H : Type*} [DecidableEq H]
    (U : Finset α) (f : α → H) (h : H) :
    wordProfile (fun x : ↥U => f x.val) h =
      (U.filter fun x => f x = h).card := by
  unfold wordProfile
  apply Finset.card_bij (fun x _ => x.val)
  · intro x hx
    exact Finset.mem_filter.mpr ⟨x.property, (Finset.mem_filter.mp hx).2⟩
  · intro x _ y _ hxy
    exact Subtype.ext hxy
  · intro x hx
    refine ⟨⟨x, (Finset.mem_filter.mp hx).1⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hx).2⟩

omit [DecidableEq α] in
/-- The recorded original labels have precisely the actual profile row. -/
theorem movedRow_wordProfile (a z : Coloring α s) (i : Fin s) :
    wordProfile (fun x : ↥(movedRow a z i) => a x.val) = profile a z i := by
  funext h
  rw [wordProfile_restrict_finset, profile_eq_card_filter_movedRow]

/-- The literal row record with its proved size and histogram constraints. -/
def profileRowEncoding (a z : Coloring α s) (n : Profile s)
    (R : Fin s → Finset α) (hn : profile a z = n)
    (hR : ∀ i, movedRow a z i ⊆ R i) (i : Fin s) :
    RowEncoding (R i) (rowCount n i) (n i) :=
  ⟨⟨movedRow a z i, hR i, by rw [movedRow_card_eq_rowCount, hn]⟩,
    ⟨fun x => a x.val, (mem_wordFiber _ _ _).mpr
      ((movedRow_wordProfile a z i).trans (congrFun hn i))⟩⟩

/-- Forgetting the constraints retains the actual changed subset and labels. -/
def rowEncodingForget {R : Finset α} {t : ℕ} {n : Color s → ℕ}
    (E : RowEncoding R t n) : RawRowEncoding α s :=
  ⟨E.1.val, E.2.val⟩

@[simp] theorem rowEncodingForget_profileRowEncoding
    (a z : Coloring α s) (n : Profile s) (R : Fin s → Finset α)
    (hn : profile a z = n) (hR : ∀ i, movedRow a z i ⊆ R i) (i : Fin s) :
    rowEncodingForget (profileRowEncoding a z n R hn hR i) =
      rawRowEncoding a z i := rfl

/-- Count actual originals of a fixed final coloring and profile. Every
injectivity and histogram condition is proved from the actual row encoding. -/
theorem card_le_profile_encoding
    (G : Finset (Coloring α s)) (z : Coloring α s) (n : Profile s)
    (R : Fin s → Finset α)
    (hEarlier : ∀ a ∈ G, Earlier a z)
    (hprofile : ∀ a ∈ G, profile a z = n)
    (hrows : ∀ a ∈ G, ∀ i, movedRow a z i ⊆ R i) :
    G.card ≤ ∏ i : Fin s,
      Nat.choose (R i).card (rowCount n i) * wordCount (rowCount n i) (n i) := by
  classical
  let encode : ↥G → ∀ i : Fin s, RowEncoding (R i) (rowCount n i) (n i) :=
    fun a => profileRowEncoding a.val z n R
      (hprofile a.val a.property) (hrows a.val a.property)
  have hinj : Function.Injective encode := by
    intro a b hab
    apply Subtype.ext
    apply rawRowEncoding_injective
      (hEarlier a.val a.property) (hEarlier b.val b.property)
    intro i
    have hi := congrArg (fun f => rowEncodingForget (f i)) hab
    simpa only [encode, rowEncodingForget_profileRowEncoding] using hi
  have hcard := Fintype.card_le_of_injective encode hinj
  simpa only [Fintype.card_coe, Fintype.card_pi, card_rowEncoding] using hcard

/-- Specialization to the actual selected bad originals in one profile group. -/
theorem groupOriginals_card_le_profile_encoding
    {F : Family α} (mu : MassFamily F) (z : Coloring α s) (n : Profile s)
    (R : Fin s → Finset α)
    (hrows : ∀ a ∈ groupOriginals mu z n, ∀ i, movedRow a z i ⊆ R i) :
    (groupOriginals mu z n).card ≤ ∏ i : Fin s,
      Nat.choose (R i).card (rowCount n i) * wordCount (rowCount n i) (n i) := by
  apply card_le_profile_encoding (groupOriginals mu z n) z n R
  · intro a ha
    obtain ⟨_, ⟨H₀, hmin⟩, _⟩ := (mem_groupOriginals mu a z n).mp ha
    exact hmin.1.1.1
  · intro a ha
    exact ((mem_groupOriginals mu a z n).mp ha).2.2
  · exact hrows

end TalagrandThreshold.Selector

end

end OAI
