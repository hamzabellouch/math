import OAI.Combinatorics.ProgressionColoring.OuterRows
import OAI.Combinatorics.ProgressionColoring.OuterRowRealBound
import OAI.Combinatorics.ProgressionColoring.OuterIncidence

namespace OAI

/-!
# The first family of outer-coloring tests

For each full word with sufficiently many light positions, choose the proved
cyclic row decomposition of its light positions. Its tests are the actual sets
of distinct labels occurring in these rows. All choices depend on the word and
the parameters, before a coloring is chosen.
-/

universe uLabel

namespace QuantitativeVanDerWaerden.OuterWordTests

open scoped BigOperators

variable {Label : Type uLabel} [Fintype Label] [DecidableEq Label] {k : ℕ}

/-- Full-word multiplicity of a label. -/
def multiplicity (word : Fin k → Label) (b : Label) : ℕ :=
  (Finset.univ.filter fun i => word i = b).card

/-- Lightness is measured in the full word, before restriction to light positions. -/
def lightPositions (M : ℕ) (word : Fin k → Label) : Finset (Fin k) :=
  Finset.univ.filter fun i => M * multiplicity word (word i) ≤ k

omit [Fintype Label] in
@[simp] theorem mem_lightPositions (M : ℕ) (word : Fin k → Label) (i : Fin k) :
    i ∈ lightPositions M word ↔ M * multiplicity word (word i) ≤ k := by
  simp [lightPositions]

abbrev LightPosition (M : ℕ) (word : Fin k → Label) := ↥(lightPositions M word)

/-- Each restricted label fibre is bounded by the full-word light multiplicity. -/
theorem light_fiber_card_le {Label : Type uLabel} [Fintype Label] [DecidableEq Label]
    {k : ℕ}
    (M : ℕ) (hM : 0 < M) (word : Fin k → Label)
    (b : Label) :
    Fintype.card {i : LightPosition M word // word i = b} ≤ k / M := by
  classical
  by_cases hb : Nonempty {i : LightPosition M word // word i = b}
  · obtain ⟨i⟩ := hb
    have hlight : M * multiplicity word b ≤ k := by
      have hi := (mem_lightPositions M word i.1).mp i.1.property
      simpa only [i.property] using hi
    have hcap : multiplicity word b ≤ k / M :=
      (Nat.le_div_iff_mul_le hM).mpr (by simpa only [Nat.mul_comm] using hlight)
    let emb : {i : LightPosition M word // word i = b} →
        {i : Fin k // word i = b} := fun i => ⟨i.1, i.2⟩
    have hemb : Function.Injective emb := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : {i : Fin k // word i = b} => z.val) hxy
    have hcard := Fintype.card_le_of_injective emb hemb
    have hcard' : Fintype.card {i : LightPosition M word // word i = b} ≤
        multiplicity word b := by simpa only [Fintype.card_subtype, multiplicity] using hcard
    exact hcard'.trans hcap
  · have : IsEmpty {i : LightPosition M word // word i = b} :=
      not_nonempty_iff.mp hb
    simp

/-- The actual row decomposition exists for each eligible full word. -/
theorem word_rows_exist (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (word : Fin k → Label) (heligible : k ≤ 10 * (lightPositions M word).card) :
    ∃ rows : Fin (k / M) → Finset (LightPosition M word),
      (∀ i, ∃! r, i ∈ rows r) ∧
      (∀ r, Set.InjOn (fun i : LightPosition M word => word i) (rows r)) ∧
      (∀ r, M / 10 ≤ (rows r).card) := by
  have hw : 0 < k / M := Nat.div_pos hMk hM
  have hwidth : M * (k / M) ≤ k := by
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self k M
  exact exists_light_row_finsets (fun i : LightPosition M word => word i)
    M (k / M) k hw (light_fiber_card_le M hM word) hwidth
    (by simpa using heligible)

noncomputable def wordRows (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (word : Fin k → Label) (heligible : k ≤ 10 * (lightPositions M word).card) :
    Fin (k / M) → Finset (LightPosition M word) :=
  Classical.choose (word_rows_exist M hM hMk word heligible)

theorem wordRows_spec (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (word : Fin k → Label) (heligible : k ≤ 10 * (lightPositions M word).card) :
    (∀ i, ∃! r, i ∈ wordRows M hM hMk word heligible r) ∧
    (∀ r, Set.InjOn (fun i : LightPosition M word => word i)
      (wordRows M hM hMk word heligible r)) ∧
    (∀ r, M / 10 ≤ (wordRows M hM hMk word heligible r).card) :=
  Classical.choose_spec (word_rows_exist M hM hMk word heligible)

def eligibleWords (M : ℕ) (words : Finset (Fin k → Label)) : Finset (Fin k → Label) :=
  words.filter fun word => k ≤ 10 * (lightPositions M word).card

abbrev TestIndex (M : ℕ) (words : Finset (Fin k → Label)) :=
  ↥(eligibleWords M words) × Fin (k / M)

omit [Fintype Label] in
theorem testIndex_card_le (M : ℕ) (words : Finset (Fin k → Label)) :
    Fintype.card (TestIndex M words) ≤ k * words.card := by
  classical
  calc
    Fintype.card (TestIndex M words) = (eligibleWords M words).card * (k / M) := by
      simp [TestIndex]
    _ ≤ words.card * k := Nat.mul_le_mul
      (Finset.card_le_card (Finset.filter_subset _ _)) (Nat.div_le_self k M)
    _ = k * words.card := Nat.mul_comm _ _

/-- Literal support of an indexed first-family row test. -/
noncomputable def support (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label)) (i : TestIndex M words) : Finset Label :=
  (wordRows M hM hMk i.1.val (Finset.mem_filter.mp i.1.property).2 i.2).image
    (fun p : LightPosition M i.1.val => i.1.val p)

theorem support_card_eq (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label)) (i : TestIndex M words) :
    (support M hM hMk words i).card =
      (wordRows M hM hMk i.1.val (Finset.mem_filter.mp i.1.property).2 i.2).card :=
  Finset.card_image_of_injOn
    ((wordRows_spec M hM hMk i.1.val (Finset.mem_filter.mp i.1.property).2).2.1 i.2)

theorem support_card_lower (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label)) (i : TestIndex M words) :
    M / 10 ≤ (support M hM hMk words i).card := by
  rw [support_card_eq]
  exact (wordRows_spec M hM hMk i.1.val (Finset.mem_filter.mp i.1.property).2).2.2 i.2

theorem support_card_real_lower (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label)) (i : TestIndex M words) :
    (M : ℝ) / 10 - 1 ≤ ((support M hM hMk words i).card : ℝ) :=
  real_div_ten_sub_one_le (support_card_lower M hM hMk words i)

omit [Fintype Label] in
/-- Restricting to the subtype of light positions does not change selected counts. -/
theorem light_selected_card (M : ℕ) (word : Fin k → Label) (p : Fin k → Prop)
    [DecidablePred p] :
    (Finset.univ.filter (fun i : LightPosition M word => p i)).card =
      ((lightPositions M word).filter p).card := by
  classical
  have himage :
      (Finset.univ.filter (fun i : LightPosition M word => p i)).image Subtype.val =
        (lightPositions M word).filter p := by
    ext i
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨a.property, ha⟩
    · rintro ⟨hi, hp⟩
      exact ⟨⟨i, hi⟩, hp, rfl⟩
  calc
    (Finset.univ.filter (fun i : LightPosition M word => p i)).card =
        ((Finset.univ.filter (fun i : LightPosition M word => p i)).image
          Subtype.val).card :=
      (Finset.card_image_of_injective _ Subtype.val_injective).symm
    _ = ((lightPositions M word).filter p).card := congrArg Finset.card himage

/-- Balancing every constructed support balances the light positions of each
eligible input word, with its original position multiplicities retained. -/
theorem supports_balance_words (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label)) (color : Label → Bool)
    (hbalance : ∀ i b, (support M hM hMk words i).card ≤
      4 * ((support M hM hMk words i).filter fun a => color a = b).card) :
    ∀ word ∈ words, k ≤ 10 * (lightPositions M word).card → ∀ b,
      (lightPositions M word).card ≤
        4 * ((lightPositions M word).filter fun i => color (word i) = b).card := by
  classical
  intro word hword heligible b
  let rows := wordRows M hM hMk word heligible
  have hrows := wordRows_spec M hM hMk word heligible
  have hrow : ∀ r, (rows r).card ≤
      4 * ((rows r).filter fun i : LightPosition M word => color (word i) = b).card := by
    intro r
    let i : TestIndex M words :=
      (⟨word, Finset.mem_filter.mpr ⟨hword, heligible⟩⟩, r)
    have hb := hbalance i b
    change ((rows r).image (fun p : LightPosition M word => word p)).card ≤
      4 * (((rows r).image (fun p : LightPosition M word => word p)).filter
        fun a => color a = b).card at hb
    have hinj : Set.InjOn (fun p : LightPosition M word => word p) (rows r) :=
      hrows.2.1 r
    have hinj' : Set.InjOn (fun p : LightPosition M word => word p)
        ((rows r).filter fun p : LightPosition M word => color (word p) = b) := by
      intro x hx y hy hxy
      exact hinj (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hy).1 hxy
    rw [Finset.card_image_of_injOn hinj, Finset.filter_image,
      Finset.card_image_of_injOn hinj'] at hb
    exact hb
  have hall := partition_balance_aggregate rows hrows.1
    (fun i : LightPosition M word => color (word i) = b) 4 hrow
  rw [Fintype.card_coe, light_selected_card M word (fun i => color (word i) = b)] at hall
  exact hall

/-- A first-family label-incident sum is bounded using the total test count.
The row index is retained even when supports happen to coincide. -/
theorem incident_weight_le (M : ℕ) (hM : 0 < M) (hMk : M ≤ k)
    (words : Finset (Fin k → Label)) (b : Label) :
    (∑ i ∈ Finset.univ.filter (fun i : TestIndex M words => b ∈ support M hM hMk words i),
        Real.exp (-((support M hM hMk words i).card : ℝ) / 32)) ≤
      ((k * words.card : ℕ) : ℝ) * Real.exp (-((M : ℝ) / 10 - 1) / 32) := by
  classical
  let incident := Finset.univ.filter
    (fun i : TestIndex M words => b ∈ support M hM hMk words i)
  have hcount : incident.card ≤ k * words.card :=
    (Finset.card_le_card (Finset.filter_subset _ _)).trans
      (by simpa using testIndex_card_le M words)
  calc
    (∑ i ∈ incident, Real.exp (-((support M hM hMk words i).card : ℝ) / 32)) ≤
        (incident.card : ℝ) * Real.exp (-((M : ℝ) / 10 - 1) / 32) :=
      outer_total_weight_bound incident (support M hM hMk words) _
        (fun i _ => support_card_real_lower M hM hMk words i)
    _ ≤ ((k * words.card : ℕ) : ℝ) * Real.exp (-((M : ℝ) / 10 - 1) / 32) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (Real.exp_pos _).le

end QuantitativeVanDerWaerden.OuterWordTests

end OAI
