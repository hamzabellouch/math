import Mathlib.Algebra.Order.AbsoluteValue.Basic
import Mathlib.Data.Rat.Floor
import Mathlib.Data.Int.Interval
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace OAI

/-! The slope-label multiplicity assumption in §2 of the manuscript
gives a uniform number of labels active at a fixed source direction.
This includes vector-valued selectors: taking the union over all bin
components does not increase the count.  The last lemmas split the
active labels at every scale into a fixed finite set of lattice slots. -/

noncomputable section

open scoped BigOperators

namespace LipschitzHilbert.SourceSlopeLabels

attribute [local instance] Classical.propDecidable

variable {ι : Type*}

/-- The source's local label multiplicity, using half-open intervals
to assign boundary labels unambiguously. -/
def LocalMultiplicity (labels : Finset ι) (slope : ι → ℝ) (d : ℝ) (M : ℕ) : Prop :=
  ∀ a : ℝ, (labels.filter (fun i => a ≤ slope i ∧ slope i < a + d)).card ≤ M

/-- All labels whose slope lies in the indicated reference window. -/
def window (labels : Finset ι) (slope : ι → ℝ) (t d radius : ℝ) : Finset ι := by
  classical
  exact labels.filter (fun i => |slope i - t| ≤ radius * d)

theorem window_card_le (labels : Finset ι) (slope : ι → ℝ)
    {t d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K) :
    (window labels slope t d radius).card ≤ (2 * K + 1) * M := by
  classical
  let active := window labels slope t d radius
  let bin : ι → ℤ := fun i => ⌊(slope i - t) / d⌋
  let bins : Finset ℤ := Finset.Icc (-(K : ℤ)) K
  have hmaps : (active : Set ι).MapsTo bin bins := by
    intro i hi
    have hwin : |slope i - t| ≤ radius * d := (Finset.mem_filter.mp hi).2
    have habs : |slope i - t| ≤ (K : ℝ) * d :=
      hwin.trans (mul_le_mul_of_nonneg_right hK hd.le)
    obtain ⟨hlo, hhi⟩ := abs_le.mp habs
    have hlow : -(K : ℝ) ≤ (slope i - t) / d := by
      apply (le_div_iff₀ hd).mpr
      linarith
    have hupp : (slope i - t) / d < (K : ℝ) + 1 := by
      apply (div_lt_iff₀ hd).mpr
      nlinarith
    exact Finset.mem_Icc.mpr ⟨Int.le_floor.mpr (by simpa using hlow),
      Int.floor_le_iff.mpr (by simpa using hupp)⟩
  have hfiber (b : ℤ) : (active.filter (fun i => bin i = b)).card ≤ M := by
    apply (Finset.card_le_card (show active.filter (fun i => bin i = b) ⊆
      labels.filter (fun i => t + (b : ℝ) * d ≤ slope i ∧
        slope i < (t + (b : ℝ) * d) + d) from ?_)).trans
      (hlocal (t + (b : ℝ) * d))
    intro i hi
    obtain ⟨hia, hib⟩ := Finset.mem_filter.mp hi
    have hil : i ∈ labels := (Finset.mem_filter.mp hia).1
    have h0 := Int.floor_le ((slope i - t) / d)
    have h1 := Int.lt_floor_add_one ((slope i - t) / d)
    change ⌊(slope i - t) / d⌋ = b at hib
    rw [hib] at h0 h1
    have h0' := (le_div_iff₀ hd).mp h0
    have h1' := (div_lt_iff₀ hd).mp h1
    exact Finset.mem_filter.mpr ⟨hil, by constructor <;> nlinarith⟩
  have hcount : bins.card = 2 * K + 1 := by
    have hcount' : (bins.card : ℤ) = 2 * (K : ℤ) + 1 := by
      dsimp [bins]
      rw [Int.card_Icc_of_le (a := -(K : ℤ)) (b := (K : ℤ)) (by omega)]
      omega
    exact_mod_cast hcount'
  calc
    active.card = ∑ b ∈ bins, (active.filter (fun i => bin i = b)).card :=
      Finset.card_eq_sum_card_fiberwise hmaps
    _ ≤ ∑ _b ∈ bins, M := Finset.sum_le_sum fun b _ => hfiber b
    _ = (2 * K + 1) * M := by simp [hcount]

/-- Active labels for any number of components. The selector support
is common to the label, so the bound has no component-count factor. -/
def active (labels : Finset ι) {κ : Type*} (selector : ι → κ → ℝ → ℂ)
    (t : ℝ) : Finset ι := by
  classical
  exact labels.filter (fun i => ∃ k, selector i k t ≠ 0)

theorem active_card_le (labels : Finset ι) (slope : ι → ℝ)
    {κ : Type*} (selector : ι → κ → ℝ → ℂ)
    {t d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K)
    (hsupport : ∀ i ∈ labels, ∀ k, selector i k t ≠ 0 →
      |t - slope i| ≤ radius * d) :
    (active labels selector t).card ≤ (2 * K + 1) * M := by
  classical
  apply (Finset.card_le_card (show active labels selector t ⊆
    window labels slope t d radius from ?_)).trans
    (window_card_le labels slope hd hlocal hK)
  intro i hi
  obtain ⟨hil, k, hk⟩ := Finset.mem_filter.mp hi
  exact Finset.mem_filter.mpr ⟨hil, by simpa only [abs_sub_comm] using hsupport i hil k hk⟩

/-- For coefficient errors the original and frozen selectors contribute
at most twice the same absolute label bound. -/
theorem active_union_card_le (labels : Finset ι) (slope : ι → ℝ)
    {κ : Type*} (selector : ι → κ → ℝ → ℂ)
    {t u d radius : ℝ} {M K : ℕ} (hd : 0 < d)
    (hlocal : LocalMultiplicity labels slope d M) (hK : radius ≤ K)
    (hsupport : ∀ i ∈ labels, ∀ k x, selector i k x ≠ 0 →
      |x - slope i| ≤ radius * d) :
    ((active labels selector u) ∪ (active labels selector t)).card ≤
      2 * ((2 * K + 1) * M) := by
  classical
  calc
    _ ≤ (active labels selector u).card + (active labels selector t).card :=
      Finset.card_union_le _ _
    _ ≤ (2 * K + 1) * M + (2 * K + 1) * M := Nat.add_le_add
      (active_card_le labels slope selector hd hlocal hK (fun i hi k => hsupport i hi k u))
      (active_card_le labels slope selector hd hlocal hK (fun i hi k => hsupport i hi k t))
    _ = _ := by omega

/-- Each scale has its own label assignment, but the same finite set of
slots suffices for all scales. Inactive slots may be represented by an
empty spatial lattice. -/
def slots {J : Type*} {Label : J → Type*} (labels : ∀ j, Finset (Label j))
    {B : ℕ} (hcard : ∀ j, (labels j).card ≤ B) (j : J) : labels j ↪ Fin B := by
  classical
  exact Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hcard j))

theorem slots_injective {J : Type*} {Label : J → Type*}
    (labels : ∀ j, Finset (Label j)) {B : ℕ}
    (hcard : ∀ j, (labels j).card ≤ B) (j : J) :
    Function.Injective (slots labels hcard j) := (slots labels hcard j).injective

/-- A slot contains at most one active label at a given scale. -/
theorem slot_fiber_card_le_one {J : Type*} {Label : J → Type*}
    (labels : ∀ j, Finset (Label j)) {B : ℕ}
    (hcard : ∀ j, (labels j).card ≤ B) (j : J) (b : Fin B) :
    (Finset.univ.filter (fun i : labels j => slots labels hcard j i = b)).card ≤ 1 := by
  classical
  apply Finset.card_le_one.mpr
  intro i hi k hk
  exact slots_injective labels hcard j
    ((Finset.mem_filter.mp hi).2.trans (Finset.mem_filter.mp hk).2.symm)

/-- Exact splitting of a finite packet sum into its label slots. -/
theorem sum_slots {J : Type*} {Label : J → Type*}
    (labels : ∀ j, Finset (Label j)) {B : ℕ}
    (hcard : ∀ j, (labels j).card ≤ B) {E : Type*} [AddCommMonoid E]
    (j : J) (f : Label j → E) :
    ∑ i ∈ labels j, f i =
      ∑ b : Fin B, ∑ i : labels j, if slots labels hcard j i = b then f i else 0 := by
  classical
  rw [Finset.sum_comm]
  simpa using (Finset.sum_attach (labels j) f).symm

/-- Recover the optional label for a slot without choosing any
distinguished label at an empty scale. -/
def labelAtSlot {A : Type*} {B : ℕ} (e : A ↪ Fin B) (b : Fin B) : Option A :=
  if h : ∃ i, e i = b then some h.choose else none

theorem labelAtSlot_at {A : Type*} {B : ℕ} (e : A ↪ Fin B) (i : A) :
    labelAtSlot e (e i) = some i := by
  classical
  unfold labelAtSlot
  split_ifs with h
  · congr 1
    exact e.injective h.choose_spec
  · exact (h ⟨i, rfl⟩).elim

theorem labelAtSlot_eq_some {A : Type*} {B : ℕ} (e : A ↪ Fin B)
    (b : Fin B) (i : A) : labelAtSlot e b = some i ↔ e i = b := by
  classical
  constructor
  · unfold labelAtSlot
    split_ifs with h
    · intro hi
      have heq : h.choose = i := Option.some.inj hi
      simpa only [heq] using h.choose_spec
    · simp
  · intro hi
    rw [← hi]
    exact labelAtSlot_at e i

/-- The spatial items retained in one label slot at a fixed scale. -/
def SlotItem {A : Type*} {B : ℕ} (e : A ↪ Fin B) (Item : A → Type*) (b : Fin B) :=
  {p : Sigma Item // e p.1 = b}

theorem slotItem_label {A : Type*} {B : ℕ} (e : A ↪ Fin B)
    {Item : A → Type*} {b : Fin B} (p : SlotItem e Item b) :
    labelAtSlot e b = some p.1.1 :=
  (labelAtSlot_eq_some e b p.1.1).mpr p.2

/-- Although labels can have overlapping integer sites, one slot never
mixes two labels at a fixed scale. Its original spatial site map is
therefore injective, as required by the packet-family constructor. -/
theorem slotItem_site_injective {A : Type*} {B : ℕ} (e : A ↪ Fin B)
    {Item : A → Type*} (site : ∀ i, Item i → ℤ × ℤ)
    (hsite : ∀ i, Function.Injective (site i)) (b : Fin B) :
    Function.Injective (fun p : SlotItem e Item b => site p.1.1 p.1.2) := by
  rintro ⟨⟨i, u⟩, hi⟩ ⟨⟨j, v⟩, hj⟩ h
  have hij : i = j := e.injective (hi.trans hj.symm)
  subst j
  apply Subtype.ext
  exact congrArg (Sigma.mk i) (hsite i h)

end LipschitzHilbert.SourceSlopeLabels

end

end OAI
