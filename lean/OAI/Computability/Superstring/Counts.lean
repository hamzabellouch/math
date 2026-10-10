import OAI.Computability.Superstring.Hierarchical

namespace OAI

namespace Superstring

namespace Counts

variable {α : Type}

/-- A substring occurrence retains its starting position, so overlapping
occurrences are counted separately. -/
def Occurs (T s : List α) (x : ℕ) : Prop :=
  x + s.length ≤ T.length ∧ ∀ i : Fin s.length, T[x + i.val]? = s[i.val]?

instance [DecidableEq α] (T s : List α) (x : ℕ) : Decidable (Occurs T s x) :=
  inferInstanceAs (Decidable (_ ∧ ∀ _i : Fin s.length, _))

abbrev Occurrence (T s : List α) := {x : Fin (T.length + 1) // Occurs T s x.val}

def number [DecidableEq α] (T s : List α) : ℕ := Fintype.card (Occurrence T s)

theorem Occurs.at {T s : List α} {x i : ℕ} (h : Occurs T s x) (hi : i < s.length) :
    T[x + i]? = s[i]? := h.2 ⟨i, hi⟩

theorem Occurs.refl (s : List α) : Occurs s s 0 := by
  simp [Occurs]

theorem Occurs.trans {T r s : List α} {x j : ℕ}
    (hT : Occurs T r x) (hr : Occurs r s j) : Occurs T s (x + j) := by
  refine ⟨by have := hT.1; have := hr.1; omega, ?_⟩
  intro i
  have hi := i.isLt
  have hj : j + i.val < r.length := by have := hr.1; omega
  simpa only [Nat.add_assoc] using (hT.at hj).trans (hr.at hi)

theorem Occurs.infix {T s : List α} {x : ℕ} (h : Occurs T s x) : s <:+: T := by
  have heq : (T.drop x).take s.length = s := by
    apply List.ext_getElem?
    intro i
    by_cases hi : i < s.length
    · simpa only [List.getElem?_take, ite_eq_left hi, List.getElem?_drop] using h.at hi
    · simp only [List.getElem?_take, ite_eq_right hi]
      exact (List.getElem?_eq_none_iff.mpr (by omega)).symm
  rw [← heq]
  exact (List.take_prefix _ _).isInfix.trans (List.drop_suffix _ _).isInfix

theorem Occurs.unique {T r s : List α} {x : ℕ}
    (hr : Occurs T r x) (hs : Occurs T s x) (hlen : r.length = s.length) : r = s := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < r.length
  · exact (hr.at hi).symm.trans (hs.at (hlen ▸ hi))
  · rw [List.getElem?_eq_none_iff.mpr (by omega),
      List.getElem?_eq_none_iff.mpr (by omega)]

/-- The inner occurrence is strictly inside the two single-letter mismatches. -/
def Block (A : ℤ → α) (s r : List α) (j : ℕ) : Prop :=
  1 ≤ j ∧ j + s.length < r.length ∧ Occurs r s j ∧
    (∀ h : Fin r.length, 0 < h.val → h.val + 1 < r.length →
      r[h.val]? = some (A ((h.val : ℤ) - j))) ∧
    r[0]? ≠ some (A (-(j : ℤ))) ∧
    r[r.length - 1]? ≠ some (A (((r.length - 1 : ℕ) : ℤ) - j))

instance [DecidableEq α] (A : ℤ → α) (s r : List α) (j : ℕ) : Decidable (Block A s r j) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ (∀ _h : Fin r.length, _) ∧ _ ∧ _))

abbrev BlockPosition (A : ℤ → α) (s r : List α) :=
  {j : Fin (r.length + 1) // Block A s r j.val}

def coefficient [DecidableEq α] (A : ℤ → α) (s r : List α) : ℕ := Fintype.card (BlockPosition A s r)


def blocking [DecidableEq α] (V : Finset (List α)) (A : ℤ → α) (s : List α) (m : List α → ℕ) : ℕ :=
  ∑ r ∈ V, coefficient A s r * m r

namespace Block

variable {A : ℤ → α} {T s r : List α} {j x : ℕ}

theorem length_pos (h : Block A s r j) : 0 < r.length := by have := h.2.1; omega

theorem left (h : Block A s r j) (hT : Occurs T r x) :
    T[x]? ≠ some (A ((x : ℤ) - ((x + j : ℕ) : ℤ))) := by
  have hh := hT.at h.length_pos
  simp only [Nat.add_zero] at hh
  rw [hh]
  have heq : (x : ℤ) - ((x + j : ℕ) : ℤ) = -(j : ℤ) := by omega
  rw [heq]
  exact h.2.2.2.2.1

theorem right (h : Block A s r j) (hT : Occurs T r x) :
    T[x + r.length - 1]? ≠ some (A (((x + r.length - 1 : ℕ) : ℤ) - ((x + j : ℕ) : ℤ))) := by
  have hp := h.length_pos
  have hh := hT.at (i := r.length - 1) (by omega)
  have heq : x + (r.length - 1) = x + r.length - 1 := by omega
  rw [heq] at hh
  rw [hh]
  have heq : ((x + r.length - 1 : ℕ) : ℤ) - ((x + j : ℕ) : ℤ) =
      ((r.length - 1 : ℕ) : ℤ) - j := by omega
  rw [heq]
  exact h.2.2.2.2.2

theorem inside (h : Block A s r j) (hT : Occurs T r x) (t : ℕ)
    (hxt : x < t) (htr : t < x + r.length - 1) :
    T[t]? = some (A ((t : ℤ) - ((x + j : ℕ) : ℤ))) := by
  have hd : t - x < r.length := by omega
  have hh := h.2.2.2.1 ⟨t - x, hd⟩ (show 0 < t - x by omega)
    (show t - x + 1 < r.length by omega)
  change r[t - x]? = some (A (((t - x : ℕ) : ℤ) - j)) at hh
  have ht := hT.at hd
  have hx : x + (t - x) = t := by omega
  rw [hx] at ht
  rw [ht, hh]
  have heq : ((t - x : ℕ) : ℤ) - j = (t : ℤ) - ((x + j : ℕ) : ℤ) := by omega
  rw [heq]


theorem boundaries_unique {r' : List α} {j' x' : ℕ}
    (h : Block A s r j) (h' : Block A s r' j')
    (hT : Occurs T r x) (hT' : Occurs T r' x') (hx : x + j = x' + j') :
    x = x' ∧ r.length = r'.length := by
  have h₁ := h.1
  have h₂ := h.2.1
  have h₁' := h'.1
  have h₂' := h'.2.1
  have hstart : x = x' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hm := h'.left hT'
      have he := h.inside hT x' hlt (by omega)
      apply hm
      simpa only [hx] using he
    · have hm := h.left hT
      have he := h'.inside hT' x hgt (by omega)
      apply hm
      simpa only [hx] using he
  refine ⟨hstart, ?_⟩
  subst x'
  have hj : j = j' := by omega
  subst j'
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact h.right hT (h'.inside hT' (x + r.length - 1) (by omega) (by omega))
  · exact h'.right hT' (h.inside hT (x + r'.length - 1) (by omega) (by omega))

end Block

/-- A recorded bracketing word occurrence, and a counted placement inside it. -/
abbrev BlockWitness (V : Finset (List α)) (T : List α) (A : ℤ → α) (s : List α) :=
  Σ r : V, Occurrence T r.val × BlockPosition A s r.val

/-- The blocked-occurrence map. -/
def blockedOccurrence (V : Finset (List α)) (T : List α) (A : ℤ → α) (s : List α)
    (w : BlockWitness V T A s) : Occurrence T s :=
  let h := w.2.1.property.trans w.2.2.property.2.2.1
  ⟨⟨w.2.1.val.val + w.2.2.val.val, by have := h.1; omega⟩, h⟩

theorem blockedOccurrence_injective (V : Finset (List α)) (T : List α)
    (A : ℤ → α) (s : List α) : Function.Injective (blockedOccurrence V T A s) := by
  intro w w' heq
  rcases w with ⟨⟨r, hr⟩, ⟨⟨x, hxb⟩, hT⟩, ⟨⟨j, hjb⟩, hB⟩⟩
  rcases w' with ⟨⟨r', hr'⟩, ⟨⟨x', hxb'⟩, hT'⟩, ⟨⟨j', hjb'⟩, hB'⟩⟩
  have hxj := congrArg (fun o : Occurrence T s => o.val.val) heq
  change x + j = x' + j' at hxj
  obtain ⟨hxx, hlen⟩ := hB.boundaries_unique hB' hT hT' hxj
  change x = x' at hxx
  subst x'
  have hrr := hT.unique hT' hlen
  change r = r' at hrr
  subst r'
  have hjj : j = j' := by omega
  subst j'
  rfl

theorem card_blockWitness [DecidableEq α] (V : Finset (List α)) (T : List α)
    (A : ℤ → α) (s : List α) :
    Fintype.card (BlockWitness V T A s) = blocking V A s (number T) := by
  rw [blocking, Finset.sum_subtype V (fun _ => Iff.rfl)]
  simp only [BlockWitness, Fintype.card_sigma, Fintype.card_prod, number, coefficient]
  apply Finset.sum_congr rfl
  intro r _
  exact Nat.mul_comm _ _


theorem blocking_le_number [DecidableEq α] (V : Finset (List α)) (T : List α)
    (A : ℤ → α) (s : List α) : blocking V A s (number T) ≤ number T s := by
  rw [← card_blockWitness]
  exact Fintype.card_le_of_injective _ (blockedOccurrence_injective V T A s)

/-- Positivity of a coefficient forces the strict length dependency used in
both the descending recursion and its occurrence-bound induction. -/
theorem coefficient_pos_length [DecidableEq α] {A : ℤ → α} {s r : List α}
    (h : 0 < coefficient A s r) : s.length + 2 ≤ r.length := by
  obtain ⟨j⟩ := Fintype.card_pos_iff.mp h
  have h₁ := j.property.1
  have h₂ := j.property.2.1
  omega

/-- Agreement with a template at origin zero, as in every count rule. -/
def Matches (A : ℤ → α) (s : List α) : Prop :=
  ∀ i : Fin s.length, s[i.val]? = some (A i.val)

theorem periodic_nat_add {A : ℤ → α} {p : ℕ} (per : Function.Periodic A (p : ℤ))
    (t : ℕ) (x : ℤ) : A (x + (t * p : ℕ)) = A x := by
  simpa only [Nat.cast_mul] using per.nat_mul t x

theorem periodic_nat_sub {A : ℤ → α} {p : ℕ} (per : Function.Periodic A (p : ℤ))
    (t : ℕ) (x : ℤ) : A (x - (t * p : ℕ)) = A x := by
  simpa only [Nat.cast_mul] using (per.nat_mul t).sub_eq x

/-- All period-spaced prefixes of a rule's longer word are genuine occurrences. -/
theorem period_prefix {A : ℤ → α} {p t : ℕ} {v w : List α}
    (per : Function.Periodic A (p : ℤ)) (hv : Matches A v) (hw : Matches A w)
    (hlen : t * p + w.length ≤ v.length) : Occurs v w (t * p) := by
  refine ⟨hlen, ?_⟩
  intro i
  have hi := i.isLt
  have hit : t * p + i.val < v.length := by omega
  rw [hv ⟨t * p + i.val, hit⟩, hw i]
  have heq : ((t * p + i.val : ℕ) : ℤ) = (i.val : ℤ) + (t * p : ℕ) := by omega
  rw [heq, periodic_nat_add per]

/-- A bracketing placement of the long word generates every period-spaced
placement of its short prefix in the SAME bracketing word. -/
theorem Block.shift {A : ℤ → α} {p t j : ℕ} {v w r : List α}
    (h : Block A v r j) (per : Function.Periodic A (p : ℤ))
    (hv : Matches A v) (hw : Matches A w) (hlen : t * p + w.length ≤ v.length) :
    Block A w r (j + t * p) := by
  refine ⟨by have := h.1; omega, by have := h.2.1; omega,
    h.2.2.1.trans (period_prefix per hv hw hlen), ?_, ?_, ?_⟩
  · intro i hi hi'
    rw [h.2.2.2.1 i hi hi']
    have heq : (i.val : ℤ) - ((j + t * p : ℕ) : ℤ) =
        ((i.val : ℤ) - j) - (t * p : ℕ) := by omega
    rw [heq, periodic_nat_sub per]
  · have heq : -((j + t * p : ℕ) : ℤ) = -(j : ℤ) - (t * p : ℕ) := by omega
    rw [heq, periodic_nat_sub per]
    exact h.2.2.2.2.1
  · have heq : ((r.length - 1 : ℕ) : ℤ) - ((j + t * p : ℕ) : ℤ) =
        (((r.length - 1 : ℕ) : ℤ) - j) - (t * p : ℕ) := by omega
    rw [heq, periodic_nat_sub per]
    exact h.2.2.2.2.2

/-- Coefficient amplification for occurrence counts. -/
theorem coefficient_amplification [DecidableEq α] {A : ℤ → α} {p k : ℕ}
    {v w r : List α} (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (hv : Matches A v) (hw : Matches A w) (hlen : w.length + k * p = v.length)
    (hb : 0 < coefficient A v r) : k + 1 ≤ coefficient A w r := by
  obtain ⟨j⟩ := Fintype.card_pos_iff.mp hb
  have hbound (t : Fin (k + 1)) : t.val * p + w.length ≤ v.length := by
    have ht := Nat.mul_le_mul_right p (show t.val ≤ k by omega)
    omega
  let f : Fin (k + 1) → BlockPosition A w r := fun t =>
    ⟨⟨j.val.val + t.val * p, by have := j.property.2.1; have := hbound t; omega⟩,
      j.property.shift per hv hw (hbound t)⟩
  have hinj : Function.Injective f := by
    intro t u heq
    have hh := congrArg (fun b : BlockPosition A w r => b.val.val) heq
    change j.val.val + t.val * p = j.val.val + u.val * p at hh
    apply Fin.ext
    nlinarith
  simpa only [Fintype.card_fin, coefficient] using Fintype.card_le_of_injective f hinj

/-- Restrict an occurrence through another containing occurrence. -/
theorem Occurs.factor {T r v : List α} {x y : ℕ}
    (hr : Occurs T r y) (hv : Occurs T v x) (hyx : y ≤ x)
    (hend : x + v.length ≤ y + r.length) : Occurs r v (x - y) := by
  refine ⟨by omega, ?_⟩
  intro i
  have hi := i.isLt
  have hridx : x - y + i.val < r.length := by omega
  have hh := hr.at hridx
  have heq : y + (x - y + i.val) = x + i.val := by omega
  rw [heq] at hh
  exact hh.symm.trans (hv.at hi)

/-- Retarget a block by a whole number of template periods, when the enlarged
inner occurrence still lies strictly between the same mismatch letters. -/
theorem Block.expand {A : ℤ → α} {p t j j' : ℕ} {v w r : List α}
    (h : Block A w r j) (per : Function.Periodic A (p : ℤ)) (hj : j = j' + t * p)
    (hj' : 1 ≤ j') (hlen : j' + v.length < r.length) (hr : Occurs r v j') :
    Block A v r j' := by
  have phase (z : ℤ) : A (z - j) = A (z - j') := by
    have heq : z - j = (z - j') - (t * p : ℕ) := by omega
    rw [heq, periodic_nat_sub per]
  refine ⟨hj', hlen, hr, ?_, ?_, ?_⟩
  · intro i hi hi'
    exact (h.2.2.2.1 i hi hi').trans (congrArg some (phase i.val))
  · have he := phase 0
    simp only [zero_sub] at he
    rw [← he]
    exact h.2.2.2.2.1
  · rw [← phase (r.length - 1 : ℕ)]
    exact h.2.2.2.2.2

/-- A blocking pair around a period-spaced short occurrence inside a matching
long word must lie outside that entire long occurrence, and blocks it too. -/
theorem Block.encloses_matching {A : ℤ → α} {T v w r : List α} {p t x y j : ℕ}
    (h : Block A w r j) (hr : Occurs T r y) (hv : Occurs T v x)
    (hmatch : Matches A v) (per : Function.Periodic A (p : ℤ))
    (hlen : t * p + w.length ≤ v.length) (hpos : y + j = x + t * p) :
    ∃ j', Block A v r j' ∧ y + j' = x := by
  have hj := h.1
  have hend := h.2.1
  have hleft : y < x := by
    by_contra hnot
    have hxy : x ≤ y := by omega
    have hiy : y - x < v.length := by omega
    have ht := hv.at hiy
    have heq : x + (y - x) = y := by omega
    rw [heq] at ht
    have hm := h.left hr
    apply hm
    rw [ht, hmatch ⟨y - x, hiy⟩]
    have heq : (y : ℤ) - ((y + j : ℕ) : ℤ) =
        ((y - x : ℕ) : ℤ) - (t * p : ℕ) := by omega
    rw [heq, periodic_nat_sub per]
  have hright : x + v.length ≤ y + r.length - 1 := by
    by_contra hnot
    have hxe : x ≤ y + r.length - 1 := by omega
    have hie : y + r.length - 1 - x < v.length := by omega
    have ht := hv.at hie
    have heq : x + (y + r.length - 1 - x) = y + r.length - 1 := by omega
    rw [heq] at ht
    have hm := h.right hr
    apply hm
    rw [ht, hmatch ⟨y + r.length - 1 - x, hie⟩]
    have heq : ((y + r.length - 1 : ℕ) : ℤ) - ((y + j : ℕ) : ℤ) =
        ((y + r.length - 1 - x : ℕ) : ℤ) - (t * p : ℕ) := by omega
    rw [heq, periodic_nat_sub per]
  refine ⟨x - y, h.expand (t := t) per (by omega) (by omega) (by omega)
    (hr.factor hv (by omega) (by omega)), by omega⟩

/-- A period-spaced suboccurrence of a fixed long occurrence. -/
def periodOccurrence {A : ℤ → α} {T v w : List α} {p k : ℕ}
    (per : Function.Periodic A (p : ℤ)) (hv : Matches A v) (hw : Matches A w)
    (hlen : w.length + k * p = v.length) (o : Occurrence T v) (t : Fin (k + 1)) :
    Occurrence T w :=
  let ht : t.val * p + w.length ≤ v.length := by
    have := Nat.mul_le_mul_right p (show t.val ≤ k by omega)
    omega
  let h := o.property.trans (period_prefix per hv hw ht)
  ⟨⟨o.val.val + t.val * p, by have := h.1; omega⟩, h⟩

theorem periodOccurrence_injective {A : ℤ → α} {T v w : List α} {p k : ℕ}
    (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (hv : Matches A v) (hw : Matches A w)
    (hlen : w.length + k * p = v.length) (o : Occurrence T v) :
    Function.Injective (periodOccurrence per hv hw hlen o) := by
  intro t u heq
  have hh := congrArg (fun b : Occurrence T w => b.val.val) heq
  change o.val.val + t.val * p = o.val.val + u.val * p at hh
  apply Fin.ext
  nlinarith


def Unblocked (V : Finset (List α)) (T : List α) (A : ℤ → α) (v : List α)
    (o : Occurrence T v) : Prop := ∀ b, blockedOccurrence V T A v b ≠ o

theorem Unblocked.period_prefix {V : Finset (List α)} {A : ℤ → α}
    {T v w : List α} {p k : ℕ} (per : Function.Periodic A (p : ℤ))
    (hv : Matches A v) (hw : Matches A w) (hlen : w.length + k * p = v.length)
    {o : Occurrence T v} (ho : Unblocked V T A v o) (t : Fin (k + 1)) :
    Unblocked V T A w (periodOccurrence per hv hw hlen o t) := by
  intro b heq
  have hh := congrArg (fun q : Occurrence T w => q.val.val) heq
  change b.2.1.val.val + b.2.2.val.val = o.val.val + t.val * p at hh
  have hbound : t.val * p + w.length ≤ v.length := by
    have := Nat.mul_le_mul_right p (show t.val ≤ k by omega)
    omega
  obtain ⟨j', hj', hpos⟩ := b.2.2.property.encloses_matching b.2.1.property
    o.property hv per hbound hh
  let b' : BlockWitness V T A v := ⟨b.1, b.2.1,
    ⟨⟨j', by have := hj'.2.1; omega⟩, hj'⟩⟩
  apply ho b'
  apply Subtype.ext
  apply Fin.ext
  exact hpos


theorem unblocked_count_growth [DecidableEq α] {V : Finset (List α)} {A : ℤ → α}
    {T v w : List α} {p k : ℕ} (hp : 0 < p) (per : Function.Periodic A (p : ℤ))
    (hv : Matches A v) (hw : Matches A w) (hlen : w.length + k * p = v.length)
    (hmore : blocking V A v (number T) < number T v) :
    blocking V A w (number T) + k + 1 ≤ number T w := by
  classical
  have hex : ∃ o : Occurrence T v, Unblocked V T A v o := by
    by_contra hnot
    simp only [Unblocked, not_exists, not_forall, ne_eq, not_not] at hnot
    have hc := Fintype.card_le_of_surjective (blockedOccurrence V T A v) hnot
    rw [card_blockWitness] at hc
    change number T v ≤ _ at hc
    omega
  obtain ⟨o, ho⟩ := hex
  have hi := (blockedOccurrence_injective V T A w).sumElim
    (periodOccurrence_injective hp per hv hw hlen o)
    (fun b t => ho.period_prefix per hv hw hlen t b)
  have hc := Fintype.card_le_of_injective _ hi
  simpa only [Fintype.card_sum, card_blockWitness, Fintype.card_fin, number,
    Nat.add_assoc] using hc

/-- The functional depends monotonically only on words STRICTLY longer than
its inner word, although the triggered count operator itself need not be monotone. -/
theorem blocking_mono [DecidableEq α] {V : Finset (List α)} {A : ℤ → α}
    {s : List α} {m n : List α → ℕ}
    (hmn : ∀ r ∈ V, s.length < r.length → m r ≤ n r) :
    blocking V A s m ≤ blocking V A s n := by
  apply Finset.sum_le_sum
  intro r hr
  by_cases hz : coefficient A s r = 0
  · simp only [hz, Nat.zero_mul, le_refl]
  · have hlen := coefficient_pos_length (Nat.pos_of_ne_zero hz)
    exact Nat.mul_le_mul_left _ (hmn r hr (by omega))

/-- Retaining the increase at one summand while all other summands increase. -/
theorem sum_increase {ι : Type} [DecidableEq ι] (I : Finset ι) (a b : ι → ℕ)
    (h : ∀ i ∈ I, a i ≤ b i) {r : ι} (hr : r ∈ I) :
    (∑ i ∈ I, a i) + (b r - a r) ≤ ∑ i ∈ I, b i := by
  have he : ∑ i ∈ I.erase r, a i ≤ ∑ i ∈ I.erase r, b i :=
    Finset.sum_le_sum (fun i hi => h i (Finset.mem_of_mem_erase hi))
  have ha := Finset.sum_erase_add I a hr
  have hb := Finset.sum_erase_add I b hr
  have hrr := h r hr
  omega


theorem period_rule_lower_bound [DecidableEq α] {V : Finset (List α)}
    {A : ℤ → α} {T v w : List α} {p k : ℕ} {m : List α → ℕ}
    (hp : 0 < p) (hk : 0 < k) (per : Function.Periodic A (p : ℤ))
    (hv : Matches A v) (hw : Matches A w) (hlen : w.length + k * p = v.length)
    (hvV : v ∈ V) (hm : ∀ r ∈ V, w.length < r.length → m r ≤ number T r)
    (htrigger : blocking V A v m < m v) :
    blocking V A w m + k + 1 ≤ number T w := by
  have hkpos : 0 < k * p := Nat.mul_pos hk hp
  have hmv := hm v hvV (by omega)
  have hbw := blocking_mono (A := A) hm
  by_cases hmore : blocking V A v (number T) < number T v
  · have hgrowth := unblocked_count_growth hp per hv hw hlen hmore
    omega
  · have hcount := blocking_le_number V T A v
    have hstrict : blocking V A v m < blocking V A v (number T) := by omega
    have hex : ∃ r ∈ V, coefficient A v r * m r < coefficient A v r * number T r := by
      by_contra hnot
      push Not at hnot
      have hsum := Finset.sum_le_sum (fun r hr => hnot r hr)
      change blocking V A v (number T) ≤ blocking V A v m at hsum
      omega
    obtain ⟨r, hr, hprod⟩ := hex
    have hcoef : 0 < coefficient A v r := by
      by_contra hnot
      have hz : coefficient A v r = 0 := by omega
      simp only [hz, Nat.zero_mul] at hprod
      omega
    have hinc : m r < number T r := by
      by_contra hnot
      have hn : number T r ≤ m r := by omega
      have := Nat.mul_le_mul_left (coefficient A v r) hn
      omega
    have hamp := coefficient_amplification hp per hv hw hlen hcoef
    have hdiff : k + 1 ≤ coefficient A w r * number T r - coefficient A w r * m r := by
      have hh : coefficient A w r * (m r + 1) ≤ coefficient A w r * number T r :=
        Nat.mul_le_mul_left _ (by omega)
      rw [Nat.mul_add, Nat.mul_one] at hh
      omega
    have hterms (r : List α) (hr : r ∈ V) :
        coefficient A w r * m r ≤ coefficient A w r * number T r := by
      by_cases hz : coefficient A w r = 0
      · simp only [hz, Nat.zero_mul, le_refl]
      · have hl := coefficient_pos_length (Nat.pos_of_ne_zero hz)
        exact Nat.mul_le_mul_left _ (hm r hr (by omega))
    have hs := sum_increase V (fun r => coefficient A w r * m r)
      (fun r => coefficient A w r * number T r) hterms hr
    change blocking V A w m + _ ≤ blocking V A w (number T) at hs
    have hl := blocking_le_number V T A w
    omega

theorem exists_occurs_of_infix {T s : List α} (h : s <:+: T) : ∃ x, Occurs T s x := by
  rcases h with ⟨a, b, rfl⟩
  rw [List.append_assoc]
  refine ⟨a.length, ⟨by simp only [List.length_append]; omega, ?_⟩⟩
  intro i
  simp only [List.getElem?_append, ite_eq_right (show ¬a.length + i.val < a.length by omega),
    Nat.add_sub_cancel_left, ite_eq_left i.isLt]

theorem number_pos_of_infix [DecidableEq α] {T s : List α} (h : s <:+: T) :
    0 < number T s := by
  obtain ⟨x, hx⟩ := exists_occurs_of_infix h
  apply Fintype.card_pos_iff.mpr
  exact ⟨⟨⟨x, by have := hx.1; omega⟩, hx⟩⟩

theorem Occurs.cons_tail {T w : List α} {c : α} {x : ℕ}
    (h : Occurs T (c :: w) x) : Occurs T w (x + 1) := by
  refine ⟨by have := h.1; simp only [List.length_cons] at this; omega, ?_⟩
  intro i
  have ht := h.at (i := i.val + 1) (by simp only [List.length_cons]; omega)
  simpa only [List.getElem?_cons_succ, Nat.add_right_comm, Nat.add_assoc] using ht

theorem Occurs.append_init {T w : List α} {c : α} {x : ℕ}
    (h : Occurs T (w ++ [c]) x) : Occurs T w x := by
  refine ⟨by have := h.1; simp only [List.length_append, List.length_singleton] at this; omega, ?_⟩
  intro i
  have ht := h.at (i := i.val) (by simp only [List.length_append, List.length_singleton]; omega)
  simpa only [List.getElem?_append, ite_eq_left i.isLt] using ht

/-- Disjointness of preceding-letter occurrence classes gives the first
extension lower bound in the count recursion. -/
theorem left_extension_number [DecidableEq α] (alphabet : Finset α) (T w : List α) :
    (∑ c ∈ alphabet, number T (c :: w)) ≤ number T w := by
  let f : (Σ c : alphabet, Occurrence T (c.val :: w)) → Occurrence T w := fun b =>
    ⟨⟨b.2.val.val + 1, by have := b.2.property.1; simp only [List.length_cons] at this; omega⟩,
      b.2.property.cons_tail⟩
  have hf : Function.Injective f := by
    intro b b' heq
    rcases b with ⟨⟨c, hc⟩, ⟨⟨x, hxb⟩, hx⟩⟩
    rcases b' with ⟨⟨d, hd⟩, ⟨⟨y, hyb⟩, hy⟩⟩
    have hh := congrArg (fun o : Occurrence T w => o.val.val) heq
    change x + 1 = y + 1 at hh
    have hxy : x = y := by omega
    subst y
    have hx0 := hx.at (i := 0) (by simp)
    have hy0 := hy.at (i := 0) (by simp)
    have hcd : c = d := by simpa only [List.getElem?_cons_zero, Option.some.injEq] using hx0.symm.trans hy0
    subst d
    rfl
  have hh := Fintype.card_le_of_injective f hf
  rw [Finset.sum_subtype alphabet (fun _ => Iff.rfl)]
  simpa only [Fintype.card_sigma, number] using hh

/-- The analogous following-letter occurrence classes are disjoint too. -/
theorem right_extension_number [DecidableEq α] (alphabet : Finset α) (T w : List α) :
    (∑ c ∈ alphabet, number T (w ++ [c])) ≤ number T w := by
  let f : (Σ c : alphabet, Occurrence T (w ++ [c.val])) → Occurrence T w := fun b =>
    ⟨b.2.val, b.2.property.append_init⟩
  have hf : Function.Injective f := by
    intro b b' heq
    rcases b with ⟨⟨c, hc⟩, ⟨⟨x, hxb⟩, hx⟩⟩
    rcases b' with ⟨⟨d, hd⟩, ⟨⟨y, hyb⟩, hy⟩⟩
    have hh := congrArg (fun o : Occurrence T w => o.val.val) heq
    change x = y at hh
    subst y
    have hx0 := hx.at (i := w.length) (by simp)
    have hy0 := hy.at (i := w.length) (by simp)
    have hcd : c = d := by
      simpa only [List.getElem?_append, lt_self_iff_false, ite_false,
        Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] using hx0.symm.trans hy0
    subst d
    rfl
  have hh := Fintype.card_le_of_injective f hf
  rw [Finset.sum_subtype alphabet (fun _ => Iff.rfl)]
  simpa only [Fintype.card_sigma, number] using hh

/-- Finite data of the preprocessed instance; geometric hypotheses are proved
for the actual input construction below, not hidden in this record. -/
structure Data (α : Type) where
  vertices : Finset (List α)
  required : Finset (List α)
  alphabet : Finset α

/-- The unique period-p text determined by the first p letters of v. Fallback
values are never used in a valid rule, since there 0 < p < length v. -/
def finiteText [Inhabited α] (v : List α) (p : ℕ) (x : ℤ) : α :=
  v[(x % (p : ℤ)).toNat]!

theorem finiteText_periodic [Inhabited α] (v : List α) (p : ℕ) :
    Function.Periodic (finiteText v p) (p : ℤ) := by
  intro x
  simp only [finiteText, Int.add_emod, Int.emod_self, add_zero, Int.emod_emod]

instance [DecidableEq α] (A : ℤ → α) (w : List α) : Decidable (Matches A w) :=
  inferInstanceAs (Decidable (∀ _i : Fin w.length, _))

/-- Equality of the longer counts preserves a blocking functional. -/
theorem blocking_congr [DecidableEq α] {V : Finset (List α)} {A : ℤ → α}
    {s : List α} {m n : List α → ℕ}
    (hmn : ∀ r ∈ V, s.length < r.length → m r = n r) :
    blocking V A s m = blocking V A s n := by
  apply Finset.sum_congr rfl
  intro r hr
  by_cases hz : coefficient A s r = 0
  · simp only [hz, Nat.zero_mul]
  · have hlen := coefficient_pos_length (Nat.pos_of_ne_zero hz)
    rw [hmn r hr (by omega)]

namespace Data

variable [DecidableEq α] [Inhabited α]


def rule (D : Data α) (m : List α → ℕ) (w v : List α) (p k : ℕ) : ℕ :=
  let A := finiteText v p
  if 0 < p ∧ 0 < k ∧ w ≠ [] ∧ w.length + k * p = v.length ∧
      Matches A v ∧ Matches A w then
    if blocking D.vertices A v m < m v then blocking D.vertices A w m + k + 1 else 0
  else 0

/-- Finite enumeration of ALL rules; no least-period restriction is imposed. -/
def rules (D : Data α) (m : List α → ℕ) (w : List α) : ℕ :=
  D.vertices.sup fun v => (Finset.range (v.length + 1)).sup fun p =>
    (Finset.range (v.length + 1)).sup fun k => D.rule m w v p k

def left (D : Data α) (m : List α → ℕ) (w : List α) : ℕ :=
  ∑ c ∈ D.alphabet, if c :: w ∈ D.vertices then m (c :: w) else 0

def right (D : Data α) (m : List α → ℕ) (w : List α) : ℕ :=
  ∑ c ∈ D.alphabet, if w ++ [c] ∈ D.vertices then m (w ++ [c]) else 0


def step (D : Data α) (m : List α → ℕ) (w : List α) : ℕ :=
  if w ∈ D.vertices ∧ w ≠ [] then
    max (if w ∈ D.required then 1 else 0) (max (D.left m w) (max (D.right m w) (D.rules m w)))
  else 0

/-- Parallel triangular evaluation; the stabilization proof below shows that
this computes the exact descending recursion, rather than a different fixed point. -/
def stage (D : Data α) : ℕ → List α → ℕ
  | 0 => fun _ => 0
  | n + 1 => D.step (D.stage n)

def depth (D : Data α) : ℕ := D.vertices.sup List.length

def count (D : Data α) : List α → ℕ := D.stage (D.depth + 1)

theorem step_le_number (D : Data α) (T : List α)
    (hinput : ∀ w ∈ D.required, w <:+: T)
    {m : List α → ℕ} (hm : ∀ r ∈ D.vertices, m r ≤ number T r) (w : List α) :
    D.step m w ≤ number T w := by
  unfold step
  split
  · apply max_le
    · split
      · exact number_pos_of_infix (hinput _ ‹_›)
      · exact Nat.zero_le _
    · apply max_le
      · apply le_trans (Finset.sum_le_sum (g := fun c => number T (c :: w)) ?_)
          (left_extension_number D.alphabet T w)
        intro c _
        split
        · exact hm _ ‹_›
        · exact Nat.zero_le _
      · apply max_le
        · apply le_trans (Finset.sum_le_sum (g := fun c => number T (w ++ [c])) ?_)
            (right_extension_number D.alphabet T w)
          intro c _
          split
          · exact hm _ ‹_›
          · exact Nat.zero_le _
        · apply Finset.sup_le
          intro v hvV
          apply Finset.sup_le
          intro p _
          apply Finset.sup_le
          intro k _
          unfold rule
          dsimp only
          split
          · rename_i h
            obtain ⟨hp, hk, _, hlen, hv, hw⟩ := h
            split
            · exact period_rule_lower_bound hp hk (finiteText_periodic v p) hv hw hlen hvV
                (fun r hr _ => hm r hr) ‹_›
            · exact Nat.zero_le _
          · exact Nat.zero_le _
  · exact Nat.zero_le _

/-- Every intermediate computational stage, not only the final counts, is bounded
by the occurrence counts of EVERY common superstring. -/
theorem stage_le_number (D : Data α) (T : List α)
    (hinput : ∀ w ∈ D.required, w <:+: T) (n : ℕ) (w : List α) :
    D.stage n w ≤ number T w := by
  induction n generalizing w with
  | zero => exact Nat.zero_le _
  | succ n ih => exact D.step_le_number T hinput (fun r _ => ih r) w

/-- A rule value depends only on strictly longer words. -/
theorem rule_congr (D : Data α) {m n : List α → ℕ} {w v : List α} (p k : ℕ)
    (hvV : v ∈ D.vertices)
    (hmn : ∀ r ∈ D.vertices, w.length < r.length → m r = n r) :
    D.rule m w v p k = D.rule n w v p k := by
  unfold rule
  dsimp only
  by_cases hvalid : 0 < p ∧ 0 < k ∧ w ≠ [] ∧ w.length + k * p = v.length ∧
      Matches (finiteText v p) v ∧ Matches (finiteText v p) w
  · rw [ite_eq_left hvalid, ite_eq_left hvalid]
    obtain ⟨hp, hk, _, hlen, _, _⟩ := hvalid
    have hkp : 0 < k * p := Nat.mul_pos hk hp
    have hlong : w.length < v.length := by omega
    have hmV := hmn v hvV hlong
    have hbV := blocking_congr (A := finiteText v p)
      (fun r hr hvr => hmn r hr (lt_trans hlong hvr))
    have hbW := blocking_congr (A := finiteText v p) hmn
    rw [hmV, hbV, hbW]
  · rw [ite_eq_right hvalid, ite_eq_right hvalid]

/-- Triangularity of the complete finite operator. -/
theorem step_congr (D : Data α) {m n : List α → ℕ} {w : List α}
    (hmn : ∀ r ∈ D.vertices, w.length < r.length → m r = n r) :
    D.step m w = D.step n w := by
  have hl : D.left m w = D.left n w := by
    apply Finset.sum_congr rfl
    intro c _
    split
    · rw [hmn _ ‹_› (by simp)]
    · rfl
  have hr : D.right m w = D.right n w := by
    apply Finset.sum_congr rfl
    intro c _
    split
    · rw [hmn _ ‹_› (by simp)]
    · rfl
  have hs : D.rules m w = D.rules n w := by
    apply Finset.sup_congr rfl
    intro v hv
    apply Finset.sup_congr rfl
    intro p _
    apply Finset.sup_congr rfl
    intro k _
    exact D.rule_congr p k hv hmn
  simp only [step, hl, hr, hs]

/-- After n stages every word less than n levels from the top has stabilized. -/
theorem stage_stable (D : Data α) (n : ℕ) (w : List α)
    (hdepth : D.depth < w.length + n) : D.stage (n + 1) w = D.stage n w := by
  induction n generalizing w with
  | zero =>
    have hnot : w ∉ D.vertices := by
      intro hw
      have hle : w.length ≤ D.depth := Finset.le_sup hw
      omega
    simp only [stage, step, hnot, false_and, ite_false]
  | succ n ih =>
    change D.step (D.stage (n + 1)) w = D.step (D.stage n) w
    apply D.step_congr
    intro r _ hwr
    exact ih r (by omega)

/-- The actual counts satisfy exactly the minimal-bound recursion. -/
theorem count_fixed (D : Data α) (w : List α) : D.step D.count w = D.count w := by
  exact D.stage_stable (D.depth + 1) w (by omega)


theorem count_le_number (D : Data α) (T : List α)
    (hinput : ∀ w ∈ D.required, w <:+: T) (w : List α) : D.count w ≤ number T w :=
  D.stage_le_number T hinput _ w

theorem count_zero (D : Data α) (w : List α)
    (hw : w ∉ D.vertices ∨ w = []) : D.count w = 0 := by
  rw [← D.count_fixed w]
  unfold step
  split
  · rename_i hvalid
    rcases hw with hw | hw
    · exact (hw hvalid.1).elim
    · exact (hvalid.2 hw).elim
  · rfl

theorem required_le_count (D : Data α) {w : List α}
    (hw : w ∈ D.vertices) (hne : w ≠ []) (hr : w ∈ D.required) :
    1 ≤ D.count w := by
  rw [← D.count_fixed w]
  rw [step, ite_eq_left ⟨hw, hne⟩, ite_eq_left hr]
  exact le_max_left _ _

theorem left_le_count (D : Data α) {w : List α}
    (hw : w ∈ D.vertices) (hne : w ≠ []) : D.left D.count w ≤ D.count w := by
  rw [← D.count_fixed w]
  rw [step, ite_eq_left ⟨hw, hne⟩]
  exact le_trans (le_max_left _ _) (le_max_right _ _)

theorem right_le_count (D : Data α) {w : List α}
    (hw : w ∈ D.vertices) (hne : w ≠ []) : D.right D.count w ≤ D.count w := by
  rw [← D.count_fixed w]
  rw [step, ite_eq_left ⟨hw, hne⟩]
  exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))

theorem left_count (D : Data α) (w : List α) :
    D.left D.count w = ∑ c ∈ D.alphabet, D.count (c :: w) := by
  apply Finset.sum_congr rfl
  intro c _
  split
  · rfl
  · exact (D.count_zero _ (Or.inl ‹_›)).symm

theorem right_count (D : Data α) (w : List α) :
    D.right D.count w = ∑ c ∈ D.alphabet, D.count (w ++ [c]) := by
  apply Finset.sum_congr rfl
  intro c _
  split
  · rfl
  · exact (D.count_zero _ (Or.inl ‹_›)).symm

theorem rule_le_count (D : Data α) {w v : List α} {p k : ℕ}
    (hw : w ∈ D.vertices) (hne : w ≠ [])
    (hv : v ∈ D.vertices) (hp : p ≤ v.length) (hk : k ≤ v.length) :
    D.rule D.count w v p k ≤ D.count w := by
  have hsup : D.rule D.count w v p k ≤ D.rules D.count w := by
    apply le_trans (Finset.le_sup (f := fun k => D.rule D.count w v p k)
      (show k ∈ Finset.range (v.length + 1) from Finset.mem_range.mpr (by omega)))
    apply le_trans (Finset.le_sup (f := fun p => (Finset.range (v.length + 1)).sup
      (fun k => D.rule D.count w v p k))
      (show p ∈ Finset.range (v.length + 1) from Finset.mem_range.mpr (by omega)))
    exact Finset.le_sup (f := fun v => (Finset.range (v.length + 1)).sup
      (fun p => (Finset.range (v.length + 1)).sup (fun k => D.rule D.count w v p k))) hv
  rw [← D.count_fixed w]
  rw [step, ite_eq_left ⟨hw, hne⟩]
  exact le_trans hsup
    (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))

end Data

/-- The finite rule representative is the original two-sided text, not merely
its forward restriction. -/
theorem finiteText_eq [Inhabited α] {A : ℤ → α} {v : List α} {p : ℕ}
    (hp : 0 < p) (hper : Function.Periodic A (p : ℤ))
    (hm : Matches A v) (hlen : p ≤ v.length) : finiteText v p = A := by
  funext x
  have hpz : (0 : ℤ) < p := by omega
  have hmod0 := Int.emod_nonneg x (show (p : ℤ) ≠ 0 by omega)
  have hmodlt := Int.emod_lt_of_pos x hpz
  have hi : (x % (p : ℤ)).toNat < v.length := by omega
  have hh := hm ⟨(x % (p : ℤ)).toNat, hi⟩
  have he : (((x % (p : ℤ)).toNat : ℕ) : ℤ) = x % p := by omega
  change v[(x % (p : ℤ)).toNat]? = some (A (((x % (p : ℤ)).toNat : ℕ) : ℤ)) at hh
  rw [he, Hierarchical.periodic_emod A (p : ℤ) hper x] at hh
  unfold finiteText
  exact List.getElem!_of_getElem? hh

namespace Data
variable [DecidableEq α] [Inhabited α]

/-- Every period rule holds for the computed counts. -/
theorem period_rule (D : Data α) {A : ℤ → α} {w v : List α} {p k : ℕ}
    (hp : 0 < p) (hk : 0 < k) (hper : Function.Periodic A (p : ℤ))
    (hw : w ∈ D.vertices) (hne : w ≠ []) (hv : v ∈ D.vertices)
    (hmv : Matches A v) (hmw : Matches A w)
    (hlen : w.length + k * p = v.length)
    (htrigger : blocking D.vertices A v D.count < D.count v) :
    blocking D.vertices A w D.count + k + 1 ≤ D.count w := by
  have hkp : p ≤ k * p := by nlinarith
  have hklen : k ≤ v.length := by nlinarith
  have hplen : p ≤ v.length := by omega
  have heq := finiteText_eq hp hper hmv hplen
  have hr := D.rule_le_count hw hne hv hplen hklen
  have hvalid : 0 < p ∧ 0 < k ∧ w ≠ [] ∧ w.length + k * p = v.length ∧
      Matches A v ∧ Matches A w := ⟨hp, hk, hne, hlen, hmv, hmw⟩
  simpa only [rule, heq, ite_eq_left hvalid, ite_eq_left htrigger] using hr

end Data

/-- Nonempty occurrences inject into the positions of the ambient word. -/
theorem number_le_length [DecidableEq α] {T s : List α} (hs : s ≠ []) : number T s ≤ T.length := by
  classical
  let f : Occurrence T s → Fin T.length := fun o =>
    ⟨o.val.val, by have := o.property.1; have := List.length_pos_iff.mpr hs; omega⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply Fin.ext
    exact congrArg (fun z : Fin T.length => z.val) h
  simpa only [number, Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- Counts of one-letter occurrences, independently of how large the alphabet
of labels is, sum to at most the symbol length of the ambient word. -/
theorem singleton_number_sum [DecidableEq α] (C : Finset α) (T : List α) :
    (∑ c ∈ C, number T [c]) ≤ T.length := by
  let f : (Σ c : C, Occurrence T [c.val]) → Fin T.length := fun b =>
    ⟨b.2.val.val, by have := b.2.property.1; simp only [List.length_singleton] at this; omega⟩
  have hf : Function.Injective f := by
    intro b b' heq
    rcases b with ⟨⟨c, hc⟩, ⟨⟨x, hxb⟩, hx⟩⟩
    rcases b' with ⟨⟨d, hd⟩, ⟨⟨y, hyb⟩, hy⟩⟩
    have hh := congrArg Fin.val heq
    change x = y at hh
    subst y
    have hcd : c = d := by
      have hh := (hx.at (i := 0) (by simp)).symm.trans (hy.at (i := 0) (by simp))
      simpa only [List.getElem?_cons_zero, Option.some.injEq] using hh
    subst d
    rfl
  have hh := Fintype.card_le_of_injective f hf
  rw [Finset.sum_subtype C (fun _ => Iff.rfl)]
  simpa only [Fintype.card_sigma, number, Fintype.card_fin] using hh

namespace Data
variable [DecidableEq α] [Inhabited α]

def weight (D : Data α) : ℕ := ∑ c ∈ D.alphabet, D.count [c]

theorem weight_le_length (D : Data α) (T : List α)
    (hinput : ∀ w ∈ D.required, w <:+: T) : D.weight ≤ T.length :=
  le_trans (Finset.sum_le_sum (fun _ _ => D.count_le_number T hinput _))
    (singleton_number_sum D.alphabet T)

end Data

end Counts

end Superstring

end OAI
