import Mathlib
import OAI.Computability.DeterministicSum.Interpolation

namespace OAI

/-! Exact polynomial-filter decision, false-triple charges and distinct-position role searches. -/

namespace DeterministicThreeSum.DeterministicDecision
open scoped BigOperators
open Finset

structure Grouping {n : ℕ} (A : Finset (Fin n)) (k : ℕ) where
  members : Fin k → Finset (Fin n)
  nonempty : ∀ g, (members g).Nonempty
  cover : ∀ a, a ∈ A ↔ ∃ g, a ∈ members g
  unique : ∀ g h a, a ∈ members g → a ∈ members h → g = h

variable {n k J T : ℕ} {A B C : Finset (Fin n)}

lemma Grouping.subset (P : Grouping A k) (g : Fin k) : P.members g ⊆ A := by
  intro a ha
  exact (P.cover a).mpr ⟨g, ha⟩

lemma Grouping.size_le (P : Grouping A k) (g : Fin k) : (P.members g).card ≤ n := by
  simpa using (Finset.card_le_univ (P.members g))

def ExactPair (x : Fin n → ℤ) (B : Finset (Fin n)) (a c : Fin n) : Prop :=
  ∃ b ∈ B, x a + x b + x c = 0

def ModularHit (J : ℕ) (x : Fin n → ℤ) (B : Finset (Fin n)) (a c : Fin n) : Prop :=
  ∃ b ∈ B, (J : ℤ) ∣ x a + x b + x c

def ExactCell (x : Fin n → ℤ) (B : Finset (Fin n)) (P : Grouping A k)
    (gc : Fin k × Fin n) : Prop :=
  ∃ a ∈ P.members gc.1, ExactPair x B a gc.2

def RoleSolution (x : Fin n → ℤ) (A B C : Finset (Fin n)) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, x a + x b + x c = 0

noncomputable def hitCount (J : ℕ) (x : Fin n → ℤ) (B : Finset (Fin n))
    (P : Grouping A k) (gc : Fin k × Fin n) : ℕ := by
  classical
  exact ((P.members gc.1).filter (fun a => ModularHit J x B a gc.2)).card

noncomputable def groupSum (E : Fin n → Fin n → ZMod T)
    (P : Grouping A k) (gc : Fin k × Fin n) : ZMod T :=
  ∑ a ∈ P.members gc.1, E a gc.2

def allCells (k : ℕ) (C : Finset (Fin n)) : Finset (Fin k × Fin n) :=
  univ ×ˢ C

noncomputable def selectedCells (E : Fin n → Fin n → ZMod T) (P : Grouping A k)
    (C : Finset (Fin n)) (D : Finset (Fin k × Fin n)) : Finset (Fin k × Fin n) := by
  classical
  exact (allCells k C).filter (fun gc => gc ∈ D ∨ groupSum E P gc ≠ 0)

def CleanAgreement (J : ℕ) (x : Fin n → ℤ) (B C : Finset (Fin n))
    (P : Grouping A k) (D : Finset (Fin k × Fin n))
    (E : Fin n → Fin n → ZMod T) : Prop := by
  classical
  exact ∀ g c, c ∈ C → (g,c) ∉ D → ∀ a ∈ P.members g,
    E a c = if ModularHit J x B a c then 1 else 0

lemma hitCount_le (x : Fin n → ℤ) (P : Grouping A k) (gc : Fin k × Fin n) :
    hitCount J x B P gc ≤ n := by
  classical
  exact (Finset.card_le_card (Finset.filter_subset _ _)).trans (P.size_le gc.1)

lemma clean_sum (x : Fin n → ℤ) (P : Grouping A k)
    (D : Finset (Fin k × Fin n)) (E : Fin n → Fin n → ZMod T)
    (h : CleanAgreement J x B C P D E) {gc : Fin k × Fin n}
    (hc : gc.2 ∈ C) (hd : gc ∉ D) :
    groupSum E P gc = (hitCount J x B P gc : ZMod T) := by
  classical
  unfold groupSum hitCount
  rw [Finset.natCast_card_filter]
  exact Finset.sum_congr rfl (fun a ha => h gc.1 gc.2 hc hd a ha)

lemma cast_count_ne_zero {h : ℕ} (ht : h < T) :
    (h : ZMod T) ≠ 0 ↔ 0 < h := by
  constructor
  · intro hn
    by_contra hz
    have : h = 0 := by omega
    simp [this] at hn
  · intro hp hz
    have hv := congrArg ZMod.val hz
    rw [ZMod.val_natCast_of_lt ht, ZMod.val_zero] at hv
    omega

lemma hitCount_pos_iff (x : Fin n → ℤ) (P : Grouping A k) (gc : Fin k × Fin n) :
    0 < hitCount J x B P gc ↔ ∃ a ∈ P.members gc.1, ModularHit J x B a gc.2 := by
  classical
  simp [hitCount, Finset.card_pos, Finset.Nonempty]

lemma clean_selected_iff (x : Fin n → ℤ) (P : Grouping A k)
    (D : Finset (Fin k × Fin n)) (E : Fin n → Fin n → ZMod T)
    (h : CleanAgreement J x B C P D E) (hn : n < T) {gc : Fin k × Fin n}
    (hc : gc.2 ∈ C) (hd : gc ∉ D) :
    gc ∈ selectedCells E P C D ↔ ∃ a ∈ P.members gc.1, ModularHit J x B a gc.2 := by
  classical
  simp only [selectedCells, mem_filter, allCells, mem_product, mem_univ, true_and,
    hc, true_and, hd, false_or]
  rw [clean_sum x P D E h hc hd,
    cast_count_ne_zero ((hitCount_le x P gc).trans_lt hn), hitCount_pos_iff]

lemma exact_modular (x : Fin n → ℤ) {a c : Fin n} (h : ExactPair x B a c) :
    ModularHit J x B a c := by
  obtain ⟨b, hb, hz⟩ := h
  exact ⟨b, hb, hz ▸ dvd_zero _⟩

lemma exact_cell_selected (x : Fin n → ℤ) (P : Grouping A k)
    (D : Finset (Fin k × Fin n)) (E : Fin n → Fin n → ZMod T)
    (h : CleanAgreement J x B C P D E) (hn : n < T) {gc : Fin k × Fin n}
    (hc : gc.2 ∈ C) (hex : ExactCell x B P gc) : gc ∈ selectedCells E P C D := by
  classical
  by_cases hd : gc ∈ D
  · exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ _, hc⟩, Or.inl hd⟩
  · apply (clean_selected_iff x P D E h hn hc hd).mpr
    obtain ⟨a, ha, hp⟩ := hex
    exact ⟨a, ha, exact_modular x hp⟩

theorem role_decision_iff (x : Fin n → ℤ) (P : Grouping A k)
    (D : Finset (Fin k × Fin n)) (E : Fin n → Fin n → ZMod T)
    (h : CleanAgreement J x B C P D E) (hn : n < T) :
    (∃ gc ∈ selectedCells E P C D, ExactCell x B P gc) ↔ RoleSolution x A B C := by
  constructor
  · rintro ⟨⟨g,c⟩, hgc, a, ha, b, hb, hz⟩
    have hc : c ∈ C := (mem_product.mp (mem_filter.mp hgc).1).2
    exact ⟨a, P.subset g ha, b, hb, c, hc, hz⟩
  · rintro ⟨a, ha, b, hb, c, hc, hz⟩
    obtain ⟨g, hg⟩ := (P.cover a).mp ha
    have hex : ExactCell x B P (g,c) := ⟨a,hg,b,hb,hz⟩
    exact ⟨(g,c), exact_cell_selected x P D E h hn hc hex, hex⟩

noncomputable def falseTriples (J : ℕ) (x : Fin n → ℤ)
    (A B C : Finset (Fin n)) : Finset (Fin n × Fin n × Fin n) := by
  classical
  exact (A ×ˢ (B ×ˢ C)).filter (fun t =>
    x t.1 + x t.2.1 + x t.2.2 ≠ 0 ∧ (J : ℤ) ∣ x t.1 + x t.2.1 + x t.2.2)

noncomputable def unsuccessfulClean (x : Fin n → ℤ) (B C : Finset (Fin n))
    (P : Grouping A k) (D : Finset (Fin k × Fin n))
    (E : Fin n → Fin n → ZMod T) : Finset (Fin k × Fin n) := by
  classical
  exact (selectedCells E P C D).filter (fun gc => gc ∉ D ∧ ¬ ExactCell x B P gc)

lemma unsuccessful_has_false (x : Fin n → ℤ) (P : Grouping A k)
    (D : Finset (Fin k × Fin n)) (E : Fin n → Fin n → ZMod T)
    (h : CleanAgreement J x B C P D E) (hn : n < T)
    {gc : Fin k × Fin n} (hu : gc ∈ unsuccessfulClean x B C P D E) :
    ∃ t ∈ falseTriples J x A B C, t.1 ∈ P.members gc.1 ∧ t.2.2 = gc.2 := by
  classical
  obtain ⟨hgc, hd, he⟩ := mem_filter.mp hu
  have hc : gc.2 ∈ C := (mem_product.mp (mem_filter.mp hgc).1).2
  obtain ⟨a, ha, b, hb, hm⟩ := (clean_selected_iff x P D E h hn hc hd).mp hgc
  have hz : x a + x b + x gc.2 ≠ 0 := fun hz => he ⟨a, ha, b, hb, hz⟩
  refine ⟨(a,b,gc.2), ?_, ha, rfl⟩
  exact mem_filter.mpr ⟨mem_product.mpr ⟨P.subset gc.1 ha,
    mem_product.mpr ⟨hb,hc⟩⟩, hz, hm⟩

theorem unsuccessful_clean_card_le (x : Fin n → ℤ) (P : Grouping A k)
    (D : Finset (Fin k × Fin n)) (E : Fin n → Fin n → ZMod T)
    (h : CleanAgreement J x B C P D E) (hn : n < T) :
    (unsuccessfulClean x B C P D E).card ≤ (falseTriples J x A B C).card := by
  classical
  choose f hf hm hc using fun gc : ↥(unsuccessfulClean x B C P D E) =>
    unsuccessful_has_false x P D E h hn gc.property
  let φ : ↥(unsuccessfulClean x B C P D E) → ↥(falseTriples J x A B C) :=
    fun gc => ⟨f gc, hf gc⟩
  have hi : Function.Injective φ := by
    intro u v huv
    have heq : f u = f v := congrArg Subtype.val huv
    apply Subtype.ext
    apply Prod.ext
    · apply P.unique _ _ (f u).1 (hm u)
      rw [heq]
      exact hm v
    · rw [← hc u, ← hc v, heq]
  simpa using Fintype.card_le_of_injective φ hi

lemma threeSUM_of_distinct (x : Fin n → ℤ) (a b c : Fin n)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) (hz : x a + x b + x c = 0) :
    ThreeSUM x := by
  rcases lt_or_gt_of_ne hab with hab | hba
  · rcases lt_or_gt_of_ne hbc with hbc | hcb
    · exact ⟨a,b,c,hab,hbc,hz⟩
    · rcases lt_or_gt_of_ne hac with hac | hca
      · exact ⟨a,c,b,hac,hcb,by omega⟩
      · exact ⟨c,a,b,hca,hab,by omega⟩
  · rcases lt_or_gt_of_ne hbc with hbc | hcb
    · rcases lt_or_gt_of_ne hac with hac | hca
      · exact ⟨b,a,c,hba,hac,by omega⟩
      · exact ⟨b,c,a,hbc,hca,by omega⟩
    · exact ⟨c,b,a,hcb,hba,by omega⟩

lemma role_solution_threeSUM (x : Fin n → ℤ)
    (hAB : Disjoint A B) (hBC : Disjoint B C) (hAC : Disjoint A C)
    (h : RoleSolution x A B C) : ThreeSUM x := by
  obtain ⟨a,ha,b,hb,c,hc,hz⟩ := h
  have hab : a ≠ b := by
    rintro rfl
    exact Finset.disjoint_left.mp hAB ha hb
  have hbc : b ≠ c := by
    rintro rfl
    exact Finset.disjoint_left.mp hBC hb hc
  have hac : a ≠ c := by
    rintro rfl
    exact Finset.disjoint_left.mp hAC ha hc
  exact threeSUM_of_distinct x a b c hab hbc hac hz

def residue (J : ℕ) (z : ℤ) : ℕ := (z : ZMod J).val

lemma residue_cast (hJ : 0 < J) (z : ℤ) :
    (residue J z : ZMod J) = (z : ZMod J) := by
  let : NeZero J := ⟨ne_of_gt hJ⟩
  exact ZMod.natCast_zmod_val _

lemma residue_lt (hJ : 0 < J) (z : ℤ) : residue J z < J := by
  let : NeZero J := ⟨ne_of_gt hJ⟩
  exact ZMod.val_lt _

noncomputable def shiftedTable (J T : ℕ) (x : Fin n → ℤ)
    (B : Finset (Fin n)) (θ : ℤ) : Fin J → ZMod T := by
  classical
  exact fun t => if ∃ j ∈ B, (t.val : ZMod J) = ((θ - x j : ℤ) : ZMod J)
    then 1 else 0

lemma shiftedTable_agreement (hJ : 0 < J) (x : Fin n → ℤ)
    (B : Finset (Fin n)) (θ : ℤ) (a c : Fin n) (u v : ℕ)
    (hu : (u : ZMod J) = (x a : ZMod J))
    (hv : (v : ZMod J) = ((x c + θ : ℤ) : ZMod J)) :
    letI : Decidable (ModularHit J x B a c) := Classical.propDecidable _
    shiftedTable J T x B θ ⟨(u + v) % J, Nat.mod_lt _ hJ⟩ =
      if ModularHit J x B a c then 1 else 0 := by
  classical
  have hsum : (((u + v) % J : ℕ) : ZMod J) =
      (x a : ZMod J) + (x c : ZMod J) + (θ : ZMod J) := by
    rw [ZMod.natCast_mod, Nat.cast_add, hu, hv, Int.cast_add, add_assoc]
  have htest : (∃ j ∈ B, (((u + v) % J : ℕ) : ZMod J) =
      ((θ - x j : ℤ) : ZMod J)) ↔ ModularHit J x B a c := by
    simp only [hsum, Int.cast_sub]
    constructor
    · rintro ⟨j,hj,hz⟩
      refine ⟨j, hj, (ZMod.intCast_zmod_eq_zero_iff_dvd _ J).mp ?_⟩
      push_cast
      linear_combination hz
    · rintro ⟨j,hj,hz⟩
      have hz' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ J).mpr hz
      push_cast at hz'
      refine ⟨j,hj,?_⟩
      linear_combination hz'
  simp only [shiftedTable, htest]

variable {base m d p e : ℕ}

def baseDigits (base : ℕ) (hb : 0 < base) : (d : ℕ) → ℕ → (Fin d → Fin base)
  | 0, _ => Fin.elim0
  | d + 1, u => Fin.cons ⟨u % base, Nat.mod_lt _ hb⟩ (baseDigits base hb d (u / base))

lemma baseDigits_value (hb : 0 < base) (d u : ℕ) (hu : u < base ^ d) :
    Digits.value base (fun i => (baseDigits base hb d u i).val) = u := by
  induction d generalizing u with
  | zero =>
    have hz : u = 0 := by simpa using hu
    simp [Digits.value, hz]
  | succ d ih =>
    have hu' : u / base < base ^ d := (Nat.div_lt_iff_lt_mul hb).mpr (by
      simpa [pow_succ] using hu)
    rw [Digits.value_succ]
    simp only [baseDigits, Fin.cons_zero, Fin.cons_succ]
    rw [ih (u / base) hu']
    exact Nat.mod_add_div u base

def residueDigits (base : ℕ) (hb : 0 < base) (d J : ℕ) (z : ℤ) : Fin d → Fin base :=
  baseDigits base hb d (residue J z)

lemma residueDigits_value (hb : 0 < base) (hJ : 0 < J) (hJpow : J ≤ base ^ d)
    (z : ℤ) : Digits.value base (fun i => (residueDigits base hb d J z i).val) =
      residue J z :=
  baseDigits_value hb d _ ((residue_lt hJ z).trans_le hJpow)

def splitOffset (m : ℕ) (z : Fin d → Fin base) : Fin d → ℕ :=
  fun i => m * ((z i).val / m)

def splitLocal (hm : 1 ≤ m) (z : Fin d → Fin base) : Fin d → Fin m :=
  fun i => ⟨(z i).val % m, Nat.mod_lt _ hm⟩

lemma splitOffset_multiple (z : Fin d → Fin base) (i : Fin d) :
    m ∣ splitOffset m z i := ⟨(z i).val / m, rfl⟩

lemma splitOffset_bound (hm : 1 ≤ m) (hdiv : m ∣ base) (z : Fin d → Fin base)
    (i : Fin d) : splitOffset m z i ≤ base - m := by
  obtain ⟨k, hk⟩ := hdiv
  have hdivlt : (z i).val / m < k := (Nat.div_lt_iff_lt_mul hm).mpr (by
    simpa [hk, Nat.mul_comm] using (z i).isLt)
  have hle := Nat.mul_le_mul_left m (Nat.succ_le_iff.mpr hdivlt)
  dsimp [splitOffset]
  rw [Nat.mul_succ, ← hk] at hle
  omega

lemma split_value (hm : 1 ≤ m) (z : Fin d → Fin base) :
    Digits.value base (fun i => splitOffset m z i + (splitLocal hm z i).val) =
      Digits.value base (fun i => (z i).val) := by
  congr 1
  funext i
  simpa only [splitOffset, splitLocal, Nat.mul_comm] using Nat.div_add_mod' (z i).val m

noncomputable def polynomialEntries (hm : 1 ≤ m) (hmb : m ≤ base) (hJ : 0 < J)
    (x : Fin n → ℤ) (B : Finset (Fin n)) (θ : ℤ)
    (offset : Fin n → Fin d → ℕ) (localDigit : Fin n → Fin d → Fin m)
    (queryDigit : Fin n → Fin d → Fin base) : Fin n → Fin n → ZMod (p ^ e) :=
  fun a c => MvPolynomial.eval
    (fun i => ((localDigit a i).val : ZMod (p ^ e)) + ((queryDigit c i).val : ZMod (p ^ e)))
    (Filter.polynomial hm hmb hJ (offset a) (shiftedTable J (p ^ e) x B θ))

noncomputable def dirtyCells (hm : 1 ≤ m) (hmb : m ≤ base)
    (P : Grouping A k) (C : Finset (Fin n))
    (localDigit : Fin n → Fin d → Fin m)
    (queryDigit : Fin n → Fin d → Fin base) : Finset (Fin k × Fin n) := by
  classical
  exact (allCells k C).filter (fun gc => ∃ a ∈ P.members gc.1,
    Digits.value base (fun i => (queryDigit gc.2 i).val) ∈
      Filter.exceptionalResidues hm hmb (localDigit a))

theorem polynomial_clean_agreement (hp : p.Prime) (he : 0 < e)
    (hq : base + m - 1 < p) (hm : 1 ≤ m) (hmb : m ≤ base) (hJ : 0 < J)
    (x : Fin n → ℤ) (B C : Finset (Fin n)) (P : Grouping A k) (θ : ℤ)
    (offset : Fin n → Fin d → ℕ) (localDigit : Fin n → Fin d → Fin m)
    (queryDigit : Fin n → Fin d → Fin base)
    (hu : ∀ a ∈ A, Digits.value base (fun i => offset a i + (localDigit a i).val) =
      residue J (x a))
    (hv : ∀ c ∈ C, Digits.value base (fun i => (queryDigit c i).val) =
      residue J (x c + θ)) :
    CleanAgreement J x B C P (dirtyCells hm hmb P C localDigit queryDigit)
      (polynomialEntries (p := p) (e := e) hm hmb hJ x B θ offset localDigit queryDigit) := by
  classical
  intro g c hc hd a ha
  have hnot : Digits.value base (fun i => (queryDigit c i).val) ∉
      Filter.exceptionalResidues hm hmb (localDigit a) := by
    intro hex
    apply hd
    exact mem_filter.mpr ⟨mem_product.mpr ⟨mem_univ g, hc⟩, a, ha, hex⟩
  unfold polynomialEntries
  rw [Filter.agreement hp he hq hm hmb hJ _ _ _ _ hnot]
  apply shiftedTable_agreement hJ x B θ a c
  · rw [hu a (P.subset g ha), residue_cast hJ]
  · rw [hv c hc, residue_cast hJ]

theorem polynomial_decision_iff (hp : p.Prime) (he : 0 < e)
    (hq : base + m - 1 < p) (hm : 1 ≤ m) (hmb : m ≤ base) (hJ : 0 < J)
    (x : Fin n → ℤ) (B C : Finset (Fin n)) (P : Grouping A k) (θ : ℤ)
    (offset : Fin n → Fin d → ℕ) (localDigit : Fin n → Fin d → Fin m)
    (queryDigit : Fin n → Fin d → Fin base)
    (hu : ∀ a ∈ A, Digits.value base (fun i => offset a i + (localDigit a i).val) =
      residue J (x a))
    (hv : ∀ c ∈ C, Digits.value base (fun i => (queryDigit c i).val) =
      residue J (x c + θ)) (hn : n < p ^ e) :
    (∃ gc ∈ selectedCells
      (polynomialEntries (p := p) (e := e) hm hmb hJ x B θ offset localDigit queryDigit)
      P C (dirtyCells hm hmb P C localDigit queryDigit), ExactCell x B P gc) ↔
        RoleSolution x A B C :=
  role_decision_iff x P _ _
    (polynomial_clean_agreement hp he hq hm hmb hJ x B C P θ offset
      localDigit queryDigit hu hv) hn

theorem residue_polynomial_decision_iff (hp : p.Prime) (he : 0 < e)
    (hq : base + m - 1 < p) (hm : 1 ≤ m) (hmb : m ≤ base) (hJ : 0 < J)
    (hJpow : J ≤ base ^ d) (x : Fin n → ℤ) (B C : Finset (Fin n))
    (P : Grouping A k) (θ : ℤ) (hn : n < p ^ e) :
    let hb : 0 < base := hm.trans hmb
    let inputs := fun a : Fin n => residueDigits base hb d J (x a)
    let queries := fun c : Fin n => residueDigits base hb d J (x c + θ)
    let offsets := fun a => splitOffset m (inputs a)
    let locals := fun a => splitLocal hm (inputs a)
    (∃ gc ∈ selectedCells
      (polynomialEntries (p := p) (e := e) hm hmb hJ x B θ offsets locals queries)
      P C (dirtyCells hm hmb P C locals queries), ExactCell x B P gc) ↔
        RoleSolution x A B C := by
  dsimp only
  apply polynomial_decision_iff hp he hq hm hmb hJ x B C P θ _ _ _ _ _ hn
  · intro a _
    rw [split_value]
    exact residueDigits_value _ hJ hJpow _
  · intro c _
    exact residueDigits_value _ hJ hJpow _

def checkedPrefix {α : Type*} (p : α → Prop) [DecidablePred p] : List α → List α
  | [] => []
  | a :: l => a :: (if p a then [] else checkedPrefix p l)

lemma checkedPrefix_sublist {α : Type*} (p : α → Prop) [DecidablePred p]
    (l : List α) : (checkedPrefix p l).Sublist l := by
  induction l with
  | nil => exact List.Sublist.refl []
  | cons a l ih =>
    simp only [checkedPrefix]
    split_ifs
    · exact List.Sublist.cons_cons a (List.nil_sublist l)
    · exact List.Sublist.cons_cons a ih

lemma checkedPrefix_success_unique {α : Type*} (p : α → Prop) [DecidablePred p]
    (l : List α) (a b : α) (ha : a ∈ checkedPrefix p l)
    (hb : b ∈ checkedPrefix p l) (hpa : p a) (hpb : p b) : a = b := by
  induction l with
  | nil => simp [checkedPrefix] at ha
  | cons c l ih =>
    by_cases hc : p c
    · simp only [checkedPrefix, ite_eq_left hc, List.mem_singleton] at ha hb
      exact ha.trans hb.symm
    · simp only [checkedPrefix, ite_eq_right hc, List.mem_cons] at ha hb
      have ha' : a ∈ checkedPrefix p l := ha.resolve_left (fun he => hc (he ▸ hpa))
      have hb' : b ∈ checkedPrefix p l := hb.resolve_left (fun he => hc (he ▸ hpb))
      exact ih ha' hb'

lemma checkedPrefix_success_iff {α : Type*} (p : α → Prop) [DecidablePred p]
    (l : List α) : (∃ a ∈ checkedPrefix p l, p a) ↔ ∃ a ∈ l, p a := by
  constructor
  · rintro ⟨a,ha,hp⟩
    exact ⟨a, (checkedPrefix_sublist p l).subset ha, hp⟩
  · induction l with
    | nil => simp
    | cons c l ih =>
      intro hex
      by_cases hc : p c
      · exact ⟨c, by simp [checkedPrefix, hc], hc⟩
      · obtain ⟨a,ha,hp⟩ := hex
        obtain ⟨b,hb,hpb⟩ := ih ⟨a, (List.mem_cons.mp ha).resolve_left
          (fun he => hc (he ▸ hp)), hp⟩
        exact ⟨b, by simp [checkedPrefix, hc, hb], hpb⟩

theorem checked_cell_count (x : Fin n → ℤ) (P : Grouping A k)
    (D : Finset (Fin k × Fin n)) (E : Fin n → Fin n → ZMod T)
    (h : CleanAgreement J x B C P D E) (hn : n < T)
    (l : List (Fin k × Fin n)) (hl : l.toFinset ⊆ selectedCells E P C D) :
    letI : DecidablePred (ExactCell x B P) := Classical.decPred _
    ((checkedPrefix (ExactCell x B P) l).toFinset).card ≤
      D.card + (falseTriples J x A B C).card + 1 := by
  classical
  let v := (checkedPrefix (ExactCell x B P) l).toFinset
  have hsub : v ⊆ (D ∪ unsuccessfulClean x B C P D E) ∪
      v.filter (ExactCell x B P) := by
    intro gc hgc
    by_cases he : ExactCell x B P gc
    · exact mem_union_right _ (mem_filter.mpr ⟨hgc,he⟩)
    · by_cases hd : gc ∈ D
      · exact mem_union_left _ (mem_union_left _ hd)
      · apply mem_union_left
        apply mem_union_right
        apply mem_filter.mpr
        exact ⟨hl (List.mem_toFinset.mpr ((checkedPrefix_sublist _ l).subset
          (List.mem_toFinset.mp hgc))), hd, he⟩
  have hone : (v.filter (ExactCell x B P)).card ≤ 1 := by
    apply card_le_one.mpr
    intro u hu v hv
    obtain ⟨hu, he⟩ := mem_filter.mp hu
    obtain ⟨hv, he'⟩ := mem_filter.mp hv
    exact checkedPrefix_success_unique _ l u v
      (List.mem_toFinset.mp hu) (List.mem_toFinset.mp hv) he he'
  have hun := unsuccessful_clean_card_le x P D E h hn
  have hu1 := card_union_le D (unsuccessfulClean x B C P D E)
  have hu2 := card_union_le (D ∪ unsuccessfulClean x B C P D E)
    (v.filter (ExactCell x B P))
  have hv := card_le_card hsub
  change v.card ≤ _
  omega

theorem pair_check_count (x : Fin n → ℤ) (P : Grouping A k)
    (D : Finset (Fin k × Fin n)) (E : Fin n → Fin n → ZMod T)
    (h : CleanAgreement J x B C P D E) (hn : n < T)
    (s : ℕ) (hs : ∀ g, (P.members g).card ≤ s)
    (l : List (Fin k × Fin n)) (hl : l.toFinset ⊆ selectedCells E P C D)
    (hlnd : l.Nodup) :
    letI : DecidablePred (ExactCell x B P) := Classical.decPred _
    let v := checkedPrefix (ExactCell x B P) l
    v.Nodup ∧ (∑ gc ∈ v.toFinset, (P.members gc.1).card) ≤
      s * (D.card + (falseTriples J x A B C).card + 1) := by
  classical
  let v := checkedPrefix (ExactCell x B P) l
  refine ⟨hlnd.sublist (checkedPrefix_sublist _ l), ?_⟩
  calc
    ∑ gc ∈ v.toFinset, (P.members gc.1).card ≤ ∑ _gc ∈ v.toFinset, s :=
      sum_le_sum (fun gc _ => hs gc.1)
    _ = s * v.toFinset.card := by simp [Nat.mul_comm]
    _ ≤ s * (D.card + (falseTriples J x A B C).card + 1) :=
      Nat.mul_le_mul_left s (checked_cell_count x P D E h hn l hl)

namespace Roles

variable {r : ℕ}

def bitLength (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

def positionBits (i : Fin n) : Fin (bitLength n) → Bool :=
  fun j => (i.val + 1).testBit j.val

lemma positionBits_injective : Function.Injective (positionBits (n := n)) := by
  intro a b hab
  apply Fin.ext
  have he : a.val + 1 = b.val + 1 := by
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < bitLength n
    · exact congrFun hab ⟨j,hj⟩
    · have hpow : n + 1 ≤ 2 ^ bitLength n := Nat.le_pow_clog (by decide) _
      have hpj : 2 ^ bitLength n ≤ 2 ^ j := Nat.pow_le_pow_right (by decide) (by omega)
      have ha : a.val + 1 < 2 ^ j := lt_of_lt_of_le (by omega) hpj
      have hb : b.val + 1 < 2 ^ j := lt_of_lt_of_le (by omega) hpj
      rw [Nat.testBit_lt_two_pow ha, Nat.testBit_lt_two_pow hb]
  omega

abbrev Color := Fin 3 → Bool

def sampledColor (code : Fin n → Fin r → Bool) (coords : Fin 3 → Fin r)
    (i : Fin n) : Color := fun j => code i (coords j)

lemma separating_coordinates (code : Fin n → Fin r → Bool)
    (hcode : Function.Injective code) (a b c : Fin n)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ coords : Fin 3 → Fin r,
      sampledColor code coords a ≠ sampledColor code coords b ∧
      sampledColor code coords b ≠ sampledColor code coords c ∧
      sampledColor code coords a ≠ sampledColor code coords c := by
  classical
  have hdiff : ∀ u v : Fin n, u ≠ v → ∃ t : Fin r, code u t ≠ code v t := by
    intro u v huv
    by_contra! h
    exact huv (hcode (funext h))
  obtain ⟨i,hi⟩ := hdiff a b hab
  obtain ⟨j,hj⟩ := hdiff b c hbc
  obtain ⟨l,hl⟩ := hdiff a c hac
  let coords : Fin 3 → Fin r := ![i,j,l]
  refine ⟨coords, ?_, ?_, ?_⟩
  · intro he
    exact hi (congrFun he 0)
  · intro he
    exact hj (congrFun he 1)
  · intro he
    exact hl (congrFun he 2)

abbrev Search (r : ℕ) := (Fin 3 → Fin r) × (Fin 3 ↪ Color)

def role (code : Fin n → Fin r → Bool) (s : Search r) (j : Fin 3) : Finset (Fin n) :=
  univ.filter (fun i => sampledColor code s.1 i = s.2 j)

lemma role_disjoint (code : Fin n → Fin r → Bool) (s : Search r)
    {i j : Fin 3} (hij : i ≠ j) : Disjoint (role code s i) (role code s j) := by
  apply Finset.disjoint_left.mpr
  intro a hi hj
  exact hij (s.2.injective ((mem_filter.mp hi).2.symm.trans (mem_filter.mp hj).2))

lemma search_card (r : ℕ) : Fintype.card (Search r) = 8 * 7 * 6 * r ^ 3 := by
  simp only [Search, Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_embedding_eq, Color, Fintype.card_bool]
  norm_num [Nat.descFactorial]
  omega

lemma positions_covered (code : Fin n → Fin r → Bool)
    (hcode : Function.Injective code) (a b c : Fin n)
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    ∃ s : Search r, a ∈ role code s 0 ∧ b ∈ role code s 1 ∧ c ∈ role code s 2 := by
  classical
  obtain ⟨coords,hAB,hBC,hAC⟩ := separating_coordinates code hcode a b c hab hbc hac
  let colors : Fin 3 → Color :=
    ![sampledColor code coords a, sampledColor code coords b, sampledColor code coords c]
  have hcolors : Function.Injective colors := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [colors]
  let s : Search r := ⟨coords, ⟨colors, hcolors⟩⟩
  refine ⟨s, ?_, ?_, ?_⟩ <;> exact mem_filter.mpr ⟨mem_univ _, rfl⟩

theorem threeSUM_iff_search (x : Fin n → ℤ) :
    ThreeSUM x ↔ ∃ s : Search (bitLength n),
      RoleSolution x (role positionBits s 0) (role positionBits s 1) (role positionBits s 2) := by
  constructor
  · rintro ⟨a,b,c,hab,hbc,hz⟩
    obtain ⟨s,ha,hb,hc⟩ := positions_covered positionBits positionBits_injective a b c
      (ne_of_lt hab) (ne_of_lt hbc) (ne_of_lt (hab.trans hbc))
    exact ⟨s,a,ha,b,hb,c,hc,hz⟩
  · rintro ⟨s,hs⟩
    exact role_solution_threeSUM x (role_disjoint _ s (by decide))
      (role_disjoint _ s (by decide)) (role_disjoint _ s (by decide)) hs

end Roles
end DeterministicThreeSum.DeterministicDecision

end OAI
