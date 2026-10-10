import Mathlib.Data.Fintype.EquivFin
import OAI.NumberTheory.Catalan.Determinants.TwoAdicSmoothedMinor

namespace OAI


namespace InternalCatalan

def oddPrimeUpperPairHighSet (p N : ℕ) : Finset ℕ :=
  Finset.Ico (p + b N) (p + min (A N) (L N - p))

def oddPrimeUpperCentralSet (p N : ℕ) : Finset ℕ :=
  Finset.Ico (max (b N) (H N - p)) (min p (L N))

def oddPrimeUpperRetainedSet (p N : ℕ) : Finset ℕ :=
  Finset.Ico (b N) (L N) \
    (oddPrimeUpperPairHighSet p N ∪ oddPrimeUpperCentralSet p N)

def oddPrimeUpperExceptionalSet (p N : ℕ) : Finset ℕ :=
  Finset.Ico (L N - p) (min (b N) (H N - p))

theorem oddPrimeUpperPairHighSet_mem_iff (p N j : ℕ) :
    j ∈ oddPrimeUpperPairHighSet p N ↔
      ∃ ell, b N ≤ ell ∧ ell < min (A N) (L N - p) ∧ j = p + ell := by
  simp only [oddPrimeUpperPairHighSet, Finset.mem_Ico]
  constructor
  · intro hj
    refine ⟨j - p, ?_, ?_, ?_⟩ <;> omega
  · rintro ⟨ell, hlo, hhi, rfl⟩
    constructor <;> omega

theorem oddPrimeUpperCentralSet_mem_iff (p N j : ℕ) :
    j ∈ oddPrimeUpperCentralSet p N ↔
      b N ≤ j ∧ j < L N ∧ H N - p ≤ j ∧ j < p := by
  simp only [oddPrimeUpperCentralSet, Finset.mem_Ico]
  omega

theorem oddPrimeUpperPairHighSet_subset_raw (p N : ℕ) :
    oddPrimeUpperPairHighSet p N ⊆ Finset.Ico (b N) (L N) := by
  intro j hj
  simp only [oddPrimeUpperPairHighSet, Finset.mem_Ico] at hj
  apply Finset.mem_Ico.mpr
  constructor <;> omega

theorem oddPrimeUpperCentralSet_subset_raw (p N : ℕ) :
    oddPrimeUpperCentralSet p N ⊆ Finset.Ico (b N) (L N) := by
  intro j hj
  have h := (oddPrimeUpperCentralSet_mem_iff p N j).mp hj
  exact Finset.mem_Ico.mpr ⟨h.1, h.2.1⟩

theorem oddPrimeUpperRetainedSet_subset_raw (p N : ℕ) :
    oddPrimeUpperRetainedSet p N ⊆ Finset.Ico (b N) (L N) := by
  intro j hj
  exact (Finset.mem_sdiff.mp hj).1

theorem oddPrimeUpperPairHighSet_disjoint_central (p N : ℕ) :
    Disjoint (oddPrimeUpperPairHighSet p N) (oddPrimeUpperCentralSet p N) := by
  apply Finset.disjoint_left.mpr
  intro j hjp hjc
  simp only [oddPrimeUpperPairHighSet, Finset.mem_Ico] at hjp
  have h := (oddPrimeUpperCentralSet_mem_iff p N j).mp hjc
  omega

theorem oddPrimeUpperRetainedSet_disjoint_pairHigh (p N : ℕ) :
    Disjoint (oddPrimeUpperRetainedSet p N) (oddPrimeUpperPairHighSet p N) := by
  apply Finset.disjoint_left.mpr
  intro j hjr hjp
  exact (Finset.mem_sdiff.mp hjr).2 (Finset.mem_union.mpr (Or.inl hjp))

theorem oddPrimeUpperRetainedSet_disjoint_central (p N : ℕ) :
    Disjoint (oddPrimeUpperRetainedSet p N) (oddPrimeUpperCentralSet p N) := by
  apply Finset.disjoint_left.mpr
  intro j hjr hjc
  exact (Finset.mem_sdiff.mp hjr).2 (Finset.mem_union.mpr (Or.inr hjc))

theorem oddPrimeUpperPool_partition (p N : ℕ) :
    oddPrimeUpperRetainedSet p N ∪
      (oddPrimeUpperPairHighSet p N ∪ oddPrimeUpperCentralSet p N) =
        Finset.Ico (b N) (L N) := by
  ext j
  simp only [oddPrimeUpperRetainedSet, Finset.mem_union, Finset.mem_sdiff]
  constructor
  · rintro (hj | hj | hj)
    · exact hj.1
    · exact oddPrimeUpperPairHighSet_subset_raw p N hj
    · exact oddPrimeUpperCentralSet_subset_raw p N hj
  · intro hj
    by_cases hp : j ∈ oddPrimeUpperPairHighSet p N
    · exact Or.inr (Or.inl hp)
    by_cases hc : j ∈ oddPrimeUpperCentralSet p N
    · exact Or.inr (Or.inr hc)
    · exact Or.inl ⟨hj, by simp [hp, hc]⟩

theorem oddPrimeUpperRetainedSet_mem_iff (p N j : ℕ) :
    j ∈ oddPrimeUpperRetainedSet p N ↔
      b N ≤ j ∧ j < L N ∧ (j < H N - p ∨ p ≤ j) ∧
        j ∉ oddPrimeUpperPairHighSet p N := by
  constructor
  · intro hj
    have hraw := Finset.mem_Ico.mp (Finset.mem_sdiff.mp hj).1
    have hnot := (Finset.mem_sdiff.mp hj).2
    refine ⟨hraw.1, hraw.2, ?_, fun hpair => hnot (Finset.mem_union.mpr (Or.inl hpair))⟩
    by_cases hJ : j < H N - p
    · exact Or.inl hJ
    · apply Or.inr
      by_contra hpj
      apply hnot
      apply Finset.mem_union.mpr
      apply Or.inr
      exact (oddPrimeUpperCentralSet_mem_iff p N j).mpr
        ⟨hraw.1, hraw.2, by omega, by omega⟩
  · rintro ⟨hb, hL, hside, hpair⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_Ico.mpr ⟨hb, hL⟩, ?_⟩
    intro hbad
    rcases Finset.mem_union.mp hbad with hbad | hbad
    · exact hpair hbad
    · have hc := (oddPrimeUpperCentralSet_mem_iff p N j).mp hbad
      rcases hside with hside | hside <;> omega

theorem oddPrimeUpperPairHighSet_card (p N : ℕ) :
    (oddPrimeUpperPairHighSet p N).card = min (A N) (L N - p) - b N := by
  rw [oddPrimeUpperPairHighSet, Nat.card_Ico]
  omega

theorem oddPrimeUpperCentralSet_card (p N : ℕ) :
    (oddPrimeUpperCentralSet p N).card = min p (L N) - max (b N) (H N - p) := by
  rw [oddPrimeUpperCentralSet, Nat.card_Ico]

theorem oddPrimeUpperRetainedSet_card (p N : ℕ) :
    (oddPrimeUpperRetainedSet p N).card =
      (L N - b N) - (min (A N) (L N - p) - b N) -
        (min p (L N) - max (b N) (H N - p)) := by
  have hsub : oddPrimeUpperPairHighSet p N ∪ oddPrimeUpperCentralSet p N ⊆
      Finset.Ico (b N) (L N) := by
    intro j hj
    rcases Finset.mem_union.mp hj with hpair | hcentral
    · exact oddPrimeUpperPairHighSet_subset_raw p N hpair
    · exact oddPrimeUpperCentralSet_subset_raw p N hcentral
  rw [oddPrimeUpperRetainedSet, Finset.card_sdiff_of_subset hsub,
    Finset.card_union_of_disjoint (oddPrimeUpperPairHighSet_disjoint_central p N),
    oddPrimeUpperPairHighSet_card, oddPrimeUpperCentralSet_card, Nat.card_Ico]
  omega

theorem oddPrimeUpperExceptionalSet_card (p N : ℕ) :
    (oddPrimeUpperExceptionalSet p N).card = min (b N) (H N - p) - (L N - p) := by
  rw [oddPrimeUpperExceptionalSet, Nat.card_Ico]

theorem oddPrimeUpperExceptionalSet_mem_iff (p N ell : ℕ) :
    ell ∈ oddPrimeUpperExceptionalSet p N ↔
      ell < H N - p ∧ ¬(b N ≤ ell ∨ ell < L N - p) := by
  simp only [oddPrimeUpperExceptionalSet, Finset.mem_Ico]
  omega

theorem oddPrimeUpperPairIndex_bounds {p N ell : ℕ} (hN : 0 < N)
    (hpH : p ≤ H N) (hH : H N ≤ 2 * p)
    (hell : ell ∈ Finset.Ico (b N) (min (A N) (L N - p))) :
    ell ∈ oddPrimeUpperRetainedSet p N ∧
      p + ell ∈ oddPrimeUpperPairHighSet p N ∧
        ell < p ∧ ell < H N - p := by
  have he := Finset.mem_Ico.mp hell
  have hLH : L N < H N := by unfold L H; omega
  have hellp : ell < p := by
    have hA : ell < A N := he.2.trans_le (Nat.min_le_left _ _)
    unfold H at hH
    unfold A at hA
    omega
  have hhigh : p + ell < L N := by omega
  have hellJ : ell < H N - p := by omega
  have hnot : ell ∉ oddPrimeUpperPairHighSet p N := by
    intro hh
    simp only [oddPrimeUpperPairHighSet, Finset.mem_Ico] at hh
    omega
  refine ⟨?_, ?_, hellp, hellJ⟩
  · exact (oddPrimeUpperRetainedSet_mem_iff p N ell).mpr
      ⟨he.1, by omega, Or.inl hellJ, hnot⟩
  · exact (oddPrimeUpperPairHighSet_mem_iff p N (p + ell)).mpr
      ⟨ell, he.1, he.2, rfl⟩

end InternalCatalan



noncomputable section

namespace InternalCatalan

def rawColumnPoolEquiv (N : ℕ) :
    Fin (n N + q N) ≃ ↥(Finset.Ico (b N) (L N)) where
  toFun c := ⟨b N + c.val, Finset.mem_Ico.mpr ⟨by omega, by
    have hc := c.isLt
    have hL := L_eq_n_add_b_add_q N
    omega⟩⟩
  invFun j := ⟨j.val - b N, by
    have hj := Finset.mem_Ico.mp j.property
    have hL := L_eq_n_add_b_add_q N
    omega⟩
  left_inv c := by
    apply Fin.ext
    change b N + c.val - b N = c.val
    omega
  right_inv j := by
    apply Subtype.ext
    change b N + (j.val - b N) = j.val
    have hj := Finset.mem_Ico.mp j.property
    omega

@[simp] theorem rawColumnPoolEquiv_apply_val (N : ℕ) (c : Fin (n N + q N)) :
    (rawColumnPoolEquiv N c).val = b N + c.val := rfl

@[simp] theorem rawColumnPoolEquiv_symm_apply_val (N : ℕ)
    (j : ↥(Finset.Ico (b N) (L N))) :
    ((rawColumnPoolEquiv N).symm j).val = j.val - b N := rfl

def oddPrimeUpperPoolSplit (p N : ℕ) :
    (↥(oddPrimeUpperRetainedSet p N) ⊕
      (↥(oddPrimeUpperPairHighSet p N) ⊕ ↥(oddPrimeUpperCentralSet p N))) ≃
        ↥(Finset.Ico (b N) (L N)) := by
  classical
  let f : (↥(oddPrimeUpperRetainedSet p N) ⊕
      (↥(oddPrimeUpperPairHighSet p N) ⊕ ↥(oddPrimeUpperCentralSet p N))) →
        ↥(Finset.Ico (b N) (L N)) := fun x => match x with
    | Sum.inl j => ⟨j.val, oddPrimeUpperRetainedSet_subset_raw p N j.property⟩
    | Sum.inr (Sum.inl j) => ⟨j.val, oddPrimeUpperPairHighSet_subset_raw p N j.property⟩
    | Sum.inr (Sum.inr j) => ⟨j.val, oddPrimeUpperCentralSet_subset_raw p N j.property⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    have hv := congrArg Subtype.val h
    rcases x with x | (x | x) <;> rcases y with y | (y | y)
    · change x.val = y.val at hv
      have hxy : x = y := Subtype.ext hv
      cases hxy
      rfl
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (oddPrimeUpperRetainedSet_disjoint_pairHigh p N)) (hv ▸ x.property) y.property)
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (oddPrimeUpperRetainedSet_disjoint_central p N)) (hv ▸ x.property) y.property)
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (oddPrimeUpperRetainedSet_disjoint_pairHigh p N)) y.property (hv ▸ x.property))
    · change x.val = y.val at hv
      have hxy : x = y := Subtype.ext hv
      cases hxy
      rfl
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (oddPrimeUpperPairHighSet_disjoint_central p N)) (hv ▸ x.property) y.property)
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (oddPrimeUpperRetainedSet_disjoint_central p N)) y.property (hv ▸ x.property))
    · change x.val = y.val at hv
      exact False.elim ((Finset.disjoint_left.mp
        (oddPrimeUpperPairHighSet_disjoint_central p N)) y.property (hv ▸ x.property))
    · change x.val = y.val at hv
      have hxy : x = y := Subtype.ext hv
      cases hxy
      rfl
  · intro j
    have hj : j.val ∈ oddPrimeUpperRetainedSet p N ∪
        (oddPrimeUpperPairHighSet p N ∪ oddPrimeUpperCentralSet p N) := by
      rw [oddPrimeUpperPool_partition]
      exact j.property
    rcases Finset.mem_union.mp hj with hr | hpc
    · exact ⟨Sum.inl ⟨j.val, hr⟩, rfl⟩
    · rcases Finset.mem_union.mp hpc with hp | hc
      · exact ⟨Sum.inr (Sum.inl ⟨j.val, hp⟩), rfl⟩
      · exact ⟨Sum.inr (Sum.inr ⟨j.val, hc⟩), rfl⟩

def oddPrimeUpperPoolEnumeration (p N : ℕ) :
    (Fin (Fintype.card ↥(oddPrimeUpperRetainedSet p N)) ⊕
      (Fin (Fintype.card ↥(oddPrimeUpperPairHighSet p N)) ⊕
        Fin (Fintype.card ↥(oddPrimeUpperCentralSet p N)))) ≃
          ↥(Finset.Ico (b N) (L N)) :=
  (Equiv.sumCongr (Fintype.equivFin ↥(oddPrimeUpperRetainedSet p N)).symm
    (Equiv.sumCongr (Fintype.equivFin ↥(oddPrimeUpperPairHighSet p N)).symm
      (Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm)).trans
        (oddPrimeUpperPoolSplit p N)

@[simp] theorem oddPrimeUpperPoolEnumeration_retained_val (p N : ℕ)
    (j : Fin (Fintype.card ↥(oddPrimeUpperRetainedSet p N))) :
    (oddPrimeUpperPoolEnumeration p N (Sum.inl j)).val =
      ((Fintype.equivFin ↥(oddPrimeUpperRetainedSet p N)).symm j).val := rfl

@[simp] theorem oddPrimeUpperPoolEnumeration_pairHigh_val (p N : ℕ)
    (j : Fin (Fintype.card ↥(oddPrimeUpperPairHighSet p N))) :
    (oddPrimeUpperPoolEnumeration p N (Sum.inr (Sum.inl j))).val =
      ((Fintype.equivFin ↥(oddPrimeUpperPairHighSet p N)).symm j).val := rfl

@[simp] theorem oddPrimeUpperPoolEnumeration_central_val (p N : ℕ)
    (j : Fin (Fintype.card ↥(oddPrimeUpperCentralSet p N))) :
    (oddPrimeUpperPoolEnumeration p N (Sum.inr (Sum.inr j))).val =
      ((Fintype.equivFin ↥(oddPrimeUpperCentralSet p N)).symm j).val := rfl

end InternalCatalan

end

end OAI
