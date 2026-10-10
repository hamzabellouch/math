import Mathlib

namespace OAI

noncomputable section
open Set

namespace Invariant233.ReturnTowers

variable {X : Type*} [AddCommGroup X]

def returnBase (a : X) (B : Set X) (n : ℕ) : Set X :=
  {x | x ∈ B ∧ 0 < n ∧ x + n • a ∈ B ∧
    ∀ j : ℕ, 0 < j → j < n → x + j • a ∉ B}

def level (a : X) (B : Set X) (n k : ℕ) : Set X :=
  (fun x => x + k • a) '' returnBase a B n

theorem returnBase_unique {a : X} {B : Set X} {x : X} {n m : ℕ}
    (hn : x ∈ returnBase a B n) (hm : x ∈ returnBase a B m) : n = m := by
  rcases hn with ⟨hx, hn, hxn, hminn⟩
  rcases hm with ⟨_, hm, hxm, hminm⟩
  rcases lt_trichotomy n m with h | h | h
  · exact False.elim (hminm n hn h hxn)
  · exact h
  · exact False.elim (hminn m hm h hxm)

theorem level_indices_eq_of_mem {a : X} {B : Set X} {z : X} {n m k l : ℕ}
    (hk : k < n) (hl : l < m)
    (hzn : z ∈ level a B n k) (hzm : z ∈ level a B m l) :
    n = m ∧ k = l := by
  obtain ⟨x, hx, hxz⟩ := hzn
  obtain ⟨y, hy, hyz⟩ := hzm
  have heq : x + k • a = y + l • a := hxz.trans hyz.symm
  have hkl : k = l := by
    rcases lt_trichotomy k l with h | h | h
    · have hs : (y + (l - k) • a) + k • a = y + l • a := by
        rw [add_assoc, ← add_nsmul, Nat.sub_add_cancel h.le]
      have hxy : x = y + (l - k) • a := add_right_cancel (heq.trans hs.symm)
      exact False.elim (hy.2.2.2 (l - k) (by omega) (by omega) (hxy ▸ hx.1))
    · exact h
    · have hs : (x + (k - l) • a) + l • a = x + k • a := by
        rw [add_assoc, ← add_nsmul, Nat.sub_add_cancel h.le]
      have hyx : y = x + (k - l) • a := add_right_cancel (heq.symm.trans hs.symm)
      exact False.elim (hx.2.2.2 (k - l) (by omega) (by omega) (hyx ▸ hy.1))
  subst l
  have hxy : x = y := add_right_cancel heq
  subst y
  exact ⟨returnBase_unique hx hy, rfl⟩

theorem level_disjoint {a : X} {B : Set X} {n m k l : ℕ}
    (hk : k < n) (hl : l < m) (hne : (n, k) ≠ (m, l)) :
    Disjoint (level a B n k) (level a B m l) := by
  apply Set.disjoint_left.mpr
  intro z hn hm
  obtain ⟨rfl, rfl⟩ := level_indices_eq_of_mem hk hl hn hm
  exact hne rfl

theorem exists_returnBase {a : X} {B : Set X} {M : ℕ} {x : X}
    (hx : x ∈ B) (hhit : ∃ n : ℕ, 0 < n ∧ n ≤ M ∧ x + n • a ∈ B) :
    ∃ n : ℕ, n ≤ M ∧ x ∈ returnBase a B n := by
  classical
  have hex : ∃ n : ℕ, 0 < n ∧ x + n • a ∈ B := by
    obtain ⟨n, hn, _, hmem⟩ := hhit
    exact ⟨n, hn, hmem⟩
  refine ⟨Nat.find hex, ?_, hx, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  · obtain ⟨n, hn, hnM, hmem⟩ := hhit
    exact (Nat.find_min' hex ⟨hn, hmem⟩).trans hnM
  · intro j hj hjn hjmem
    exact (Nat.find_min hex hjn) ⟨hj, hjmem⟩

theorem exists_level_of_hitting {a : X} {B : Set X} {M : ℕ}
    (hreturn : ∀ x ∈ B, ∃ n : ℕ, 0 < n ∧ n ≤ M ∧ x + n • a ∈ B)
    (hback : ∀ z : X, ∃ k : ℕ, z - k • a ∈ B) (z : X) :
    ∃ n k : ℕ, 0 < n ∧ n ≤ M ∧ k < n ∧ z ∈ level a B n k := by
  classical
  let k := Nat.find (hback z)
  let x := z - k • a
  have hx : x ∈ B := Nat.find_spec (hback z)
  obtain ⟨n, hnM, hn⟩ := exists_returnBase hx (hreturn x hx)
  have hkn : k < n := by
    by_contra h
    have hnk : n ≤ k := by omega
    have heq : z - (k - n) • a = x + n • a := by
      dsimp [x]
      rw [sub_nsmul a hnk]
      abel
    have hsmall : k ≤ k - n := Nat.find_min' (hback z) (heq ▸ hn.2.2.1)
    have hnpos := hn.2.1
    omega
  exact ⟨n, k, hn.2.1, hnM, hkn, x, hn, by simp [x]⟩

@[simp]
theorem returnBase_zero (a : X) (B : Set X) : returnBase a B 0 = ∅ := by
  ext x
  simp [returnBase]

@[simp]
theorem level_zero (a : X) (B : Set X) (n : ℕ) : level a B n 0 = returnBase a B n := by
  simp [level]

theorem image_level_succ (a : X) (B : Set X) (n k : ℕ) :
    (fun x => x + a) '' level a B n k = level a B n (k + 1) := by
  simp only [level, Set.image_image]
  congr 1
  funext x
  simp [add_nsmul, add_assoc]

theorem image_level_top_subset (a : X) (B : Set X) (n : ℕ) :
    (fun x => x + a) '' level a B n (n - 1) ⊆ B := by
  rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
  have hn : 1 ≤ n := hx.2.1
  have heq : (n - 1) • a + a = n • a := by
    simpa only [add_nsmul, one_nsmul] using
      congrArg (fun j : ℕ => j • a) (Nat.sub_add_cancel hn)
  change (x + (n - 1) • a) + a ∈ B
  rw [add_assoc, heq]
  exact hx.2.2.1

theorem level_disjoint_base {a : X} {B : Set X} {n k : ℕ}
    (hk0 : 0 < k) (hkn : k < n) : Disjoint (level a B n k) B := by
  apply Set.disjoint_left.mpr
  rintro z ⟨x, hx, rfl⟩ hz
  exact hx.2.2.2 k hk0 hkn hz

theorem height_lt_of_disjoint_translates {a : X} {B : Set X} {L n : ℕ}
    (hdisj : ∀ j : ℕ, 0 < j → j ≤ L →
      Disjoint ((fun x => x + j • a) '' B) B)
    (hne : (returnBase a B n).Nonempty) : L < n := by
  obtain ⟨x, hx⟩ := hne
  by_contra h
  exact Set.disjoint_left.mp (hdisj n hx.2.1 (by omega))
    ⟨x, hx.1, rfl⟩ hx.2.2.1

section Measurable
variable [MeasurableSpace X] [MeasurableAdd₂ X] [MeasurableNeg X]

omit [MeasurableNeg X] in

theorem measurableSet_returnBase (a : X) {B : Set X} (hB : MeasurableSet B) (n : ℕ) :
    MeasurableSet (returnBase a B n) := by
  unfold returnBase
  apply MeasurableSet.inter hB
  apply MeasurableSet.inter (show MeasurableSet {x : X | 0 < n} from by
    by_cases hn : 0 < n
    · convert MeasurableSet.univ (α := X) using 1
      ext x
      exact iff_true_intro hn
    · convert MeasurableSet.empty (α := X) using 1
      ext x
      exact iff_false_intro hn)
  apply MeasurableSet.inter (hB.preimage (measurable_id.add_const _))
  have hm : MeasurableSet (⋂ j : ℕ, ⋂ (_ : 0 < j), ⋂ (_ : j < n),
      ((fun x : X => x + j • a) ⁻¹' B)ᶜ) :=
    MeasurableSet.iInter fun j => MeasurableSet.iInter fun _ =>
      MeasurableSet.iInter fun _ => (hB.preimage (measurable_id.add_const _)).compl
  have heq : {x : X | ∀ j : ℕ, 0 < j → j < n → x + j • a ∉ B} =
      ⋂ j : ℕ, ⋂ (_ : 0 < j), ⋂ (_ : j < n),
        ((fun x : X => x + j • a) ⁻¹' B)ᶜ := by
    ext x
    simp only [Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage]
    rfl
  change MeasurableSet {x : X | ∀ j : ℕ, 0 < j → j < n → x + j • a ∉ B}
  rw [heq]
  exact hm

theorem measurableSet_level (a : X) {B : Set X} (hB : MeasurableSet B) (n k : ℕ) :
    MeasurableSet (level a B n k) := by
  have heq : level a B n k = (fun z => z - k • a) ⁻¹' returnBase a B n := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
    · intro hz
      exact ⟨z - k • a, hz, sub_add_cancel z _⟩
  rw [heq]
  exact (measurableSet_returnBase a hB n).preimage (measurable_id.sub_const _)

end Measurable

end Invariant233.ReturnTowers

end

end OAI
