import OAI.Computability.StarHeight.Model

namespace OAI

namespace GeneralizedStarHeight

universe u
universe uι uι2

namespace HasHeightAtMost

open scoped Computability

variable {Alphabet : Type u} {L M : Language Alphabet} {n k : ℕ}

lemma mono (h : HasHeightAtMost L n) (hn : n ≤ k) : HasHeightAtMost L k := by
  obtain ⟨P, rfl, hP⟩ := h
  exact ⟨P, rfl, hP.trans hn⟩

lemma zero (n : ℕ) : HasHeightAtMost (0 : Language Alphabet) n :=
  ⟨Expression.zero, rfl, Nat.zero_le _⟩

lemma one (n : ℕ) : HasHeightAtMost (1 : Language Alphabet) n :=
  ⟨Expression.one, rfl, Nat.zero_le _⟩

lemma letter (a : Alphabet) (n : ℕ) : HasHeightAtMost ({[a]} : Language Alphabet) n :=
  ⟨Expression.letter a, rfl, Nat.zero_le _⟩

lemma union (hL : HasHeightAtMost L n) (hM : HasHeightAtMost M n) :
    HasHeightAtMost (L + M) n := by
  obtain ⟨P, rfl, hP⟩ := hL
  obtain ⟨Q, rfl, hQ⟩ := hM
  exact ⟨P.union Q, rfl, max_le hP hQ⟩

lemma concat (hL : HasHeightAtMost L n) (hM : HasHeightAtMost M n) :
    HasHeightAtMost (L * M) n := by
  obtain ⟨P, rfl, hP⟩ := hL
  obtain ⟨Q, rfl, hQ⟩ := hM
  exact ⟨P.concat Q, rfl, max_le hP hQ⟩

lemma compl (hL : HasHeightAtMost L n) : HasHeightAtMost Lᶜ n := by
  obtain ⟨P, rfl, hP⟩ := hL
  exact ⟨P.compl, rfl, hP⟩

lemma inter (hL : HasHeightAtMost L n) (hM : HasHeightAtMost M n) :
    HasHeightAtMost (L ⊓ M) n := by
  have h := (hL.compl.union hM.compl).compl
  have heq : ((Lᶜ + Mᶜ)ᶜ : Language Alphabet) = L ⊓ M := by
    ext x
    change (¬(x ∉ L ∨ x ∉ M)) ↔ x ∈ L ∧ x ∈ M
    tauto
  exact heq ▸ h

lemma star (hL : HasHeightAtMost L n) : HasHeightAtMost L∗ (1 + n) := by
  obtain ⟨P, rfl, hP⟩ := hL
  exact ⟨P.star, rfl, Nat.add_le_add_left hP 1⟩

lemma finset_iSup {ι : Type uι} (s : Finset ι) (L : ι → Language Alphabet)
    (h : ∀ i ∈ s, HasHeightAtMost (L i) n) :
    HasHeightAtMost (⨆ i ∈ s, L i) n := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.notMem_empty, iSup_false, iSup_bot]
      exact zero n
  | @insert i s hi ih =>
      rw [Finset.iSup_insert]
      exact (h i (Finset.mem_insert_self _ _)).union
        (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

lemma iSup {ι : Type uι2} [Finite ι] (L : ι → Language Alphabet)
    (h : ∀ i, HasHeightAtMost (L i) n) : HasHeightAtMost (⨆ i, L i) n := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  simpa using finset_iSup Finset.univ L (fun i _ => h i)

lemma singleton (w : List Alphabet) (n : ℕ) :
    HasHeightAtMost ({w} : Language Alphabet) n := by
  induction w with
  | nil => exact one n
  | cons a w ih =>
      have h := (letter a n).concat ih
      convert h using 1
      apply Language.ext
      intro x
      change (x = a :: w) ↔ _
      rw [Language.mem_mul]
      change (x = a :: w) ↔ ∃ s, s = [a] ∧ ∃ t, t = w ∧ s ++ t = x
      simp [eq_comm]

lemma finite (L : Language Alphabet) (hL : (L : Set (List Alphabet)).Finite) (n : ℕ) :
    HasHeightAtMost L n := by
  have heq : L = ⨆ w : {w : List Alphabet // w ∈ L}, ({w.1} : Language Alphabet) := by
    ext x
    rw [Language.mem_iSup]
    change (x ∈ L) ↔ ∃ w : {w : List Alphabet // w ∈ L}, x = w.1
    simp
  let : Finite {w : List Alphabet // w ∈ L} := hL.to_subtype
  rw [heq]
  exact iSup _ (fun w => singleton w.1 n)

end HasHeightAtMost

end GeneralizedStarHeight

end OAI
