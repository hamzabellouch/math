import OAI.NumberTheory.Ostmann.Arithmetic.HistorySupportDescentIntegrality
import OAI.NumberTheory.Ostmann.Construction.History

namespace OAI

namespace Ostmann.Arithmetic.HistorySupportDescent
open Construction

private theorem move_giant {p X : ℕ} {u h O : List ℕ}
    (hc : (p :: (u ++ ((X :: h) ++ O))).Pairwise Nat.Coprime) :
    ((p :: X :: (u ++ h)) ++ O).Pairwise Nat.Coprime := by
  have he : (p :: (u ++ (X :: h))).Perm (p :: X :: (u ++ h)) :=
    List.Perm.cons p List.perm_middle
  apply ((he.append_right O).pairwise_iff Nat.Coprime.symm).mp
  simpa only [List.cons_append,List.append_assoc] using hc

theorem child_lists_coprime (a : State) (p : ℕ) (u hp hm : List SmallSlot)
    (outside : List ℕ) (v w : ℤ)
    (hparent : a.Coprime outside) (hperm : a.small.Perm (hp ++ hm))
    (hv : IsCoprime v ((a.giantPlus * (hp.map SmallSlot.value).prod : ℕ) : ℤ))
    (hw : IsCoprime w ((a.giantMinus * (hm.map SmallSlot.value).prod : ℕ) : ℤ))
    (hN : reversalNumerator v w
      ((a.giantPlus * (hp.map SmallSlot.value).prod : ℕ) : ℤ)
      ((a.giantMinus * (hm.map SmallSlot.value).prod : ℕ) : ℤ) =
      a.frequency * ((u.map SmallSlot.value).prod : ℤ) * (p : ℤ))
    (hu : (u.map SmallSlot.value).Nodup) (huprime : ∀ b ∈ u, Nat.Prime b.value)
    (hsq : ∀ b ∈ u, ¬ (b.value : ℤ) * b.value ∣ reversalNumerator v w
      ((a.giantPlus * (hp.map SmallSlot.value).prod : ℕ) : ℤ)
      ((a.giantMinus * (hm.map SmallSlot.value).prod : ℕ) : ℤ))
    (hpO : ∀ q ∈ outside, Nat.Coprime p q)
    (huO : ∀ b ∈ u, ∀ q ∈ outside, Nat.Coprime b.value q) :
    ((p :: a.giantPlus :: (u ++ hp).map SmallSlot.value) ++ outside).Pairwise Nat.Coprime ∧
    ((p :: a.giantMinus :: (u ++ hm).map SmallSlot.value) ++ outside).Pairwise Nat.Coprime := by
  have hvalues : a.values.Perm ((a.giantPlus :: hp.map SmallSlot.value) ++
      (a.giantMinus :: hm.map SmallSlot.value)) := by
    have h₁ := List.Perm.cons a.giantPlus (List.Perm.cons a.giantMinus (hperm.map SmallSlot.value))
    simp only [List.map_append] at h₁
    exact h₁.trans (List.Perm.cons _ List.perm_middle.symm)
  have hbase : ((a.giantPlus :: hp.map SmallSlot.value) ++
      ((a.giantMinus :: hm.map SmallSlot.value) ++ outside)).Pairwise Nat.Coprime := by
    simpa only [List.append_assoc] using
      ((hvalues.append_right outside).pairwise_iff Nat.Coprime.symm).mp hparent
  have huprime' : ∀ b ∈ u.map SmallSlot.value, Nat.Prime b := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact huprime c hc
  have hsq' : ∀ b ∈ u.map SmallSlot.value, ¬ (b : ℤ) * b ∣ reversalNumerator v w
      (((a.giantPlus :: hp.map SmallSlot.value).prod : ℕ) : ℤ)
      (((a.giantMinus :: hm.map SmallSlot.value).prod : ℕ) : ℤ) := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact hsq c hc
  have huO' : ∀ b ∈ u.map SmallSlot.value, ∀ q ∈ outside, Nat.Coprime b q := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hb
    exact huO c hc
  obtain ⟨hl,hr⟩ := children_pairwise hbase hv hw hN
    (prime_list_pairwise hu huprime') huprime' hsq' hpO huO'
  exact ⟨by simpa only [List.map_append] using move_giant hl,
    by simpa only [List.map_append] using move_giant hr⟩

theorem state_coprime_of_child_list {child : State} {p X : ℕ}
    {u inherited : List SmallSlot} {outside : List ℕ}
    (hplus : child.giantPlus = p) (hminus : child.giantMinus = X)
    (hsmall : child.small.Perm (u ++ inherited))
    (hc : ((p :: X :: (u ++ inherited).map SmallSlot.value) ++ outside).Pairwise Nat.Coprime) :
    child.Coprime outside := by
  have hp : child.values.Perm (p :: X :: (u ++ inherited).map SmallSlot.value) := by
    simpa only [State.values,hplus,hminus] using
      List.Perm.cons p (List.Perm.cons X (hsmall.map SmallSlot.value))
  exact ((hp.append_right outside).pairwise_iff Nat.Coprime.symm).mpr hc

end Ostmann.Arithmetic.HistorySupportDescent

end OAI
