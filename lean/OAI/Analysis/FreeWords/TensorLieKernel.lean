import Mathlib

namespace OAI

noncomputable section

namespace KKWeingarten

open scoped BigOperators

noncomputable section

def LieInvariant {r d : ℕ} (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ) : Prop :=
  ∀ (i j : Fin d) (a b : Fin r → Fin d),
    (∑ s, if a s = i then T (Function.update a s j) b else 0) =
    ∑ s, if b s = j then T a (Function.update b s i) else 0

theorem image_update_duplicate {r d : ℕ} (a : Fin r → Fin d)
    (s t : Fin r) (hst : s ≠ t) (hat : a s = a t) (k : Fin d) :
    Finset.univ.image (Function.update a s k) = insert k (Finset.univ.image a) := by
  classical
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_insert]
  constructor
  · rintro ⟨u,hu⟩
    by_cases hus : u=s
    · subst u
      left
      simpa using hu.symm
    · right
      exact ⟨u,by simpa [Function.update_of_ne hus] using hu⟩
  · rintro (rfl | ⟨u,rfl⟩)
    · exact ⟨s,by simp⟩
    · by_cases hus : u=s
      · subst u
        exact ⟨t,by simpa [Function.update_of_ne hst.symm] using hat.symm⟩
      · exact ⟨u,by simp [Function.update_of_ne hus]⟩

theorem lieInvariant_eq_zero_of_injective_rows {r d : ℕ} (hrd : r ≤ d)
    (T : Matrix (Fin r → Fin d) (Fin r → Fin d) ℂ) (hT : LieInvariant T)
    (hz : ∀ a, Function.Injective a → ∀ b, T a b=0) : T=0 := by
  classical
  have hmain (m : ℕ) : ∀ a : Fin r → Fin d,
      r - (Finset.univ.image a).card=m → ∀ b, T a b=0 := by
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro a hm b
      by_cases hai : Function.Injective a
      · exact hz a hai b
      · obtain ⟨s,t,hat,hst⟩ := Function.not_injective_iff.mp hai
        have hc : (Finset.univ.image a).card < r := by
          have hle := Finset.card_image_le (s := Finset.univ) (f := a)
          have hne : (Finset.univ.image a).card ≠ r := by
            intro heq
            have hh := Finset.card_image_iff.mp (show (Finset.univ.image a).card = Finset.univ.card by simpa using heq)
            exact hai (fun x y hxy => hh (Finset.mem_univ x) (Finset.mem_univ y) hxy)
          simpa using lt_of_le_of_ne (by simpa using hle) hne
        obtain ⟨k,hk⟩ : ∃ k : Fin d, k ∉ Finset.univ.image a := by
          by_contra hh
          push Not at hh
          have heq : Finset.univ.image a = Finset.univ := Finset.eq_univ_of_forall hh
          have hcard := congrArg Finset.card heq
          simp only [Finset.card_univ,Fintype.card_fin] at hcard
          omega
        let a' := Function.update a s k
        have hc' : (Finset.univ.image a').card = (Finset.univ.image a).card+1 := by
          rw [show a'=Function.update a s k from rfl, image_update_duplicate a s t hst hat,
            Finset.card_insert_of_notMem hk]
        have hlt : r - (Finset.univ.image a').card < m := by omega
        have ha' : ∀ b, T a' b=0 := ih _ hlt a' rfl
        have hsp : ∀ u : Fin r, a' u=k ↔ u=s := by
          intro u
          by_cases hus : u=s
          · subst u; simp [a']
          · have hau : a u ≠ k := fun heq => hk (Finset.mem_image.mpr ⟨u,Finset.mem_univ u,heq⟩)
            simp [a',hus,hau]
        have hid : Function.update a' s (a s)=a := by
          simp [a',Function.update_idem]
        have he := hT k (a s) a' b
        simp only [hsp] at he
        rw [Finset.sum_eq_single s] at he
        · simpa [hid,ha'] using he
        · intro u _ hus
          simp [hus]
        · simp
  ext a b
  exact hmain _ a rfl b

end

end KKWeingarten
end

end OAI
