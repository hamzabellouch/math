import Mathlib
import OAI.Analysis.FreeWords.HaarSignedWords

namespace OAI

noncomputable section

namespace KKFreeWords

open scoped BigOperators ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

omit [StarOrderedRing A]

theorem trace_signedWord_last (hτ : τ 1 = 1) (s : unitary A) (hs : (s:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow s k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P)) {w : List (ℤ × A)}
    (hw : ∀ a ∈ w, a.1 ≠ 0 ∧ a.2 ∈ P ∧ τ a.2 = 0)
    (k : ℤ) (hk : k ≠ 0) (x : A) (hx : x ∈ P) :
    τ (signedWord s (w ++ [(k,x)])) = 0 := by
  have hxc : τ (x - τ x • (1:A)) = 0 := by simp [map_sub, map_smul, hτ]
  have hmem : x - τ x • (1:A) ∈ P := P.sub_mem hx (P.smul_mem P.one_mem _)
  have hz := trace_signedWord_centered s hs hHaar hfree
    (w := w ++ [(k, x - τ x • (1:A))]) (by simp) (by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · have he : a = (k, x - τ x • (1:A)) := by simpa using ha
        subst a
        exact ⟨hk,hmem,hxc⟩)
  have he := trace_signedWord_end s hs hHaar hfree hw k hk
  have hsub :
      τ (signedWord s (w ++ [(k, x - τ x • (1:A))])) =
      τ (signedWord s (w ++ [(k,x)])) - τ x * τ (signedWord s w * upow s k) := by
    simp [signedWord, List.prod_append, mul_sub, map_sub, map_smul]
  rw [hz,he,mul_zero,sub_zero] at hsub
  exact hsub.symm

theorem trace_signedWord_interior (hτ : τ 1 = 1) (s : unitary A) (hs : (s:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow s k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P)) {w : List (ℤ × A)} (hne : w ≠ [])
    (hw : ∀ a ∈ w, a.1 ≠ 0 ∧ a.2 ∈ P)
    (hc : ∀ a ∈ w.dropLast, τ a.2 = 0) : τ (signedWord s w) = 0 := by
  have he := List.dropLast_append_getLast hne
  rw [← he]
  have hl := hw _ (List.getLast_mem hne)
  exact trace_signedWord_last hτ s hs hHaar hfree (fun a ha =>
    ⟨(hw a (List.mem_of_mem_dropLast ha)).1,
      (hw a (List.mem_of_mem_dropLast ha)).2, hc a ha⟩) _ hl.1 _ hl.2

theorem trace_signedWord_split (s : unitary A) (p r : List (ℤ × A))
    (k l : ℤ) (x y : A) :
    τ (signedWord s (p ++ (k,x)::(l,y)::r)) =
      τ (signedWord s (p ++ (k,x-τ x • (1:A))::(l,y)::r)) +
      τ x * τ (signedWord s (p ++ (k+l,y)::r)) := by
  simp only [signedWord, List.map_append, List.map_cons, List.prod_append, List.prod_cons,
    upow_add, mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one,
    map_sub, map_smul, smul_eq_mul]
  simp only [mul_assoc]
  ring

def badSeparators (τ : A →ₚ[ℂ] ℂ) (w : List (ℤ × A)) : ℕ :=
  w.countP (fun a => decide (τ a.2 ≠ 0))

theorem badSeparators_center (p r : List (ℤ × A)) (k l : ℤ) (x x' y : A)
    (hx : τ x ≠ 0) (hx' : τ x' = 0) :
    badSeparators τ (p ++ (k,x')::(l,y)::r) + 1 =
      badSeparators τ (p ++ (k,x)::(l,y)::r) := by
  simp [badSeparators, List.countP_cons, hx, hx']; omega

theorem badSeparators_merge (p r : List (ℤ × A)) (k l : ℤ) (x y : A)
    (hx : τ x ≠ 0) :
    badSeparators τ (p ++ (k+l,y)::r) + 1 =
      badSeparators τ (p ++ (k,x)::(l,y)::r) := by
  simp [badSeparators, List.countP_cons, hx]; omega

theorem exists_bad_separator {w : List (ℤ × A)}
    (h : ¬ ∀ a ∈ w.dropLast, τ a.2 = 0) :
    ∃ p a b r, w = p ++ a::b::r ∧ τ a.2 ≠ 0 := by
  induction w with
  | nil => simp at h
  | cons a w ih =>
    cases w with
    | nil => simp at h
    | cons b r =>
      by_cases ha : τ a.2 = 0
      · have ht : ¬ ∀ c ∈ (b::r).dropLast, τ c.2 = 0 := by
          intro hc
          apply h
          simpa [List.dropLast_cons_cons, ha] using hc
        obtain ⟨p,c,d,t,hp,hc⟩ := ih ht
        exact ⟨a::p,c,d,t,by simp [hp],hc⟩
      · exact ⟨[],a,b,r,rfl,ha⟩

theorem trace_signedWord (hτ : τ 1 = 1) (s : unitary A) (hs : (s:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow s k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P)) {w : List (ℤ × A)}
    (hne : w ≠ []) (hw : ∀ a ∈ w, a.1 ≠ 0 ∧ a.2 ∈ P)
    (hc : w.IsChain (SignedRelation τ)) : τ (signedWord s w) = 0 := by
  classical
  suffices H : ∀ n : ℕ, ∀ w : List (ℤ × A), badSeparators τ w ≤ n → w ≠ [] →
      (∀ a ∈ w, a.1 ≠ 0 ∧ a.2 ∈ P) → w.IsChain (SignedRelation τ) →
      τ (signedWord s w) = 0 from H _ w le_rfl hne hw hc
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro w hn hne hw hc
    by_cases hi : ∀ a ∈ w.dropLast, τ a.2 = 0
    · exact trace_signedWord_interior hτ s hs hHaar hfree hne hw hi
    · obtain ⟨p,⟨k,x⟩,⟨l,y⟩,r,rfl,hx⟩ := exists_bad_separator hi
      have hkx := hw (k,x) (by simp)
      have hly := hw (l,y) (by simp)
      have hkl : SameSign k l := by
        have hrel := (List.isChain_append_cons_cons.mp hc).2.1
        exact hrel.resolve_left hx
      have hxc : τ (x - τ x • (1:A)) = 0 := by simp [map_sub, map_smul, hτ]
      have hxp : x - τ x • (1:A) ∈ P := P.sub_mem hkx.2 (P.smul_mem P.one_mem _)
      let w₀ := p ++ (k,x-τ x • (1:A))::(l,y)::r
      let w₁ := p ++ (k+l,y)::r
      have hn₀ : badSeparators τ w₀ < n := by
        have hh := badSeparators_center p r k l x (x-τ x • (1:A)) y hx hxc
        change badSeparators τ w₀ + 1 = _ at hh
        omega
      have hn₁ : badSeparators τ w₁ < n := by
        have hh := badSeparators_merge p r k l x y hx
        change badSeparators τ w₁ + 1 = _ at hh
        omega
      have hm₀ : ∀ a ∈ w₀, a.1 ≠ 0 ∧ a.2 ∈ P := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hw a (List.mem_append_left _ ha)
        · rcases List.mem_cons.mp ha with rfl | ha
          · exact ⟨hkx.1,hxp⟩
          · exact hw a (List.mem_append_right _ (List.mem_cons_of_mem _ ha))
      have hm₁ : ∀ a ∈ w₁, a.1 ≠ 0 ∧ a.2 ∈ P := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hw a (List.mem_append_left _ ha)
        · rcases List.mem_cons.mp ha with rfl | ha
          · exact ⟨hkl.add_left.nonzero_left,hly.2⟩
          · exact hw a (by simp only [List.mem_append,List.mem_cons]; tauto)
      have hz₀ := ih _ hn₀ w₀ le_rfl (by simp [w₀]) hm₀ (signedChain_center hxc hc)
      have hz₁ := ih _ hn₁ w₁ le_rfl (by simp [w₁]) hm₁ (signedChain_merge hkl hc)
      exact (trace_signedWord_split s p r k l x y).trans (by rw [hz₀,hz₁,mul_zero,add_zero])

end

end KKFreeWords
end

end OAI
