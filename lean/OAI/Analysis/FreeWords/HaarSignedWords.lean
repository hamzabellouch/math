import Mathlib
import OAI.Analysis.FreeWords.ConjugateFree

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

def SameSign (k l : ℤ) : Prop := (0 < k ∧ 0 < l) ∨ (k < 0 ∧ l < 0)

theorem SameSign.symm {k l : ℤ} (h : SameSign k l) : SameSign l k := by
  rcases h with h | h <;> [left; right] <;> exact ⟨h.2,h.1⟩

theorem SameSign.trans {k l m : ℤ} (h : SameSign k l) (h' : SameSign l m) :
    SameSign k m := by
  rcases h with h | h <;> rcases h' with h' | h'
  · exact Or.inl ⟨h.1,h'.2⟩
  · omega
  · omega
  · exact Or.inr ⟨h.1,h'.2⟩

theorem SameSign.add_left {k l : ℤ} (h : SameSign k l) : SameSign (k+l) k := by
  rcases h with h | h <;> [left; right] <;> constructor <;> omega

theorem SameSign.add_right {k l : ℤ} (h : SameSign k l) : SameSign (k+l) l := by
  exact h.add_left.trans h

theorem SameSign.nonzero_left {k l : ℤ} (h : SameSign k l) : k ≠ 0 := by
  rcases h with h | h <;> omega

def SignedRelation (τ : A →ₚ[ℂ] ℂ) (a b : ℤ × A) : Prop :=
  τ a.2 = 0 ∨ SameSign a.1 b.1

def signedWord (s : unitary A) (w : List (ℤ × A)) : A :=
  (w.map (fun a => upow s a.1 * a.2)).prod

def signedExpansion (s : unitary A) (w : List (ℤ × A)) : List (Bool × A) :=
  w.flatMap (fun a => [(false, upow s a.1), (true, a.2)])

omit [PartialOrder A] [StarOrderedRing A] in
theorem signedExpansion_value (s : unitary A) (w : List (ℤ × A)) :
    ((signedExpansion s w).map Prod.snd).prod = signedWord s w := by
  induction w with
  | nil => simp [signedExpansion, signedWord]
  | cons a w ih =>
    simp only [signedExpansion, List.flatMap_cons, List.cons_append, List.nil_append,
      List.map_cons, List.prod_cons] at *
    rw [ih]
    simp [signedWord, mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
theorem signedExpansion_chain (s : unitary A) (w : List (ℤ × A)) :
    (signedExpansion s w).IsChain (fun a b => a.1 ≠ b.1) := by
  induction w with
  | nil => simp [signedExpansion]
  | cons a w ih =>
    cases w with
    | nil => simp [signedExpansion]
    | cons b w =>
      simpa [signedExpansion, List.isChain_cons_cons] using ih

omit [PartialOrder A] [StarOrderedRing A] in
theorem signedExpansion_end_chain (s : unitary A) (w : List (ℤ × A)) (k : ℤ) :
    (signedExpansion s w ++ [(false, upow s k)]).IsChain (fun a b => a.1 ≠ b.1) := by
  induction w with
  | nil => simp [signedExpansion]
  | cons a w ih =>
    cases w with
    | nil => simp [signedExpansion]
    | cons b w =>
      simpa [signedExpansion, List.isChain_cons_cons] using ih

omit [StarOrderedRing A] in
theorem signedExpansion_centered (s : unitary A) (hs : (s:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow s k) = 0) {w : List (ℤ × A)}
    (hw : ∀ a ∈ w, a.1 ≠ 0 ∧ a.2 ∈ P ∧ τ a.2 = 0) :
    ∀ a ∈ signedExpansion s w, a.2 ∈ binaryCopy S P a.1 ∧ τ a.2 = 0 := by
  intro a ha
  obtain ⟨b,hb,ha⟩ := List.mem_flatMap.mp ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl
  · exact ⟨upow_mem s hs _,hHaar _ (hw b hb).1⟩
  · exact (hw b hb).2

omit [StarOrderedRing A] in
theorem trace_signedWord_centered (s : unitary A) (hs : (s:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow s k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P)) {w : List (ℤ × A)} (hne : w ≠ [])
    (hw : ∀ a ∈ w, a.1 ≠ 0 ∧ a.2 ∈ P ∧ τ a.2 = 0) :
    τ (signedWord s w) = 0 := by
  have hne' : signedExpansion s w ≠ [] := by
    cases w with
    | nil => contradiction
    | cons a w => simp [signedExpansion]
  simpa only [signedExpansion_value] using
    hfree _ hne' (signedExpansion_chain s w) (signedExpansion_centered s hs hHaar hw)

omit [StarOrderedRing A] in
theorem trace_signedWord_end (s : unitary A) (hs : (s:A) ∈ S)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow s k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P)) {w : List (ℤ × A)}
    (hw : ∀ a ∈ w, a.1 ≠ 0 ∧ a.2 ∈ P ∧ τ a.2 = 0) (k : ℤ) (hk : k ≠ 0) :
    τ (signedWord s w * upow s k) = 0 := by
  have h := hfree (signedExpansion s w ++ [(false, upow s k)]) (by simp)
    (signedExpansion_end_chain s w k) (by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact signedExpansion_centered s hs hHaar hw a ha
      · have he : a = (false, upow s k) := by simpa using ha
        subst a
        exact ⟨upow_mem s hs _,hHaar _ hk⟩)
  simpa only [List.map_append, List.prod_append, List.map_cons, List.map_nil,
    List.prod_cons, List.prod_nil, mul_one, signedExpansion_value] using h

omit [StarOrderedRing A] in
theorem signedChain_center {p r : List (ℤ × A)} {k l : ℤ} {x x' y : A}
    (hx' : τ x' = 0) (h : (p ++ (k,x)::(l,y)::r).IsChain (SignedRelation τ)) :
    (p ++ (k,x')::(l,y)::r).IsChain (SignedRelation τ) := by
  induction p with
  | nil =>
    exact List.isChain_cons_cons.mpr ⟨Or.inl hx', (List.isChain_cons_cons.mp h).2⟩
  | cons a p ih =>
    cases p with
    | nil =>
      obtain ⟨ha,ht⟩ := List.isChain_cons_cons.mp h
      exact List.isChain_cons_cons.mpr ⟨ha,ih ht⟩
    | cons b p =>
      obtain ⟨ha,ht⟩ := List.isChain_cons_cons.mp h
      exact List.isChain_cons_cons.mpr ⟨ha,ih ht⟩

omit [StarOrderedRing A] in
theorem signedChain_merge {p r : List (ℤ × A)} {k l : ℤ} {x y : A}
    (hkl : SameSign k l) (h : (p ++ (k,x)::(l,y)::r).IsChain (SignedRelation τ)) :
    (p ++ (k+l,y)::r).IsChain (SignedRelation τ) := by
  induction p with
  | nil =>
    cases r with
    | nil => simp
    | cons b r =>
      obtain ⟨hb,ht⟩ := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp h).2)
      exact List.isChain_cons_cons.mpr ⟨by
        rcases hb with hb | hb
        · exact Or.inl hb
        · exact Or.inr (hkl.add_right.trans hb), ht⟩
  | cons a p ih =>
    cases p with
    | nil =>
      obtain ⟨ha,ht⟩ := List.isChain_cons_cons.mp h
      exact List.isChain_cons_cons.mpr ⟨by
        rcases ha with ha | ha
        · exact Or.inl ha
        · exact Or.inr (ha.trans hkl.add_left.symm), ih ht⟩
    | cons b p =>
      obtain ⟨ha,ht⟩ := List.isChain_cons_cons.mp h
      exact List.isChain_cons_cons.mpr ⟨ha,ih ht⟩

end

end KKFreeWords
end

end OAI
