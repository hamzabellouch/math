import Mathlib
import OAI.Analysis.FreeWords.HaarSignedTrace

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

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

def signInt (b : Bool) : ℤ := if b then 1 else -1

def unitaryLetter (u : unitary A) (b : Bool) : A := if b then u else star (u:A)

def twistLeft (U : unitary A) (b : Bool) : A := if b then 1 else star (U:A)

def twistRight (U : unitary A) (b : Bool) : A := if b then U else 1

def letterWord (u : unitary A) (w : List (Bool × A)) : A :=
  (w.map (fun a => unitaryLetter u a.1 * a.2)).prod

def twistExpansion (U : unitary A) (t : A) : List (Bool × A) → List (ℤ × A)
  | [] => []
  | [(b,x)] => [(signInt b, twistRight U b * x * t)]
  | (b,x)::(c,y)::r =>
    (signInt b, twistRight U b * x * twistLeft U c) :: twistExpansion U t ((c,y)::r)

omit [PartialOrder A] [StarOrderedRing A] in
theorem unitaryLetter_factor (s U : unitary A) (b : Bool) :
    twistLeft U b * upow s (signInt b) * twistRight U b = unitaryLetter (s*U) b := by
  cases b <;> simp [twistLeft,twistRight,signInt,unitaryLetter,upow, ← Unitary.star_eq_inv]

omit [PartialOrder A] [StarOrderedRing A] in
theorem twistLeft_mem (U : unitary A) (hU : (U:A) ∈ P) (b : Bool) :
    twistLeft U b ∈ P := by
  cases b <;> simp only [twistLeft,Bool.false_eq_true,ite_false,ite_true]
  · exact star_mem hU
  · exact P.one_mem

omit [PartialOrder A] [StarOrderedRing A] in
theorem twistRight_mem (U : unitary A) (hU : (U:A) ∈ P) (b : Bool) :
    twistRight U b ∈ P := by
  cases b <;> simp only [twistRight,Bool.false_eq_true,ite_false,ite_true]
  · exact P.one_mem
  · exact hU

omit [PartialOrder A] [StarOrderedRing A] in
theorem twistExpansion_mem (U : unitary A) (hU : (U:A) ∈ P) (t : A) (ht : t ∈ P)
    {w : List (Bool × A)} (hw : ∀ a ∈ w, a.2 ∈ P) :
    ∀ a ∈ twistExpansion U t w, a.1 ≠ 0 ∧ a.2 ∈ P := by
  induction w with
  | nil => simp [twistExpansion]
  | cons a w ih =>
    obtain ⟨b,x⟩ := a
    cases w with
    | nil =>
      intro a ha
      have he : a = (signInt b, twistRight U b*x*t) := by simpa [twistExpansion] using ha
      subst a
      exact ⟨by cases b <;> simp [signInt],
        P.mul_mem (P.mul_mem (twistRight_mem U hU b) (hw (b,x) (by simp))) ht⟩
    | cons c r =>
      obtain ⟨c,y⟩ := c
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact ⟨by cases b <;> simp [signInt],
          P.mul_mem (P.mul_mem (twistRight_mem U hU b) (hw (b,x) (by simp)))
            (twistLeft_mem U hU c)⟩
      · exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha)) a ha

def LetterRelation (τ : A →ₚ[ℂ] ℂ) (a b : Bool × A) : Prop :=
  a.1 ≠ b.1 → τ a.2 = 0

omit [StarOrderedRing A] in
theorem trace_unitarySandwich (hτ : ∀ x y, τ (x*y) = τ (y*x))
    (U : unitary A) (x : A) : τ ((U:A) * x * star (U:A)) = τ x := by
  rw [hτ]
  simp only [← mul_assoc]
  rw [Unitary.star_mul_self_of_mem U.property, one_mul]

omit [StarOrderedRing A] in
theorem twist_separator_relation (hτ : ∀ x y, τ (x*y) = τ (y*x))
    (U : unitary A) (b c : Bool) (x y : A)
    (h : b ≠ c → τ x = 0) :
    SignedRelation τ (signInt b,twistRight U b*x*twistLeft U c) (signInt c,y) := by
  cases b <;> cases c
  · right; norm_num [signInt,SameSign]
  · left; simpa [twistRight,twistLeft] using h (by decide)
  · left
    simpa only [twistRight,twistLeft,ite_true,Bool.false_eq_true,ite_false,
      trace_unitarySandwich hτ] using h (by decide)
  · right; norm_num [signInt,SameSign]

omit [StarOrderedRing A] in
theorem twistExpansion_chain (hτ : ∀ x y, τ (x*y) = τ (y*x))
    (U : unitary A) (t : A) {w : List (Bool × A)}
    (h : w.IsChain (LetterRelation τ)) :
    (twistExpansion U t w).IsChain (SignedRelation τ) := by
  induction w with
  | nil => simp [twistExpansion]
  | cons a w ih =>
    obtain ⟨b,x⟩ := a
    cases w with
    | nil => simp [twistExpansion]
    | cons a r =>
      obtain ⟨c,y⟩ := a
      obtain ⟨hb,ht⟩ := List.isChain_cons_cons.mp h
      have hh := ih ht
      cases r with
      | nil =>
        exact List.isChain_cons_cons.mpr ⟨twist_separator_relation hτ U b c x _ hb, hh⟩
      | cons a r =>
        obtain ⟨d,z⟩ := a
        exact List.isChain_cons_cons.mpr ⟨twist_separator_relation hτ U b c x _ hb, hh⟩

omit [PartialOrder A] [StarOrderedRing A] in
theorem twistExpansion_value (s U : unitary A) (t : A) (a : Bool × A)
    (w : List (Bool × A)) :
    twistLeft U a.1 * signedWord s (twistExpansion U t (a::w)) =
      letterWord (s*U) (a::w) * t := by
  induction w generalizing a with
  | nil =>
    obtain ⟨b,x⟩ := a
    calc
      _ = (twistLeft U b * upow s (signInt b) * twistRight U b) * x * t := by
        simp [twistExpansion,signedWord,mul_assoc]
      _ = _ := by rw [unitaryLetter_factor]; simp [letterWord,mul_assoc]
  | cons c w ih =>
    obtain ⟨b,x⟩ := a
    obtain ⟨c,y⟩ := c
    calc
      _ = (twistLeft U b * upow s (signInt b) * twistRight U b) * x *
          (twistLeft U c * signedWord s (twistExpansion U t ((c,y)::w))) := by
        simp only [twistExpansion,signedWord,List.map_cons,List.prod_cons]
        simp only [mul_assoc]
      _ = unitaryLetter (s*U) b * x * (letterWord (s*U) ((c,y)::w) * t) := by
        rw [unitaryLetter_factor,ih (c,y)]
      _ = _ := by simp [letterWord,mul_assoc]

omit [PartialOrder A] [StarOrderedRing A] in
theorem twistExpansion_right (s U : unitary A) (t : A) (a : Bool × A)
    (w : List (Bool × A)) :
    signedWord s (twistExpansion U t (a::w)) =
      signedWord s (twistExpansion U 1 (a::w)) * t := by
  induction w generalizing a with
  | nil => obtain ⟨b,x⟩ := a; simp [twistExpansion,signedWord,mul_assoc]
  | cons c w ih =>
    obtain ⟨b,x⟩ := a
    obtain ⟨c,y⟩ := c
    change (upow s (signInt b) * (twistRight U b*x*twistLeft U c)) *
      signedWord s (twistExpansion U t ((c,y)::w)) = _
    rw [ih]
    simp only [twistExpansion,signedWord,List.map_cons,List.prod_cons,mul_assoc]

omit [StarOrderedRing A] in
theorem trace_letterWord (hτ₁ : τ 1 = 1) (hτ : ∀ x y, τ (x*y) = τ (y*x))
    (s U : unitary A) (hs : (s:A) ∈ S) (hU : (U:A) ∈ P)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow s k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P)) {w : List (Bool × A)} (hne : w ≠ [])
    (hw : ∀ a ∈ w, a.2 ∈ P) (hc : w.IsChain (LetterRelation τ)) :
    τ (letterWord (s*U) w) = 0 := by
  cases w with
  | nil => contradiction
  | cons a w =>
    have hn : twistExpansion U (twistLeft U a.1) (a::w) ≠ [] := by
      obtain ⟨b,x⟩ := a
      cases w with
      | nil => simp [twistExpansion]
      | cons a w => obtain ⟨c,y⟩ := a; simp [twistExpansion]
    have hh := trace_signedWord hτ₁ s hs hHaar hfree hn
      (twistExpansion_mem U hU _ (twistLeft_mem U hU a.1) hw)
      (twistExpansion_chain hτ U _ hc)
    have hv := twistExpansion_value s U 1 a w
    rw [mul_one] at hv
    calc
      τ (letterWord (s*U) (a::w))
          = τ (twistLeft U a.1 * signedWord s (twistExpansion U 1 (a::w))) := by rw [hv]
      _ = τ (signedWord s (twistExpansion U 1 (a::w)) * twistLeft U a.1) := hτ _ _
      _ = τ (signedWord s (twistExpansion U (twistLeft U a.1) (a::w))) := by
        rw [twistExpansion_right s U (twistLeft U a.1) a w]
      _ = 0 := hh

end

end KKFreeWords
end

end OAI
