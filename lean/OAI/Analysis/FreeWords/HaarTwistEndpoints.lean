import Mathlib
import OAI.Analysis.FreeWords.HaarTwistMoments

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

variable {τ : A →ₚ[ℂ] ℂ}

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

omit [StarOrderedRing A] in
theorem powerBlocks_chain_last_free {w : List (ℤ × A)}
    (hw : w.IsChain (fun a _ => τ a.2 = 0)) :
    (powerBlocks w).IsChain (LetterRelation τ) := by
  induction w with
  | nil => simp [powerBlocks]
  | cons a w ih =>
    cases w with
    | nil => simpa [powerBlocks] using powerBlock_chain a.1 a.2
    | cons b w =>
      have hx : τ a.2 = 0 := (List.isChain_cons_cons.mp hw).1
      exact powerBlock_chain_append a.1 a.2 hx
        (ih (List.isChain_cons_cons.mp hw).2)

omit [StarOrderedRing A] in
theorem trace_twisted_signedWord (hτ : FaithfulTracial τ)
    (s U : unitary A) (hs : (s:A) ∈ S) (hU : (U:A) ∈ P)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow s k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P)) {w : List (ℤ × A)} (hne : w ≠ [])
    (hw : ∀ a ∈ w, a.1 ≠ 0 ∧ a.2 ∈ P)
    (hc : w.IsChain (fun a _ => τ a.2 = 0)) :
    τ (signedWord (s*U) w) = 0 := by
  have hk : ∀ a ∈ w, a.1 ≠ 0 := fun a ha => (hw a ha).1
  have hz := trace_letterWord hτ.1 hτ.2.1 s U hs hU hHaar hfree
    (powerBlocks_ne_nil hne hk) (powerBlocks_mem (fun a ha => (hw a ha).2))
    (powerBlocks_chain_last_free hc)
  simpa only [powerBlocks_value _ hk] using hz

def signedMulLast (t : A) : List (ℤ × A) → List (ℤ × A)
  | [] => []
  | [(k,x)] => [(k,x*t)]
  | a::b::w => a :: signedMulLast t (b::w)

omit [PartialOrder A] [StarOrderedRing A] in
theorem signedMulLast_value (u : unitary A) (t : A) {w : List (ℤ × A)} (hne : w ≠ []) :
    signedWord u (signedMulLast t w) = signedWord u w * t := by
  induction w with
  | nil => contradiction
  | cons a w ih =>
    cases w with
    | nil => simp [signedMulLast,signedWord,mul_assoc]
    | cons b w =>
      simpa only [signedMulLast,signedWord,List.map_cons,List.prod_cons,mul_assoc]
        using congrArg (fun z => upow u a.1 * a.2 * z) (ih (by simp))

omit [PartialOrder A] [StarOrderedRing A] in
theorem signedMulLast_ne_nil (t : A) {w : List (ℤ × A)} (hne : w ≠ []) :
    signedMulLast t w ≠ [] := by
  cases w with
  | nil => contradiction
  | cons a w => cases w <;> simp [signedMulLast]

omit [PartialOrder A] [StarOrderedRing A] in
theorem signedMulLast_mem (t : A) (ht : t ∈ P) {w : List (ℤ × A)}
    (hw : ∀ a ∈ w, a.1 ≠ 0 ∧ a.2 ∈ P) :
    ∀ a ∈ signedMulLast t w, a.1 ≠ 0 ∧ a.2 ∈ P := by
  induction w with
  | nil => simp [signedMulLast]
  | cons a w ih =>
    have ha := hw a (by simp)
    cases w with
    | nil =>
      intro b hb
      simp only [signedMulLast,List.mem_singleton] at hb
      subst b
      exact ⟨ha.1,P.mul_mem ha.2 ht⟩
    | cons b w =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact ha
      · exact ih (fun z hz => hw z (List.mem_cons_of_mem _ hz)) c hc

omit [StarOrderedRing A] in
theorem signedMulLast_chain (t : A) {w : List (ℤ × A)}
    (hw : w.IsChain (fun a _ => τ a.2 = 0)) :
    (signedMulLast t w).IsChain (fun a _ => τ a.2 = 0) := by
  induction w with
  | nil => simp [signedMulLast]
  | cons a w ih =>
    cases w with
    | nil => simp [signedMulLast]
    | cons b w =>
      have ha : τ a.2 = 0 := (List.isChain_cons_cons.mp hw).1
      have hb := ih (List.isChain_cons_cons.mp hw).2
      cases w with
      | nil => simpa [signedMulLast] using ha
      | cons c w =>
        exact List.isChain_cons_cons.mpr ⟨ha,hb⟩

end

end KKFreeWords
end

end OAI
