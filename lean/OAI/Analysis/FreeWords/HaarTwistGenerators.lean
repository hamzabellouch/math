import Mathlib
import OAI.Analysis.FreeWords.HaarTwistEndpoints

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

end

end KKFreeWords

namespace KKFreeWords

open scoped ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable {τ : A →ₚ[ℂ] ℂ} {S P : StarSubalgebra ℂ A}

def powerPSet (τ : A →ₚ[ℂ] ℂ) (u : unitary A) (P : StarSubalgebra ℂ A)
    (b : Bool) : Set A :=
  if b then {x | x ∈ P ∧ τ x = 0} else {x | ∃ k : ℤ, k ≠ 0 ∧ upow u k = x}

omit [StarOrderedRing A] in
theorem parse_power_word (u : unitary A) {a : A} {w : List (Bool × A)}
    (hchain : ((false,a)::w).IsChain (fun x y => x.1 ≠ y.1))
    (hmem : ∀ x ∈ (false,a)::w, x.2 ∈ powerPSet τ u P x.1) :
    ∃ v : List (ℤ × A), v ≠ [] ∧
      (∀ x ∈ v, x.1 ≠ 0 ∧ x.2 ∈ P) ∧
      v.IsChain (fun x _ => τ x.2 = 0) ∧
      (((false,a)::w).map Prod.snd).prod = signedWord u v := by
  induction w using List.twoStepInduction generalizing a with
  | nil =>
    obtain ⟨k,hk,rfl⟩ := hmem (false,a) (by simp)
    refine ⟨[(k,1)],by simp,?_,by simp,?_⟩
    · simpa using And.intro hk P.one_mem
    · simp [signedWord]
  | singleton b =>
    obtain ⟨b,y⟩ := b
    cases b with
    | false => simp at hchain
    | true =>
      obtain ⟨k,hk,rfl⟩ := hmem (false,a) (by simp)
      have hy : y ∈ P ∧ τ y = 0 := hmem (true,y) (by simp)
      refine ⟨[(k,y)],by simp,?_,by simp,?_⟩
      · simpa using And.intro hk hy.1
      · simp [signedWord]
  | cons_cons b c w ih _ =>
    obtain ⟨b,y⟩ := b
    obtain ⟨c,z⟩ := c
    cases b with
    | false => simp at hchain
    | true =>
      cases c with
      | true => simp at hchain
      | false =>
        obtain ⟨k,hk,rfl⟩ := hmem (false,a) (by simp)
        have hy : y ∈ P ∧ τ y = 0 := hmem (true,y) (by simp)
        have hct := (List.isChain_cons_cons.mp (List.isChain_cons_cons.mp hchain).2).2
        have hmt : ∀ x ∈ (false,z)::w, x.2 ∈ powerPSet τ u P x.1 :=
          fun x hx => hmem x (by simp only [List.mem_cons] at hx ⊢; tauto)
        obtain ⟨v,hvn,hvm,hvc,hvv⟩ := ih hct hmt
        refine ⟨(k,y)::v,by simp,?_,?_,?_⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact ⟨hk,hy.1⟩
          · exact hvm x hx
        · cases v with
          | nil => contradiction
          | cons x v => exact List.isChain_cons_cons.mpr ⟨hy.2,hvc⟩
        · simp only [List.map_cons,List.prod_cons,signedWord] at hvv ⊢
          rw [← mul_assoc, hvv]

omit [StarOrderedRing A] in
theorem trace_twisted_generator_word (hτ : FaithfulTracial τ)
    (s U : unitary A) (hs : (s:A) ∈ S) (hU : (U:A) ∈ P)
    (hHaar : ∀ k : ℤ, k ≠ 0 → τ (upow s k) = 0)
    (hfree : ScalarFree τ (binaryCopy S P)) {w : List (Bool × A)} (hne : w ≠ [])
    (hchain : w.IsChain (fun x y => x.1 ≠ y.1))
    (hmem : ∀ x ∈ w, x.2 ∈ powerPSet τ (s*U) P x.1) :
    τ ((w.map Prod.snd).prod) = 0 := by
  cases w with
  | nil => contradiction
  | cons a w =>
    obtain ⟨b,x⟩ := a
    cases b with
    | false =>
      obtain ⟨v,hvn,hvm,hvc,hvv⟩ := parse_power_word (s*U) hchain hmem
      rw [hvv]
      exact trace_twisted_signedWord hτ s U hs hU hHaar hfree hvn hvm hvc
    | true =>
      have hx : x ∈ P ∧ τ x = 0 := hmem (true,x) (by simp)
      cases w with
      | nil => simpa using hx.2
      | cons b w =>
        obtain ⟨b,y⟩ := b
        cases b with
        | true => simp at hchain
        | false =>
          have hct := (List.isChain_cons_cons.mp hchain).2
          have hmt : ∀ a ∈ (false,y)::w, a.2 ∈ powerPSet τ (s*U) P a.1 :=
            fun a ha => hmem a (List.mem_cons_of_mem _ ha)
          obtain ⟨v,hvn,hvm,hvc,hvv⟩ := parse_power_word (s*U) hct hmt
          have hz := trace_twisted_signedWord hτ s U hs hU hHaar hfree
            (signedMulLast_ne_nil x hvn) (signedMulLast_mem x hx.1 hvm)
            (signedMulLast_chain x hvc)
          rw [signedMulLast_value (s*U) x hvn] at hz
          simp only [List.map_cons,List.prod_cons]
          rw [show y * (w.map Prod.snd).prod = signedWord (s*U) v from hvv,
            hτ.2.1]
          exact hz

end

end KKFreeWords
end

end OAI
