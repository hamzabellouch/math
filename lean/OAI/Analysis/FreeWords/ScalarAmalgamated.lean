import Mathlib
import OAI.Analysis.FreeWords.ScalarAmalgamatedDefinitions

namespace OAI

noncomputable section

namespace KKAmalgamatedTransport

noncomputable section

variable {A : Type*} [Ring A]

@[simp] theorem pairProd_nil : pairProd ([] : List (A×A))=1 := rfl

@[simp] theorem pairProd_cons (z : A×A) (w : List (A×A)) :
    pairProd (z::w)=z.1*z.2*pairProd w := rfl

@[simp] theorem pairProd_append (w v : List (A×A)) :
    pairProd (w++v)=pairProd w*pairProd v := by
  simp [pairProd,List.map_append,List.prod_append]

def Blocks (S T : Set A) : Set A :=
  {a | ∃ w : List (A×A), ∃ c : A,
    (∀ z∈w, z.1∈S ∧ z.2∈T) ∧ c∈S ∧ a=pairProd w*c}

theorem block_single {S T : Set A} {a : A} (ha : a∈S) : a∈Blocks S T := by
  exact ⟨[],a,by simp,ha,by simp⟩

theorem block_join {S T : Set A} {a b c : A}
    (ha : a∈Blocks S T) (hb : b∈T) (hc : c∈Blocks S T) :
    a*b*c∈Blocks S T := by
  obtain ⟨w,d,hw,hd,rfl⟩ := ha
  obtain ⟨v,e,hv,he,rfl⟩ := hc
  refine ⟨w++[(d,b)]++v,e,?_,he,?_⟩
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · rcases List.mem_append.mp hz with hz | hz
      · exact hw z hz
      · have hz' : z=(d,b) := List.mem_singleton.mp hz
        subst z
        exact ⟨hd,hb⟩
    · exact hv z hz
  · simp [mul_assoc]

variable [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

theorem block_mem {S T : Set A} (Q : StarSubalgebra ℂ A)
    (hS : S⊆Q) (hT : T⊆Q) {a : A} (ha : a∈Blocks S T) : a∈Q := by
  obtain ⟨w,c,hw,hc,rfl⟩ := ha
  apply Q.mul_mem _ (hS hc)
  induction w with
  | nil => exact Q.one_mem
  | cons z w ih =>
    have hz := hw z List.mem_cons_self
    apply Q.mul_mem (Q.mul_mem (hS hz.1) (hT hz.2))
    exact ih (fun a ha => hw a (List.mem_cons_of_mem _ ha))

theorem block_expectation_zero
    (τ : A →ₗ[ℂ] ℂ) (E : A →ₗ[ℂ] A) (B C : StarSubalgebra ℂ A)
    (hτ1 : τ 1=1) (hErange : ∀ a, E a∈B)
    (hEright : ∀ a b, b∈B → E (a*b)=E a*b)
    (hτE : ∀ a, τ (E a)=τ a)
    (hfaith : ∀ b∈B, τ (b*star b)=0 → b=0)
    (hfree : AlternatingMoments τ (Centered τ C) (Centered τ B))
    {a : A} (ha : a∈Blocks (Centered τ C) (Centered τ B)) : E a=0 := by
  obtain ⟨w,c,hw,hc,rfl⟩ := ha
  let a := pairProd w*c
  have hzero : τ a=0 := (hfree w hw).2 c hc
  have htest (b : A) (hb : b∈B) : τ (a*b)=0 := by
    let b₀ := b-(τ b) • (1:A)
    have hb₀ : b₀∈Centered τ B := by
      refine ⟨B.sub_mem hb (B.smul_mem B.one_mem _),?_⟩
      simp [b₀,map_sub,map_smul,hτ1]
    have hw' : ∀ z∈w++[(c,b₀)], z.1∈Centered τ C ∧ z.2∈Centered τ B := by
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact hw z hz
      · have hz' := List.mem_singleton.mp hz
        subst z
        exact ⟨hc,hb₀⟩
    have hh := (hfree (w++[(c,b₀)]) hw').1 (by simp)
    have hh' : τ (a*b₀)=0 := by simpa [a,mul_assoc] using hh
    simpa [b₀,mul_sub,mul_smul_comm,map_sub,map_smul,hzero] using hh'
  apply hfaith _ (hErange _)
  rw [← hEright _ _ (star_mem (hErange _)),hτE]
  exact htest _ (star_mem (hErange _))

theorem scalar_amalgamated_cyclic_transport : ScalarAmalgamatedCyclicTransport (A := A) := by
  intro τ E B C P Q hτ1 hBP hBQ hCQ hErange hEfix hEright hτE hfaith hscalar hrelative
  let S := Blocks (Centered τ C) (Centered τ B)
  have hSQ : S⊆RelativeCentered E Q := by
    intro a ha
    exact ⟨block_mem Q (fun _ h => hCQ h.1) (fun _ h => hBQ h.1) ha,
      block_expectation_zero τ E B C hτ1 hErange hEright hτE hfaith hscalar ha⟩
  have hdecomp (x : A) (hx : x∈Centered τ P) :
      (x-E x)∈RelativeCentered E P ∧ E x∈Centered τ B := by
    refine ⟨⟨P.sub_mem hx.1 (hBP (hErange x)),?_⟩,hErange x,?_⟩
    · rw [map_sub,hEfix _ (hErange x),sub_self]
    · rw [hτE,hx.2]
  have haux : ∀ w : List (A×A),
      (∀ z∈w, z.1∈Centered τ C ∧ z.2∈Centered τ P) →
      ∀ p : List (A×A),
      (∀ z∈p, z.1∈RelativeCentered E Q ∧ z.2∈RelativeCentered E P) →
      ∀ c∈S, ∀ x∈Centered τ P,
        E (pairProd p*c*x*pairProd w)=0 := by
    intro w
    induction w with
    | nil =>
      intro _ p hp c hc x hx
      obtain ⟨hx₀,hxB⟩ := hdecomp x hx
      have hp' : ∀ z∈p++[(c,x-E x)],
          z.1∈RelativeCentered E Q ∧ z.2∈RelativeCentered E P := by
        intro z hz
        rcases List.mem_append.mp hz with hz | hz
        · exact hp z hz
        · have hz' := List.mem_singleton.mp hz
          subst z
          exact ⟨hSQ hc,hx₀⟩
      have h₀ := (hrelative (p++[(c,x-E x)]) hp').1 (by simp)
      have hB : E (pairProd p*c*E x)=0 := by
        rw [hEright _ _ (hErange x),(hrelative p hp).2 c (hSQ hc),zero_mul]
      have he : pairProd p*c*x*pairProd [] =
          pairProd (p++[(c,x-E x)])+pairProd p*c*E x := by
        simp only [pairProd_nil,pairProd_append,pairProd_cons,mul_one]
        noncomm_ring
      rw [he,map_add,h₀,hB,add_zero]
    | cons z w ih =>
      intro hw p hp c hc x hx
      have hz := hw z List.mem_cons_self
      have hw' := fun a ha => hw a (List.mem_cons_of_mem _ ha)
      obtain ⟨hx₀,hxB⟩ := hdecomp x hx
      have hp' : ∀ a∈p++[(c,x-E x)],
          a.1∈RelativeCentered E Q ∧ a.2∈RelativeCentered E P := by
        intro a ha
        rcases List.mem_append.mp ha with ha | ha
        · exact hp a ha
        · have ha' := List.mem_singleton.mp ha
          subst a
          exact ⟨hSQ hc,hx₀⟩
      have hzc : z.1∈S := block_single hz.1
      have hnew : c*E x*z.1∈S := block_join hc hxB hzc
      have h₀ := ih hw' (p++[(c,x-E x)]) hp' z.1 hzc z.2 hz.2
      have hB := ih hw' p hp (c*E x*z.1) hnew z.2 hz.2
      have he : pairProd p*c*x*pairProd (z::w) =
          pairProd (p++[(c,x-E x)])*z.1*z.2*pairProd w+
          pairProd p*(c*E x*z.1)*z.2*pairProd w := by
        simp only [pairProd_append,pairProd_cons,pairProd_nil,mul_one]
        noncomm_ring
      rw [he,map_add,h₀,hB,add_zero]
  intro w hne hw
  cases w with
  | nil => exact (hne rfl).elim
  | cons z w =>
    have hz := hw z List.mem_cons_self
    have hh := haux w (fun a ha => hw a (List.mem_cons_of_mem _ ha)) [] (by simp)
      z.1 (block_single hz.1) z.2 hz.2
    have he : E (pairProd (z::w))=0 := by simpa only [pairProd_cons,pairProd_nil,one_mul] using hh
    rw [← hτE,he,map_zero]

end

end KKAmalgamatedTransport
end

end OAI
