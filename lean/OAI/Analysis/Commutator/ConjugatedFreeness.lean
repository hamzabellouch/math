import Mathlib
import OAI.Analysis.Commutator.ConjugatedWordAlgebra
import OAI.Analysis.Commutator.FreeMoments

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching.ConjugatedWords

open Words

variable {A B : Type} [CStarAlgebra A] [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

variable (φ : A →⋆ₐ[ℂ] B) (u : unitary B)

def pair (c : Bool) : StarSubalgebra ℂ B :=
  if c then φ.range else ((Unitary.conjStarAlgAut ℂ B u).toStarAlgHom.comp φ).range

variable (S : StarSubalgebra ℂ B) (ρ : B →ₗ[ℂ] ℂ)

omit [PartialOrder B] [StarOrderedRing B] in
lemma trace_unitary_conjugation (hρ : ∀ a∈S,∀ b∈S,ρ (a*b)=ρ (b*a))
    (v : unitary B) (hv : (v:B)∈S) (a : B) (ha : a∈S) :
    ρ ((v:B)*a*star (v:B))=ρ a := by
  calc
    _ = ρ ((a*star (v:B))*(v:B)) := by
      rw [mul_assoc]
      exact hρ _ hv _ (S.mul_mem ha (S.star_mem' hv))
    _ = ρ a := by rw [mul_assoc,v.property.1,mul_one]

omit [PartialOrder B] [StarOrderedRing B] in
include S in
theorem free_of_centered_unitary_words (τ : A →ₗ[ℂ] ℂ)
    (hu : (u:B)∈S) (hφ : ∀ a,φ a∈S)
    (hρ : ∀ a∈S,∀ b∈S,ρ (a*b)=ρ (b*a))
    (htrace : ∀ a,ρ (φ a)=τ a)
    (hword : ∀ (J : Type) (x : J → A),(∀ j,τ (x j)=0) →
      ∀ l : List (Letter J Bool),l≠[] → Valid l →
        ρ (word (φ ∘ x) signPower (PartialUnitary.ofUnitary u) l)=0) :
    FreeMoments.Free (pair φ u) ρ := by
  classical
  let J := FreeMoments.Letter (pair φ u) ρ
  have hpre (a : J) : ∃ x : A,τ x=0 ∧
      a.val=if a.color then φ x else (u:B)*φ x*star (u:B) := by
    cases hc : a.color with
    | false =>
      obtain ⟨x,hx⟩ := (show a.val∈((Unitary.conjStarAlgAut ℂ B u).toStarAlgHom.comp φ).range from by
        simpa only [pair,hc,Bool.false_eq_true,ite_false] using a.mem)
      have he : (u:B)*φ x*star (u:B)=a.val := hx
      refine ⟨x,?_,by simpa only [hc,Bool.false_eq_true,ite_false] using he.symm⟩
      rw [←htrace,←trace_unitary_conjugation S ρ hρ u hu (φ x) (hφ x),he]
      exact a.centered
    | true =>
      obtain ⟨x,hx⟩ := (show a.val∈φ.range from by simpa only [pair,hc,ite_true] using a.mem)
      change φ x=a.val at hx
      refine ⟨x,?_,by simpa only [hc,ite_true] using hx.symm⟩
      rw [←htrace,hx]
      exact a.centered
  choose x hxc hx using hpre
  have hval (a : J) : (leftUnitary u a.color:B)*φ (x a)*star (leftUnitary u a.color:B)=a.val := by
    cases hc : a.color <;> simpa [leftUnitary,hc] using (hx a).symm
  have hmem (a : J) : a.val∈S := by
    rw [←hval a]
    have hleft : (leftUnitary u a.color:B)∈S := by
      cases a.color <;> simp only [leftUnitary] <;> first | exact hu | exact S.one_mem
    exact S.mul_mem (S.mul_mem hleft (hφ _)) (S.star_mem' hleft)
  intro w hw hne
  have hwmem : FreeMoments.word w∈S := by
    clear hw hne
    induction w with
    | nil => exact S.one_mem
    | cons a l ih => exact S.mul_mem (hmem a) ih
  cases w with
  | nil => exact (hne rfl).elim
  | cons a l =>
    let σ := a.color
    let c : J → Bool := FreeMoments.Letter.color
    have hv := encode_valid c σ (show (a::l).IsChain (fun a b : J => c a≠c b) from hw)
    have hz := hword J x hxc (encode c σ (a::l)) (encode_ne_nil c σ (by simp)) hv
    rw [word_encode] at hz
    have he : ((a::l).map (fun a => (leftUnitary u (c a):B)*(φ ∘ x) a*star (leftUnitary u (c a):B))).prod=
        FreeMoments.word (a::l) := by
      apply congrArg List.prod
      apply List.map_congr_left
      intro j _
      exact hval j
    rw [he] at hz
    change ρ (star (leftUnitary u σ:B)*FreeMoments.word (a::l)*(leftUnitary u σ:B))=0 at hz
    have hleft : (star (leftUnitary u σ):B)∈S := by
      apply S.star_mem'
      cases σ <;> simp only [leftUnitary] <;> first | exact hu | exact S.one_mem
    have ht := trace_unitary_conjugation S ρ hρ (star (leftUnitary u σ)) hleft _ hwmem
    simp only [Unitary.coe_star,star_star] at ht
    exact ht.symm.trans hz

end Kadison.FinitePatching.ConjugatedWords

end

end
end

end OAI
