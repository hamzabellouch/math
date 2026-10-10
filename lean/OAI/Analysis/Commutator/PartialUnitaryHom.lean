import Mathlib
import OAI.Analysis.Commutator.PartialUnitaryCompletion
import OAI.Analysis.Commutator.PartialUnitaryWords

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FinitePatching

variable {A B J K : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]

namespace PartialUnitary

def map (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) : PartialUnitary B where
  val := φ v.val
  support := φ v.support
  projection := v.projection.map φ
  star_mul := by rw [←map_star,←map_mul,v.star_mul]
  mul_star := by rw [←map_star,←map_mul,v.mul_star]
  mul_support := by rw [←map_mul,v.mul_support]
  support_mul := by rw [←map_mul,v.support_mul]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_power (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) (k : ℤ) :
    φ (v.power k)=(v.map φ).power k := by
  cases k with
  | ofNat n => cases n <;> simp [power,map]
  | negSucc n => simp [power,map,map_star]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_ofUnitary (φ : A →⋆ₐ[ℂ] B) (u : unitary A) :
    (ofUnitary u).map φ=ofUnitary ⟨φ u,Unitary.map_mem φ u.property⟩ := by
  apply ext
  rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma ofUnitary_power_one (u : unitary A) : (ofUnitary u).power 1=(u:A) := by
  simp [power,ofUnitary]

omit [PartialOrder A] [StarOrderedRing A] in
lemma ofUnitary_power_neg_one (u : unitary A) : (ofUnitary u).power (-1)=star (u:A) := by
  change star (u:A)^1=star (u:A)
  simp

end PartialUnitary

namespace Words

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_slotPower (φ : A →⋆ₐ[ℂ] B) (k : K → ℤ) (v : PartialUnitary A) (s : Slot K) :
    φ (slotPower k v s)=slotPower k (v.map φ) s := by
  cases s with
  | none => exact map_one φ
  | some s =>
    cases s with
    | none => rfl
    | some i => exact v.map_power φ (k i)

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_letter (φ : A →⋆ₐ[ℂ] B) (x : J → A) (k : K → ℤ) (v : PartialUnitary A) (i : Letter J K) :
    φ (letter x k v i)=letter (φ ∘ x) k (v.map φ) i := by
  simp only [letter,map_mul,map_slotPower,Function.comp_apply]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B] in
lemma map_word (φ : A →⋆ₐ[ℂ] B) (x : J → A) (k : K → ℤ) (v : PartialUnitary A) (l : List (Letter J K)) :
    φ (word x k v l)=word (φ ∘ x) k (v.map φ) l := by
  induction l with
  | nil => exact map_one φ
  | cons i l ih => simp only [word_cons,map_mul,map_letter,ih]

end Words

end Kadison.FinitePatching

namespace Kadison.FinitePatching

variable {A B J K : Type*} [CStarAlgebra A] [CStarAlgebra B]

namespace PartialUnitary

lemma map_power_algebra (φ : A →⋆ₐ[ℂ] B) (v : PartialUnitary A) (k : ℤ) :
    φ (v.power k)=(v.map φ).power k := by
  cases k with
  | ofNat n => cases n <;> simp [power,map]
  | negSucc n => simp [power,map,map_star]

lemma map_ofUnitary_algebra (φ : A →⋆ₐ[ℂ] B) (u : unitary A) :
    (ofUnitary u).map φ=ofUnitary ⟨φ u,Unitary.map_mem φ u.property⟩ := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  apply ext
  rfl

end PartialUnitary

namespace Words

lemma map_word_algebra (φ : A →⋆ₐ[ℂ] B) (x : J → A) (k : K → ℤ) (v : PartialUnitary A)
    (l : List (Letter J K)) : φ (word x k v l)=word (φ ∘ x) k (v.map φ) l := by
  let : PartialOrder A := CStarAlgebra.spectralOrder A
  let : StarOrderedRing A := CStarAlgebra.spectralOrderedRing A
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  exact map_word φ x k v l

end Words

end Kadison.FinitePatching

end

end
end

end OAI
