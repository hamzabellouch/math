import Mathlib
import OAI.Analysis.Commutator.FreeWordTensor

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace TensorProduct CStarAlgebra

open UniformSpace

namespace Kadison.FreeWordAction

open FreeWordTensor FreeMoments

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (ht : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (f : D →⋆ₐ[ℂ] A) {ι : Type*} (S : ι → StarSubalgebra ℂ A) (i : ι)
  (hS : S i=f.range)

def innerFamily (u : unitary D) (k : ι) : A ≃⋆ₐ[ℂ] A := by
  classical
  exact if k=i then Unitary.conjStarAlgAut ℂ A (⟨f (u:D),Unitary.map_mem f u.property⟩)
    else StarAlgEquiv.refl ℂ A

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
@[simp] lemma innerFamily_self (u : unitary D) (a : A) :
    innerFamily f i u i a=f (u:D)*a*f (star (u:D)) := by
  simp [innerFamily,map_star]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
lemma innerFamily_other (u : unitary D) {k : ι} (hk : k≠i) (a : A) :
    innerFamily f i u k a=a := by simp [innerFamily,hk]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
include hS in
lemma innerFamily_mem (u : unitary D) (k : ι) (a : A) (ha : a∈S k) :
    innerFamily f i u k a∈S k := by
  by_cases hk : k=i
  · subst k
    rw [innerFamily_self]
    have hf (d : D) : f d∈S i := by rw [hS]; exact ⟨d,rfl⟩
    exact mul_mem (mul_mem (hf _) ha) (hf _)
  · simpa only [innerFamily_other f i u hk a] using ha

omit [PartialOrder D] [StarOrderedRing D] in
include ht in
lemma innerFamily_trace (u : unitary D) (k : ι) (a : A) :
    t.functional (innerFamily f i u k a)=t.functional a := by
  by_cases hk : k=i
  · subst k
    rw [innerFamily_self,ht,←mul_assoc,←map_mul,Unitary.star_mul_self_of_mem u.property,
      map_one,one_mul]
  · rw [innerFamily_other f i u hk a]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
lemma innerFamily_one (k : ι) (a : A) : innerFamily f i 1 k a=a := by
  by_cases hk : k=i
  · subst k; simp
  · exact innerFamily_other f i 1 hk a

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
lemma innerFamily_mul (u v : unitary D) (k : ι) (a : A) :
    innerFamily f i (u*v) k a=innerFamily f i u k (innerFamily f i v k a) := by
  by_cases hk : k=i
  · subst k
    rw [innerFamily_self,innerFamily_self,innerFamily_self]
    change f ((u:D)*(v:D))*a*f (star ((u:D)*(v:D))) =
      f (u:D)*(f (v:D)*a*f (star (v:D)))*f (star (u:D))
    rw [map_mul,star_mul,map_mul]
    simp only [mul_assoc]
  · simp only [innerFamily_other f i _ hk]

omit [PartialOrder A] [StarOrderedRing A] [PartialOrder D] [StarOrderedRing D] in
lemma innerFamily_continuous (k : ι) (a : A) :
    Continuous fun u : unitary D => innerFamily f i u k a := by
  by_cases hk : k=i
  · subst k
    simp only [innerFamily_self]
    exact (((map_continuous f).comp continuous_subtype_val).mul continuous_const).mul
      ((map_continuous f).comp continuous_subtype_val.star)
  · simpa only [innerFamily_other f i _ hk] using (continuous_const : Continuous fun _ : unitary D => a)

end Kadison.FreeWordAction

end

end
end

end OAI
