import OAI.Analysis.Pureness.Quasitrace.ComplexQuasitraceBounds
import OAI.Analysis.Pureness.Quasitrace.ComplexQuasitracePullback
import Mathlib.Analysis.CStarAlgebra.Projection

namespace OAI
noncomputable section
namespace CuntzPureness
open scoped ComplexStarModule IsMulCommutative
variable {A : Type*} [CStarAlgebra A]

lemma ComplexQuasitrace.map_add_commuting_selfAdjoint (T : ComplexQuasitrace A)
    (a b : selfAdjoint A) (hab : Commute a.1 b.1) :
    T (a.1+b.1) = T a.1+T b.1 := by
  let S := StarAlgebra.adjoin ℂ {a.1,b.1}
  have hc : ∀ x ∈ ({a.1,b.1} : Set A), ∀ y ∈ ({a.1,b.1} : Set A), x*y=y*x := by
    intro x hx y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · rfl
    · exact hab.eq
    · exact hab.eq.symm
    · rfl
  let : IsMulCommutative S := StarAlgebra.isMulCommutative_adjoin ℂ (by
    intro element hmem
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with rfl | rfl
    · exact a.2.isStarNormal
    · exact b.2.isStarNormal)
    (fun left hleft right hright _ => hc left hleft right hright) (by
    intro x hx y hy _
    have hs : star y = y := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · exact a.2.star_eq
      · exact b.2.star_eq
    rw [hs]
    exact hc x hx y hy)
  let x : S := ⟨a.1, StarAlgebra.subset_adjoin ℂ _ (by simp)⟩
  let y : S := ⟨b.1, StarAlgebra.subset_adjoin ℂ _ (by simp)⟩
  have h := (T.subalgebraLinear S).map_add x y
  simp only [ComplexQuasitrace.subalgebraLinear_apply] at h
  exact h

def centralProjectionHom (p : A) (hp : IsStarProjection p) (hc : ∀ x, Commute p x) :
    A →⋆ₙₐ[ℂ] A where
  toFun x := p*x
  map_zero' := mul_zero p
  map_add' x y := mul_add p x y
  map_mul' x y := by
    symm
    calc
      (p*x)*(p*y) = p*((x*p)*y) := by simp only [mul_assoc]
      _ = p*((p*x)*y) := by rw [← (hc x).eq]
      _ = (p*p)*(x*y) := by simp only [mul_assoc]
      _ = p*(x*y) := by rw [hp.isIdempotentElem.eq]
  map_smul' c x := mul_smul_comm c p x
  map_star' x := by
    rw [star_mul, hp.isSelfAdjoint.star_eq, (hc (star x)).eq]

def ComplexQuasitrace.centralCompression (T : ComplexQuasitrace A)
    (p : A) (hp : IsStarProjection p) (hc : ∀ x, Commute p x) : ComplexQuasitrace A :=
  T.comap (centralProjectionHom p hp hc)

lemma ComplexQuasitrace.centralCompression_apply (T : ComplexQuasitrace A)
    (p : A) (hp : IsStarProjection p) (hc : ∀ x, Commute p x) (x : A) :
    T.centralCompression p hp hc x = T (p*x) := rfl

theorem ComplexQuasitrace.central_projection_split (T : ComplexQuasitrace A)
    (p : A) (hp : IsStarProjection p) (hc : ∀ x, Commute p x) (x : A) :
    T x = T (p*x)+T ((1-p)*x) := by
  have hq : ∀ a : A, Commute (1-p) a := fun a => (Commute.one_left a).sub_left (hc a)
  let φ := centralProjectionHom p hp hc
  let ψ := centralProjectionHom (1-p) hp.one_sub hq
  have hs (a : selfAdjoint A) : T a.1 = T (p*a.1)+T ((1-p)*a.1) := by
    have ha : IsSelfAdjoint (p*a.1) := a.2.map φ
    have hb : IsSelfAdjoint ((1-p)*a.1) := a.2.map ψ
    have hab : Commute (p*a.1) ((1-p)*a.1) :=
      ((hc (1-p)).mul_right (hc a.1)).mul_left
        ((hq a.1).symm.mul_right (Commute.refl a.1))
    have h := T.map_add_commuting_selfAdjoint ⟨p*a.1,ha⟩ ⟨(1-p)*a.1,hb⟩ hab
    have he : p*a.1+(1-p)*a.1=a.1 := by noncomm_ring
    change T (p*a.1+(1-p)*a.1) = _ at h
    rwa [he] at h
  have hx := T.real_add_I (ℜ x) (ℑ x)
  have hpv := (T.comap φ).real_add_I (ℜ x) (ℑ x)
  have hqv := (T.comap ψ).real_add_I (ℜ x) (ℑ x)
  rw [realPart_add_I_smul_imaginaryPart] at hx hpv hqv
  change T (p*x) = T (p*(ℜ x).1)+Complex.I*T (p*(ℑ x).1) at hpv
  change T ((1-p)*x) = T ((1-p)*(ℜ x).1)+Complex.I*T ((1-p)*(ℑ x).1) at hqv
  rw [hx, hpv, hqv, hs (ℜ x), hs (ℑ x)]
  ring
end CuntzPureness

end

end OAI
