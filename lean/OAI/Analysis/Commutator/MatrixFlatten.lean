import Mathlib
import OAI.Analysis.Commutator.MatrixTraceFaithful

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.MatrixGNS

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (ι κ : Type*) [Fintype ι] [Fintype κ]

local instance : DecidableEq ι := Classical.decEq ι

local instance : DecidableEq κ := Classical.decEq κ

local instance : DecidableEq (κ×ι) := Classical.decEq (κ×ι)

def flattenHom : CStarMatrix κ κ (CStarMatrix ι ι A) →⋆ₐ[ℂ] CStarMatrix (κ×ι) (κ×ι) A where
  toFun X := CStarMatrix.ofMatrix (fun p q => X p.1 q.1 p.2 q.2)
  map_zero' := rfl
  map_add' X Y := rfl
  map_mul' X Y := by
    ext p q
    change (X*Y) p.1 q.1 p.2 q.2=∑ r : κ×ι,X p.1 r.1 p.2 r.2*Y r.1 q.1 r.2 q.2
    rw [CStarMatrix.mul_apply]
    change (∑ j, (X p.1 j * Y j q.1 : CStarMatrix ι ι A)) p.2 q.2=_
    have heval (Z : κ → CStarMatrix ι ι A) :
        (∑ j,Z j) p.2 q.2=∑ j,Z j p.2 q.2 := by
      suffices ∀ s : Finset κ,(∑ j ∈ s,Z j) p.2 q.2=∑ j∈s,Z j p.2 q.2 from
        this Finset.univ
      intro s
      induction s using Finset.induction_on with
      | empty => rfl
      | @insert a s ha ih =>
        rw [Finset.sum_insert ha,Finset.sum_insert ha]
        change Z a p.2 q.2+(∑ j∈s,Z j) p.2 q.2=Z a p.2 q.2+_
        rw [ih]
    rw [heval]
    simp only [CStarMatrix.mul_apply,Fintype.sum_prod_type]
  map_one' := by
    ext p q
    change (1:CStarMatrix κ κ (CStarMatrix ι ι A)) p.1 q.1 p.2 q.2=
      (1:CStarMatrix (κ×ι) (κ×ι) A) p q
    by_cases hp : p.1=q.1 <;> by_cases hq : p.2=q.2 <;>
      simp [CStarMatrix.one_apply,hp,hq,Prod.ext_iff]
  commutes' z := by
    ext p q
    change (algebraMap ℂ (CStarMatrix κ κ (CStarMatrix ι ι A)) z) p.1 q.1 p.2 q.2=
      (algebraMap ℂ (CStarMatrix (κ×ι) (κ×ι) A) z) p q
    by_cases hp : p.1=q.1 <;> by_cases hq : p.2=q.2 <;>
      simp [CStarMatrix.algebraMap_apply,hp,hq,Prod.ext_iff]
  map_star' X := rfl

omit [PartialOrder A] [StarOrderedRing A] in
lemma flattenHom_bijective : Function.Bijective (flattenHom (A:=A) ι κ) := by
  constructor
  · intro X Y h
    ext i j k l
    exact congrArg (fun Z : CStarMatrix (κ×ι) (κ×ι) A => Z (i,k) (j,l)) h
  · intro X
    refine ⟨CStarMatrix.ofMatrix (fun i j => CStarMatrix.ofMatrix (fun k l => X (i,k) (j,l))),?_⟩
    rfl

def flatten : CStarMatrix κ κ (CStarMatrix ι ι A) ≃⋆ₐ[ℂ] CStarMatrix (κ×ι) (κ×ι) A :=
  StarAlgEquiv.ofBijective (flattenHom ι κ) (flattenHom_bijective ι κ)

omit [PartialOrder A] [StarOrderedRing A] in
@[simp] lemma flatten_apply (X : CStarMatrix κ κ (CStarMatrix ι ι A)) (p q : κ×ι) :
    flatten ι κ X p q=X p.1 q.1 p.2 q.2 := rfl

lemma trace_flatten (τ : A →ₚ[ℂ] ℂ) (X : CStarMatrix κ κ (CStarMatrix ι ι A)) :
    trace (ι:=κ×ι) τ (flatten ι κ X)=trace (ι:=κ) (trace (ι:=ι) τ) X := by
  simp only [trace_apply,flatten_apply,Fintype.sum_prod_type,Fintype.card_prod,
    Nat.cast_mul,mul_inv_rev]
  rw [←Finset.mul_sum]
  ring

def flatBalancedUnitary (X : CStarMatrix ι ι A) (hX : ‖X‖≤1) :
    _root_.unitary (CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A) :=
  ⟨flatten ι (Fin 2) (BalancedDilation.symmetry X),
    by
      rw [Unitary.mem_iff]
      have h := (Unitary.mem_iff.mp (BalancedDilation.symmetry_unitary X hX))
      constructor
      · rw [←map_star,←map_mul,h.1,map_one]
      · rw [←map_star,←map_mul,h.2,map_one]⟩

lemma flatBalancedUnitary_sq (X : CStarMatrix ι ι A) (hX : ‖X‖≤1) :
    (flatBalancedUnitary ι X hX:CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)*
      (flatBalancedUnitary ι X hX:CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)=1 := by
  change flatten ι (Fin 2) (BalancedDilation.symmetry X)*
    flatten ι (Fin 2) (BalancedDilation.symmetry X)=1
  rw [←map_mul,BalancedDilation.symmetry_mul_self X hX,map_one]

lemma flatBalancedUnitary_trace (τ : A →ₚ[ℂ] ℂ)
    (hτ : ∀ a b : A,τ (a*b)=τ (b*a)) (X : CStarMatrix ι ι A) (hX : ‖X‖≤1) :
    trace (ι:=(Fin 2)×ι) τ (flatBalancedUnitary ι X hX:
      CStarMatrix ((Fin 2)×ι) ((Fin 2)×ι) A)=0 := by
  change trace (ι:=(Fin 2)×ι) τ (flatten ι (Fin 2) (BalancedDilation.symmetry X))=0
  rw [trace_flatten]
  exact balanced_symmetry_trace_zero (trace (ι:=ι) τ) (trace_mul τ hτ) X hX

end Kadison.MatrixGNS

end

end
end

end OAI
