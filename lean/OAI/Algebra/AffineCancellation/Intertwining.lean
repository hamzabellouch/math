import OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

namespace ComplexCancellation.DerivationIntertwining
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
def subalgebra (f : R →ₐ[k] S) (D : Derivation k R R) (E : Derivation k S S) : Subalgebra k R where
  carrier := {r | E (f r)=f (D r)}
  algebraMap_mem' a := by
    change E (f (algebraMap k R a))=f (D (algebraMap k R a))
    rw [f.commutes,E.map_algebraMap,D.map_algebraMap,map_zero]
  add_mem' := by
    intro r s hr hs
    change E (f r)=f (D r) at hr
    change E (f s)=f (D s) at hs
    change E (f (r+s))=f (D (r+s))
    rw [map_add,map_add,hr,hs,map_add,map_add]
  mul_mem' := by
    intro r s hr hs
    change E (f r)=f (D r) at hr
    change E (f s)=f (D s) at hs
    change E (f (r*s))=f (D (r*s))
    rw [map_mul,Derivation.leibniz,Derivation.leibniz,hr,hs,smul_eq_mul,smul_eq_mul,smul_eq_mul,smul_eq_mul,map_add,map_mul,map_mul]
lemma mvPolynomial (f : R →ₐ[k] S) (D : Derivation k R R) (E : Derivation k S S)
    {ι : Type*} (q : MvPolynomial ι k →ₐ[k] R) (p : MvPolynomial ι k)
    (hX : ∀ i, E (f (q (MvPolynomial.X i)))=f (D (q (MvPolynomial.X i)))) : E (f (q p))=f (D (q p)) := by
  change q p ∈ subalgebra f D E
  induction p using MvPolynomial.induction_on with
  | C c => rw [MvPolynomial.C_eq_algebraMap,q.commutes]; exact (subalgebra f D E).algebraMap_mem c
  | add r s hr hs => rw [map_add]; exact add_mem hr hs
  | mul_X r i hr => rw [map_mul]; exact mul_mem hr (hX i)
end ComplexCancellation.DerivationIntertwining

end

end OAI
