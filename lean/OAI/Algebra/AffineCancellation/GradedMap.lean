import OAI.Algebra.AffineCancellation.Model

namespace OAI

noncomputable section

namespace ComplexCancellation.GradedMap
open MvPolynomial
variable {k R S : Type*} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]
lemma mvpolynomial {ι : Type*} (G : ℤ → Submodule k R) [GradedAlgebra G]
    (w : ι → ℤ) (f : MvPolynomial ι k →ₐ[k] R)
    (hX : ∀ i, f (X i) ∈ G (w i)) {p : MvPolynomial ι k} {e : ℤ}
    (hp : IsWeightedHomogeneous w p e) : f p ∈ G e := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact (G e).zero_mem
  | add p q hp hq ihp ihq => rw [map_add]; exact add_mem ihp ihq
  | monomial d a hd =>
    rw [monomial_eq,map_mul,MvPolynomial.C_eq_algebraMap,AlgHom.commutes,← Algebra.smul_def]
    apply (G e).smul_mem
    rw [Finsupp.prod,map_prod]
    simp only [map_pow]
    have ht := SetLike.prod_pow_mem_graded G w (fun i => f (X i)) (F := d.support) (fun i => d i) (fun i _ => hX i)
    convert ht using 1
    rw [← hd,Finsupp.weight_apply,Finsupp.sum]

lemma projection (G : ℤ → Submodule k R) (H : ℤ → Submodule k S)
    [GradedAlgebra G] [GradedAlgebra H] (f : R →ₐ[k] S)
    (hf : ∀ e r, r ∈ G e → f r ∈ H e) (e : ℤ) (r : R) :
    f (GradedAlgebra.proj G e r)=GradedAlgebra.proj H e (f r) := by
  induction r using DirectSum.Decomposition.inductionOn G with
  | zero => simp only [map_zero]
  | @homogeneous i r =>
    by_cases hi : i=e
    · subst i
      rw [show GradedAlgebra.proj G e (r : R)=r from DirectSum.decompose_of_mem_same G r.2,
        show GradedAlgebra.proj H e (f r)=f r from DirectSum.decompose_of_mem_same H (hf e r r.2)]
    · rw [show GradedAlgebra.proj G e (r : R)=0 from DirectSum.decompose_of_mem_ne G r.2 hi,
        show GradedAlgebra.proj H e (f r)=0 from DirectSum.decompose_of_mem_ne H (hf i r r.2) hi,map_zero]
  | add r s hr hs => simp only [map_add,hr,hs]
lemma reflect (G : ℤ → Submodule k R) (H : ℤ → Submodule k S)
    [GradedAlgebra G] [GradedAlgebra H] (f : R →ₐ[k] S)
    (hf : Function.Injective f) (hm : ∀ e r, r ∈ G e → f r ∈ H e)
    {e : ℤ} {r : R} (hr : f r ∈ H e) : r ∈ G e := by
  have he : GradedAlgebra.proj G e r=r := by
    apply hf
    rw [projection G H f hm,show GradedAlgebra.proj H e (f r)=f r from DirectSum.decompose_of_mem_same H hr]
  rw [← he]
  exact (DirectSum.decompose G r e).property
end ComplexCancellation.GradedMap

end

end OAI
