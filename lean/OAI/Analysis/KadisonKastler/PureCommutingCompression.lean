import OAI.Analysis.KadisonKastler.PureStateExtension

namespace OAI

/-! # Compression to a pure cyclic representation

A pure vector-state restriction makes every commuting operator scalar
after compression to the cyclic subspace. This is the factorization step
for the initial product state on the two commuting factor algebras.
-/

namespace KadisonKastler

open NaimarkZFC
open scoped ComplexStarModule ComplexOrder

noncomputable section

variable {A : Type*} [CStarAlgebra A]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem irreducible_commutant_complex_scalar
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hπ : IsIrreducible π)
    (T : H →L[ℂ] H) (hT : ∀ a, Commute T (π a)) :
    ∃ z : ℂ, T=z • (1 : H →L[ℂ] H) := by
  have hstar (a : A) : Commute (star T) (π a) := by
    have h := (hT (star a)).star_star
    simpa only [map_star,star_star] using h
  have hre (a : A) : Commute (realPart T).val (π a) := by
    rw [realPart_apply_coe]
    exact ((hT a).add_left (hstar a)).smul_left _
  have him (a : A) : Commute (imaginaryPart T).val (π a) := by
    rw [imaginaryPart_apply_coe]
    exact (((hT a).sub_left (hstar a)).smul_left _).smul_left _
  obtain ⟨r,hr⟩ := irreducible_commutant_selfAdjoint_scalar π hπ _
    (realPart T).property hre
  obtain ⟨s,hs⟩ := irreducible_commutant_selfAdjoint_scalar π hπ _
    (imaginaryPart T).property him
  refine ⟨(r : ℂ)+Complex.I*(s : ℂ),?_⟩
  calc
    T = (realPart T).val+Complex.I • (imaginaryPart T).val :=
      (realPart_add_I_smul_imaginaryPart T).symm
    _ = r • (1 : H →L[ℂ] H)+Complex.I • (s • (1 : H →L[ℂ] H)) := by rw [hr,hs]
    _ = _ := by rw [← Complex.coe_smul,← Complex.coe_smul,smul_smul,← add_smul]

variable [PartialOrder A] [StarOrderedRing A]

theorem cyclicGNSMap_intertwines (f : A →ₚ[ℂ] ℂ)
    (π : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcoeff : ∀ a, f a=inner ℂ ξ (π a ξ)) (a : A) :
    (cyclicGNSMap f π ξ hcoeff).comp (f.gnsStarAlgHom a)=
      (π a).comp (cyclicGNSMap f π ξ hcoeff) := by
  apply DFunLike.coe_injective
  apply (gnsVector_cyclic f).equalizer (by fun_prop) (by fun_prop)
  funext b
  simp only [ContinuousLinearMap.comp_apply,Function.comp_apply,gns_apply_vector,
    gns_apply_coe,cyclicGNSMap_apply,map_mul,mul_apply_eq_comp]

theorem pureVector_commuting_factorization
    (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (hξ : ‖ξ‖=1)
    (hpure : IsPureState (NaimarkZFC.vectorFunctional π.toNonUnitalStarAlgHom ξ))
    (T : H →L[ℂ] H) (hT : ∀ a, Commute T (π a)) (a : A) :
    inner ℂ ξ (π a (T ξ))=inner ℂ ξ (π a ξ)*inner ℂ ξ (T ξ) := by
  let f := NaimarkZFC.vectorFunctional π.toNonUnitalStarAlgHom ξ
  have hf : IsState f := isState_vectorFunctional π.toNonUnitalStarAlgHom π.map_one ξ hξ
  let P := positiveOfSquares f hf.2
  have hcoeff (b : A) : P b=inner ℂ ξ (π.toNonUnitalStarAlgHom b ξ) := rfl
  let W := cyclicGNSMap P π.toNonUnitalStarAlgHom ξ hcoeff
  let g := gnsVector P
  have hWg : W g=ξ := by
    change cyclicGNSMap P π.toNonUnitalStarAlgHom ξ hcoeff (P.toPreGNS 1)=ξ
    rw [cyclicGNSMap_apply]
    change π 1 ξ=ξ
    have hone : π 1=1 := map_one π
    rw [hone]
    rfl
  have hg : ‖g‖=1 := gnsVector_norm_eq_one P ((isState_iff f).mp hf).1
  have hW (b : A) : W.comp (P.gnsStarAlgHom b)=(π b).comp W :=
    cyclicGNSMap_intertwines P π.toNonUnitalStarAlgHom ξ hcoeff b
  have hWs (b : A) : W.adjoint.comp (π b)=(P.gnsStarAlgHom b).comp W.adjoint := by
    have h := congrArg ContinuousLinearMap.adjoint (hW (star b))
    simpa only [ContinuousLinearMap.adjoint_comp,map_star,
      ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_adjoint] using h.symm
  let C := W.adjoint.comp (T.comp W)
  have hC (b : A) : Commute C (P.gnsStarAlgHom b) := by
    change C.comp (P.gnsStarAlgHom b)=(P.gnsStarAlgHom b).comp C
    ext x
    have hWx := congrArg (fun L : P.GNS →L[ℂ] H => L x) (hW b)
    have hTx := congrArg (fun L : H →L[ℂ] H => L (W x)) (hT b).eq
    have hWsx := congrArg (fun L : H →L[ℂ] P.GNS => L (T (W x))) (hWs b)
    change W.adjoint (T (W (P.gnsStarAlgHom b x)))=
      P.gnsStarAlgHom b (W.adjoint (T (W x)))
    change W (P.gnsStarAlgHom b x)=π b (W x) at hWx
    change T (π b (W x))=π b (T (W x)) at hTx
    change W.adjoint (π b (T (W x)))=P.gnsStarAlgHom b (W.adjoint (T (W x))) at hWsx
    rw [hWx,hTx,hWsx]
  obtain ⟨z,hz⟩ := irreducible_commutant_complex_scalar P.gnsNonUnitalStarAlgHom
    (pure_gns_irreducible f hf hpure) C hC
  have hzvalue : inner ℂ ξ (T ξ)=z := by
    calc
      inner ℂ ξ (T ξ) = inner ℂ g (C g) := by
        change inner ℂ ξ (T ξ)=inner ℂ g (W.adjoint (T (W g)))
        rw [ContinuousLinearMap.adjoint_inner_right,hWg]
      _ = inner ℂ g (z • g) := by rw [hz]; rfl
      _ = z := by rw [inner_smul_right,inner_self_eq_norm_sq_to_K,hg]; simp
  calc
    inner ℂ ξ (π a (T ξ)) = inner ℂ ξ (T (π a ξ)) :=
      congrArg (fun x => inner ℂ ξ x) (congrArg (fun L : H →L[ℂ] H => L ξ) (hT a).eq.symm)
    _ = inner ℂ g (C (P.gnsStarAlgHom a g)) := by
      change _=inner ℂ g (W.adjoint (T (W (P.gnsStarAlgHom a g))))
      rw [ContinuousLinearMap.adjoint_inner_right,hWg]
      have hWa := congrArg (fun L : P.GNS →L[ℂ] H => L g) (hW a)
      change W (P.gnsStarAlgHom a g)=π a (W g) at hWa
      rw [hWg] at hWa
      exact congrArg (fun x => inner ℂ ξ (T x)) hWa.symm
    _ = z*inner ℂ g (P.gnsStarAlgHom a g) := by rw [hz]; simp only [smul_apply,one_apply_eq_self,inner_smul_right]
    _ = inner ℂ ξ (π a ξ)*inner ℂ ξ (T ξ) := by
      rw [gnsVector_coefficient,hcoeff,hzvalue,mul_comm]
      rfl

end

end KadisonKastler

end OAI
