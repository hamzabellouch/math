import Mathlib
import OAI.Analysis.Commutator.OrthogonalLinkSums

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder InnerProductSpace Topology BigOperators

open Filter

universe u

namespace Kadison.PartialIsometryOrder

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure PartialDecomposition (M : VonNeumannAlgebra H) (p : H →L[ℂ] H) where
  I : Type u
  v : I → Link M p 1
  nonzero : ∀ i,(v i).val≠0
  cross : ∀ i j,i≠j → star (v i).val*(v j).val=0
  strong : ∀ x : H,Tendsto (fun s : Finset I => (∑ i∈s,(v i).final) x) atTop (𝓝 x)

theorem exists_partialDecomposition (M : VonNeumannAlgebra H)
    (hM : FactorCorner.IsFactor M) {p : H →L[ℂ] H}
    (hpM : p∈M) (hp : IsStarProjection p) (hpn : p≠0) :
    Nonempty (PartialDecomposition M p) := by
  classical
  obtain ⟨S,hS⟩ := exists_maximal_orthogonalLinks M p 1
  let T : Set (Link M p 1) := {v | v∈S ∧ v.val≠0}
  have hTS : T⊆S := fun _ h => h.1
  have hT : OrthogonalLinks M p 1 T := fun _ hv _ hw hne => hS.1 (hTS hv) (hTS hw) hne
  have hspaces : familySpace M p 1 T=familySpace M p 1 S := by
    apply le_antisymm
    · apply Submodule.topologicalClosure_mono
      apply Submodule.span_mono
      rintro x ⟨v,hv,ξ,rfl⟩
      exact ⟨v,hTS hv,ξ,rfl⟩
    · apply Submodule.topologicalClosure_minimal
      · apply Submodule.span_le.mpr
        rintro x ⟨v,hv,ξ,rfl⟩
        change v.val ξ∈familySpace M p 1 T
        by_cases hz : v.val=0
        · rw [hz]
          exact (familySpace M p 1 T).zero_mem
        · exact familySpace_generator M p 1 T ⟨hv,hz⟩ ξ
      · exact Submodule.isClosed_topologicalClosure _
  have hspan : (familySpace M p 1 T).starProjection=1 := by
    have he : (familySpace M p 1 T).starProjection=(familySpace M p 1 S).starProjection := by
      congr 1
    rw [he]
    exact maximal_family_spans M p 1 hM hpM M.one_mem hp (IsStarProjection.one _) hpn S hS
  refine ⟨⟨T,fun i => i.val,fun i => i.property.2,?_,?_⟩⟩
  · intro i j hij
    exact family_cross M p 1 T hT hij
  · intro x
    simpa only [finiteProjection,one_apply_eq_self] using
      finiteProjection_tendsto M p 1 T hT (IsStarProjection.one _) hspan x

namespace PartialDecomposition

variable {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (D : PartialDecomposition M p)

def support (s : Finset D.I) : H →L[ℂ] H := ∑ i∈s,(D.v i).final

lemma support_projection (s : Finset D.I) : IsStarProjection (D.support s) := by
  classical
  constructor
  · change D.support s*D.support s=D.support s
    rw [support,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum,Finset.sum_eq_single_of_mem i hi]
    · exact (D.v i).final_projection.isIdempotentElem.eq
    · intro j hj hne
      change ((D.v i).val*star (D.v i).val)*((D.v j).val*star (D.v j).val)=0
      calc
        _=((D.v i).val*(star (D.v i).val*(D.v j).val))*star (D.v j).val := by noncomm_ring
        _=0 := by rw [D.cross i j hne.symm,mul_zero,zero_mul]
  · change star (D.support s)=D.support s
    rw [support,star_sum]
    exact Finset.sum_congr rfl (fun i _ => (D.v i).final_projection.isSelfAdjoint.star_eq)

lemma support_norm_le (s : Finset D.I) : ‖D.support s‖≤1 :=
  (D.support_projection s).norm_le _

lemma support_tendsto (x : H) : Tendsto (fun s : Finset D.I => D.support s x) atTop (𝓝 x) :=
  D.strong x

lemma eq_zero_of_coefficients_zero {a : H →L[ℂ] H}
    (ha : ∀ i j,star (D.v i).val*a*(D.v j).val=0) : a=0 := by
  have hleft (i : D.I) : star (D.v i).val*a=0 := by
    ext x
    have he (s : Finset D.I) : (star (D.v i).val*a) (D.support s x)=0 := by
      have ht : (star (D.v i).val*a)*D.support s=0 := by
        rw [support,Finset.mul_sum]
        apply Finset.sum_eq_zero
        intro j hj
        change (star (D.v i).val*a)*((D.v j).val*star (D.v j).val)=0
        rw [←mul_assoc,ha i j,zero_mul]
      exact congrArg (fun T : H →L[ℂ] H => T x) ht
    exact tendsto_nhds_unique
      (((star (D.v i).val*a).continuous.tendsto x).comp (D.support_tendsto x))
      (by simpa only [Function.comp_def,he,zero_apply] using
        (tendsto_const_nhds : Tendsto (fun _ : Finset D.I => (0:H)) atTop (𝓝 0)))
  ext x
  have he (s : Finset D.I) : D.support s (a x)=0 := by
    have ht : D.support s*a=0 := by
      rw [support,Finset.sum_mul]
      apply Finset.sum_eq_zero
      intro i hi
      change ((D.v i).val*star (D.v i).val)*a=0
      rw [mul_assoc,hleft i,mul_zero]
    exact congrArg (fun T : H →L[ℂ] H => T x) ht
  exact tendsto_nhds_unique (D.support_tendsto (a x))
    (by simpa only [Function.comp_def,he,zero_apply] using
      (tendsto_const_nhds : Tendsto (fun _ : Finset D.I => (0:H)) atTop (𝓝 0)))

lemma eq_of_coefficients_eq {a b : H →L[ℂ] H}
    (h : ∀ i j,star (D.v i).val*a*(D.v j).val=star (D.v i).val*b*(D.v j).val) : a=b := by
  apply sub_eq_zero.mp
  apply D.eq_zero_of_coefficients_zero
  intro i j
  rw [mul_sub,sub_mul,h i j,sub_self]

end PartialDecomposition

end Kadison.PartialIsometryOrder

end

end
end

end OAI
