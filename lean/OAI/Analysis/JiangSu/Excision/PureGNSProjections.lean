import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Excision.PureStateCarrier
import OAI.Analysis.JiangSu.CStarAlgebras.StateCoefficientApproximation

namespace OAI

section

noncomputable section
namespace PureStateExcision
open scoped ComplexOrder InnerProductSpace

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

 lemma projection_vector_value (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (P : H →L[ℂ] H) (hP : IsStarProjection P) (hcomm : ∀ a : A,Commute P (π a)) (a : A) :
    NuclearTrace.vectorFunctional π (P ξ) a=⟪ξ,π a (P ξ)⟫_ℂ := by
  have he : star P*π a*P=π a*P := by
    rw [hP.isSelfAdjoint.star_eq,hcomm a |>.eq, mul_assoc,hP.isIdempotentElem.eq]
  change ⟪P ξ,π a (P ξ)⟫_ℂ=_
  rw [←ContinuousLinearMap.adjoint_inner_right P ξ,←ContinuousLinearMap.star_eq_adjoint]
  exact congrArg (fun z : H →L[ℂ] H => ⟪ξ,z ξ⟫_ℂ) he

 lemma projection_vector_sum (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (P : H →L[ℂ] H) (hP : IsStarProjection P) (hcomm : ∀ a : A,Commute P (π a)) (a : A) :
    NuclearTrace.vectorFunctional π (P ξ) a+
      NuclearTrace.vectorFunctional π ((1-P) ξ) a=NuclearTrace.vectorFunctional π ξ a := by
  have hQ : IsStarProjection (1-P) := hP.one_sub
  have hcQ (a : A) : Commute (1-P) (π a) := (Commute.one_left _).sub_left (hcomm a)
  rw [projection_vector_value π ξ P hP hcomm a,projection_vector_value π ξ (1-P) hQ hcQ a]
  rw [←inner_add_right,←map_add]
  simp

 omit [PartialOrder A] [StarOrderedRing A] in
 lemma commuting_operator_eq_zero_of_cyclic (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (hcyc : DenseRange (fun a => π a ξ)) (P : H →L[ℂ] H)
    (hcomm : ∀ a : A,Commute P (π a)) (hξ : P ξ=0) : P=0 := by
  apply ContinuousLinearMap.ext
  have he : (fun x : H => P x)=(fun _ : H => (0 : H)) :=
    hcyc.equalizer P.continuous continuous_const (by
      funext a
      change P (π a ξ)=0
      have ha := congrArg (fun T : H →L[ℂ] H => T ξ) (hcomm a).eq
      change P (π a ξ)=π a (P ξ) at ha
      rw [ha,hξ,map_zero])
  intro x
  exact congrFun he x

 theorem pure_gns_commutant_projection (f : A →ₚ[ℂ] ℂ) (hf1 : f 1=1)
    (hpure : ofPositiveState f hf1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (P : f.GNS →L[ℂ] f.GNS) (hP : IsStarProjection P)
    (hcomm : ∀ a : A,Commute P (f.gnsStarAlgHom a)) : P=0 ∨ P=1 := by
  let ξ := Pureness.stateGNSVector f
  let π := f.gnsStarAlgHom
  let Q := (1-P : f.GNS →L[ℂ] f.GNS)
  have hQ : IsStarProjection Q := hP.one_sub
  have hcQ (a : A) : Commute Q (π a) := (Commute.one_left _).sub_left (hcomm a)
  let g := NuclearTrace.vectorFunctional π (P ξ)
  let h := NuclearTrace.vectorFunctional π (Q ξ)
  let t : ℝ := ‖P ξ‖^2
  have hg1 : g 1=(t : ℂ) := by
    change ⟪P ξ,π 1 (P ξ)⟫_ℂ=(t : ℂ)
    simp only [map_one,one_apply_eq_self,inner_self_eq_norm_sq_to_K,t,
      RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_pow]
  have hh1 : h 1=((‖Q ξ‖^2 : ℝ) : ℂ) := by
    change ⟪Q ξ,π 1 (Q ξ)⟫_ℂ=_
    simp only [map_one,one_apply_eq_self,inner_self_eq_norm_sq_to_K,
      RCLike.ofReal_eq_complex_ofReal,Complex.ofReal_pow]
  have hadd (a : A) : g a+h a=f a := by
    exact (projection_vector_sum π ξ P hP hcomm a).trans (Pureness.stateGNS_vector_value f a)
  have hnorm : t+‖Q ξ‖^2=1 := by
    have he := congrArg Complex.re (hadd 1)
    rw [hg1,hh1,hf1] at he
    exact_mod_cast he
  have ht0 : 0≤t := sq_nonneg _
  have ht1 : t≤1 := by nlinarith [sq_nonneg ‖Q ξ‖]
  by_cases hz : t=0
  · left
    apply commuting_operator_eq_zero_of_cyclic π ξ (NuclearNorm.stateGNS_cyclic f) P hcomm
    apply norm_eq_zero.mp
    exact (sq_eq_zero_iff.mp hz)
  by_cases ho : t=1
  · right
    have hzQ : Q ξ=0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (Q ξ)]
    have hzQ' := commuting_operator_eq_zero_of_cyclic π ξ (NuclearNorm.stateGNS_cyclic f) Q hcQ hzQ
    exact (sub_eq_zero.mp hzQ').symm
  have ht : 0<t := lt_of_le_of_ne ht0 (Ne.symm hz)
  have hlt : t<1 := lt_of_le_of_ne ht1 ho
  have he (a : A) : g a=(t : ℂ)*f a := by
    have hs := extreme_positive_summand (ofPositiveState f hf1) hpure g h ht hlt hg1
      (by rw [hh1]; exact_mod_cast (by linarith : ‖Q ξ‖^2=1-t)) (fun a => by
        rw [toPositiveState_ofPositiveState]
        exact hadd a) a
    rw [toPositiveState_ofPositiveState] at hs
    exact hs
  have hv : P ξ=(t : ℂ) • ξ := by
    apply ext_inner_left ℂ
    intro y
    refine (NuclearNorm.stateGNS_cyclic f).induction_on y ?_ ?_
    · exact isClosed_eq (by fun_prop) (by fun_prop)
    intro a
    have ha := he (star a)
    rw [projection_vector_value π ξ P hP hcomm] at ha
    change ⟪ξ,π (star a) (P ξ)⟫_ℂ=(t : ℂ)*f (star a) at ha
    rw [map_star,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at ha
    rw [inner_smul_right,ha]
    congr 1
    have hx := Pureness.stateGNS_vector_value f (star a)
    change ⟪ξ,π (star a) ξ⟫_ℂ=f (star a) at hx
    rw [map_star,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at hx
    exact hx.symm
  have hproj : P (P ξ)=P ξ := congrArg (fun T : f.GNS →L[ℂ] f.GNS => T ξ) hP.isIdempotentElem.eq
  have hs : (t*t : ℝ)=t := by
    have hi := congrArg (fun z : f.GNS => ⟪ξ,z⟫_ℂ) hproj
    rw [hv,map_smul,hv,inner_smul_right,inner_smul_right,
      inner_self_eq_norm_sq_to_K,Pureness.stateGNSVector_norm f hf1] at hi
    simpa using congrArg Complex.re hi
  have : t=1 := by nlinarith
  exact (ho this).elim

end PureStateExcision

end
end

section

noncomputable section
namespace PureStateExcision
open scoped ComplexOrder InnerProductSpace

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [PartialOrder A] [StarOrderedRing A] in
lemma invariant_starProjection_commute (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (U : Submodule ℂ H) [U.HasOrthogonalProjection]
    (hU : ∀ a : A,∀ x∈U,π a x∈U) (a : A) : Commute U.starProjection (π a) := by
  apply ContinuousLinearMap.ext
  intro x
  change U.starProjection (π a x)=π a (U.starProjection x)
  apply U.eq_starProjection_of_mem_of_inner_eq_zero (hU a _ (U.starProjection_apply_mem x))
  intro y hy
  rw [←map_sub]
  have he := U.starProjection_inner_eq_zero x (π (star a) y) (hU (star a) y hy)
  rw [map_star,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at he
  exact he

theorem pure_gns_invariant_subspace (f : A →ₚ[ℂ] ℂ) (hf1 : f 1=1)
    (hpure : ofPositiveState f hf1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (U : Submodule ℂ f.GNS) (hclosed : IsClosed (U : Set f.GNS))
    (hU : ∀ a : A,∀ x∈U,f.gnsStarAlgHom a x∈U) : U=⊥ ∨ U=⊤ := by
  let : CompleteSpace U := hclosed.completeSpace_coe
  obtain h0|h1 := pure_gns_commutant_projection f hf1 hpure U.starProjection
    isStarProjection_starProjection (invariant_starProjection_commute f.gnsStarAlgHom U hU)
  · left
    apply bot_unique
    intro x hx
    have he := U.starProjection_eq_self_iff.mpr hx
    rw [h0] at he
    exact he.symm
  · right
    apply top_unique
    intro x _
    have he := U.starProjection_apply_mem x
    simpa [h1] using he

 def orbitLinear (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) : A →ₗ[ℂ] H where
  toFun a := π a ξ
  map_add' a b := by simp
  map_smul' r a := by simp

lemma orbit_invariant (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H) (a : A) :
    (orbitLinear π ξ).range ∈ Module.End.invtSubmodule (π a).toLinearMap := by
  intro x hx
  obtain ⟨b,rfl⟩ := hx
  refine ⟨a*b,?_⟩
  simp [orbitLinear]

 theorem pure_gns_nonzero_cyclic (f : A →ₚ[ℂ] ℂ) (hf1 : f 1=1)
    (hpure : ofPositiveState f hf1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (ξ : f.GNS) (hξ : ξ≠0) : DenseRange (fun a => f.gnsStarAlgHom a ξ) := by
  let R := (orbitLinear f.gnsStarAlgHom ξ).range
  have hinv (a : A) : R.topologicalClosure ∈
      Module.End.invtSubmodule (f.gnsStarAlgHom a).toLinearMap :=
    Submodule.topologicalClosure_mem_invtSubmodule (orbit_invariant _ ξ a)
  have hmem : ξ∈R.topologicalClosure := R.le_topologicalClosure (by
    refine ⟨1,?_⟩
    simp [orbitLinear])
  have he : R.topologicalClosure=⊤ := by
    obtain hb|ht := pure_gns_invariant_subspace f hf1 hpure R.topologicalClosure
      R.isClosed_topologicalClosure hinv
    · rw [hb] at hmem
      exact (hξ hmem).elim
    · exact ht
  exact R.dense_iff_topologicalClosure_eq_top.mpr he

end PureStateExcision

end
end

end OAI
