import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.CuntzSemigroup.CuntzRescaling
import OAI.Analysis.JiangSu.Excision.PureGNSProjections

namespace OAI

noncomputable section


namespace PureStateExcision

section
open scoped ComplexOrder InnerProductSpace

variable {A H : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma sqrt_apply_sqrt (operator : H →L[ℂ] H) (positive : 0 ≤ operator) (vector : H) :
    CFC.sqrt operator (CFC.sqrt operator vector) = operator vector :=
  congrArg (fun multiplier : H →L[ℂ] H => multiplier vector)
    (CFC.sqrt_mul_sqrt_self operator positive)

lemma sqrt_vector_value (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (T : H →L[ℂ] H) (hT : 0≤T) (hcomm : ∀ a : A,Commute T (π a)) (a : A) :
    NuclearTrace.vectorFunctional π (CFC.sqrt T ξ) a=⟪ξ,π a (T ξ)⟫_ℂ := by
  have hs (a : A) : Commute (CFC.sqrt T) (π a) := by
    rw [CFC.sqrt_eq_cfc]
    exact (hcomm a).cfc_nnreal _
  have he : star (CFC.sqrt T)*π a*CFC.sqrt T=π a*T := by
    rw [(CFC.sqrt_nonneg T).isSelfAdjoint.star_eq,(hs a).eq,mul_assoc,
      CFC.sqrt_mul_sqrt_self T hT]
  change ⟪CFC.sqrt T ξ,π a (CFC.sqrt T ξ)⟫_ℂ=_
  rw [←ContinuousLinearMap.adjoint_inner_right (CFC.sqrt T) ξ,
    ←ContinuousLinearMap.star_eq_adjoint]
  exact congrArg (fun z : H →L[ℂ] H => ⟪ξ,z ξ⟫_ℂ) he

lemma sqrt_vector_sum (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : H)
    (T : H →L[ℂ] H) (hT : 0≤T) (hT1 : T≤1)
    (hcomm : ∀ a : A,Commute T (π a)) (a : A) :
    NuclearTrace.vectorFunctional π (CFC.sqrt T ξ) a+
      NuclearTrace.vectorFunctional π (CFC.sqrt (1-T) ξ) a=
        NuclearTrace.vectorFunctional π ξ a := by
  have hcQ (a : A) : Commute (1-T) (π a) := (Commute.one_left _).sub_left (hcomm a)
  rw [sqrt_vector_value π ξ T hT hcomm a,
    sqrt_vector_value π ξ (1-T) (sub_nonneg.mpr hT1) hcQ a]
  rw [←inner_add_right,←map_add]
  simp

lemma vector_eq_of_cyclic_values (f : A →ₚ[ℂ] ℂ) (v : f.GNS) (t : ℂ)
    (h : ∀ a : A,⟪Pureness.stateGNSVector f,f.gnsStarAlgHom a v⟫_ℂ=t*f a) :
    v=t • Pureness.stateGNSVector f := by
  apply ext_inner_left ℂ
  intro y
  refine (NuclearNorm.stateGNS_cyclic f).induction_on y ?_ ?_
  · exact isClosed_eq (by fun_prop) (by fun_prop)
  intro a
  have ha := h (star a)
  rw [map_star,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at ha
  rw [inner_smul_right,ha]
  congr 1
  have hx := Pureness.stateGNS_vector_value f (star a)
  rw [map_star,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right] at hx
  exact hx.symm

theorem pure_gns_positive_commutant (f : A →ₚ[ℂ] ℂ) (hf1 : f 1=1)
    (hpure : ofPositiveState f hf1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (T : f.GNS →L[ℂ] f.GNS) (hT : 0≤T) (hT1 : T≤1)
    (hcomm : ∀ a : A,Commute T (f.gnsStarAlgHom a)) :
    ∃ t : ℝ,0≤t ∧ t≤1 ∧ T=(t : ℂ) • 1 := by
  let : CStarAlgebra (f.GNS →L[ℂ] f.GNS) := inferInstance
  let ξ := Pureness.stateGNSVector f
  let π := f.gnsStarAlgHom
  let S : f.GNS →L[ℂ] f.GNS := CFC.sqrt T
  let R : f.GNS →L[ℂ] f.GNS := CFC.sqrt (1-T)
  let g := NuclearTrace.vectorFunctional π (S ξ)
  let h := NuclearTrace.vectorFunctional π (R ξ)
  let t : ℝ := ‖S ξ‖^2
  have hg1 : g 1=(t : ℂ) := by
    change ⟪S ξ,π 1 (S ξ)⟫_ℂ=(t : ℂ)
    rw [map_one,one_apply_eq_self,inner_self_eq_norm_sq_to_K]
    simp [t]
  have hh1 : h 1=((‖R ξ‖^2 : ℝ) : ℂ) := by
    change ⟪R ξ,π 1 (R ξ)⟫_ℂ=_
    rw [map_one,one_apply_eq_self,inner_self_eq_norm_sq_to_K]
    simp
  have hadd (a : A) : g a+h a=f a := by
    exact (sqrt_vector_sum π ξ T hT hT1 hcomm a).trans (Pureness.stateGNS_vector_value f a)
  have hnorm : t+‖R ξ‖^2=1 := by
    have he := congrArg Complex.re (hadd 1)
    rw [hg1,hh1,hf1] at he
    exact_mod_cast he
  have ht0 : 0≤t := sq_nonneg _
  have ht1 : t≤1 :=
    (le_add_of_nonneg_right (sq_nonneg ‖R ξ‖)).trans_eq hnorm
  have hv : T ξ=(t : ℂ) • ξ := by
    by_cases hz : t=0
    · have hs : S ξ=0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hz)
      have he : T ξ=S (S ξ) := (sqrt_apply_sqrt T hT ξ).symm
      rw [he,hs,map_zero,hz,Complex.ofReal_zero,zero_smul]
    by_cases ho : t=1
    · have hs : R ξ=0 := by
        apply norm_eq_zero.mp
        nlinarith [norm_nonneg (R ξ)]
      have he : (1-T) ξ=0 := by
        have he : (1-T) ξ=R (R ξ) :=
          (sqrt_apply_sqrt (1-T) (sub_nonneg.mpr hT1) ξ).symm
        rw [he,hs,map_zero]
      rw [ho,Complex.ofReal_one,one_smul]
      change ξ-T ξ=0 at he
      exact (sub_eq_zero.mp he).symm
    apply vector_eq_of_cyclic_values f (T ξ) (t : ℂ)
    intro a
    rw [←sqrt_vector_value π ξ T hT hcomm a]
    have he := extreme_positive_summand (ofPositiveState f hf1) hpure g h
      (lt_of_le_of_ne ht0 (Ne.symm hz)) (lt_of_le_of_ne ht1 ho) hg1
      (by rw [hh1]; exact_mod_cast (by linarith : ‖R ξ‖^2=1-t))
      (fun a => by rw [toPositiveState_ofPositiveState]; exact hadd a) a
    rw [toPositiveState_ofPositiveState] at he
    exact he
  refine ⟨t,ht0,ht1,?_⟩
  have he := commuting_operator_eq_zero_of_cyclic π ξ (NuclearNorm.stateGNS_cyclic f)
    (T-(t : ℂ) • 1) (fun a => (hcomm a).sub_left ((Commute.one_left _).smul_left _))
    (by change T ξ-(t : ℂ) • ξ=0; rw [hv,sub_self])
  exact sub_eq_zero.mp he

end
open scoped ComplexOrder InnerProductSpace ComplexStarModule

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma selfadjoint_affine_effect {B : Type*} [CStarAlgebra B] [PartialOrder B] [StarOrderedRing B]
    (T : B) (hT : IsSelfAdjoint T) :
    let c : ℝ := ‖T‖+1
    let V : B := (2*c)⁻¹ • (T+c • 1)
    0≤V ∧ V≤1 := by
  let c : ℝ := ‖T‖+1
  have hc : 0<c := by dsimp [c]; positivity
  have hlow : -(c • (1 : B))≤T := by
    apply le_trans _ hT.neg_algebraMap_norm_le_self
    rw [neg_le_neg_iff,Algebra.algebraMap_eq_smul_one]
    exact smul_le_smul_of_nonneg_right (by dsimp [c]; linarith) zero_le_one
  have hhigh : T≤c • (1 : B) := by
    apply hT.le_algebraMap_norm_self.trans
    rw [Algebra.algebraMap_eq_smul_one]
    exact smul_le_smul_of_nonneg_right (by dsimp [c]; linarith) zero_le_one
  let V : B := (2*c)⁻¹ • (T+c • 1)
  have hV0 : 0≤V := smul_nonneg (inv_nonneg.mpr (by positivity)) (neg_le_iff_add_nonneg.mp hlow)
  have he : (2*c)⁻¹ • ((2*c) • (1 : B))=1 := by
    rw [smul_smul,inv_mul_cancel₀ (by positivity : 2*c≠0),one_smul]
  have hV1 : V≤1 := by
    rw [←he]
    apply smul_le_smul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
    calc T+c • (1 : B)≤c • 1+c • 1 := add_le_add hhigh le_rfl
      _=(2*c) • 1 := by rw [←add_smul]; congr 1; ring
  exact ⟨hV0,hV1⟩

lemma pure_gns_selfadjoint_commutant (f : A →ₚ[ℂ] ℂ) (hf1 : f 1=1)
    (hpure : ofPositiveState f hf1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (T : f.GNS →L[ℂ] f.GNS) (hT : IsSelfAdjoint T)
    (hcomm : ∀ a : A,Commute T (f.gnsStarAlgHom a)) :
    ∃ t : ℝ,T=(t : ℂ) • 1 := by
  let : CStarAlgebra (f.GNS →L[ℂ] f.GNS) := inferInstance
  let : Algebra ℝ (f.GNS →L[ℂ] f.GNS) := ContinuousLinearMap.algebra
  let c : ℝ := ‖T‖+1
  have hc : 0<c := by dsimp [c]; positivity
  let V : f.GNS →L[ℂ] f.GNS := (2*c)⁻¹ • (T+c • 1)
  obtain ⟨hV0,hV1⟩ := selfadjoint_affine_effect T hT
  have hVc (a : A) : Commute V (f.gnsStarAlgHom a) :=
    ((hcomm a).add_left ((Commute.one_left _).smul_left c)).smul_left ((2*c)⁻¹)
  obtain ⟨t,_,_,ht⟩ := pure_gns_positive_commutant f hf1 hpure V hV0 hV1 hVc
  refine ⟨2*c*t-c,?_⟩
  have hs := congrArg (fun S : f.GNS →L[ℂ] f.GNS => (2*c) • S) ht
  simp only [V,smul_smul,mul_inv_cancel₀ (show 2*c≠0 by positivity),one_smul,
    Complex.coe_smul] at hs
  rw [←eq_sub_iff_add_eq] at hs
  rw [hs,Complex.coe_smul,sub_smul]

theorem pure_gns_scalar_commutant (f : A →ₚ[ℂ] ℂ) (hf1 : f 1=1)
    (hpure : ofPositiveState f hf1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (T : f.GNS →L[ℂ] f.GNS)
    (hcomm : ∀ a : A,Commute T (f.gnsStarAlgHom a)) :
    ∃ z : ℂ,T=z • 1 := by
  let : CStarAlgebra (f.GNS →L[ℂ] f.GNS) := inferInstance
  let : Algebra ℝ (f.GNS →L[ℂ] f.GNS) := ContinuousLinearMap.algebra
  have hcstar (a : A) : Commute (star T) (f.gnsStarAlgHom a) := by
    have h := (hcomm (star a)).star_star
    simpa only [map_star,star_star] using h
  have hcR (a : A) : Commute (ℜ T : f.GNS →L[ℂ] f.GNS) (f.gnsStarAlgHom a) := by
    rw [realPart_apply_coe]
    exact ((hcomm a).add_left (hcstar a)).smul_left _
  have hcI (a : A) : Commute (ℑ T : f.GNS →L[ℂ] f.GNS) (f.gnsStarAlgHom a) := by
    rw [imaginaryPart_apply_coe]
    exact (((hcomm a).sub_left (hcstar a)).smul_left _).smul_left _
  obtain ⟨r,hr⟩ := pure_gns_selfadjoint_commutant f hf1 hpure (ℜ T) (ℜ T).property hcR
  obtain ⟨s,hs⟩ := pure_gns_selfadjoint_commutant f hf1 hpure (ℑ T) (ℑ T).property hcI
  refine ⟨(r : ℂ)+Complex.I*(s : ℂ),?_⟩
  rw [←realPart_add_I_smul_imaginaryPart T,hr,hs,smul_smul,add_smul]

end PureStateExcision

end

end OAI
