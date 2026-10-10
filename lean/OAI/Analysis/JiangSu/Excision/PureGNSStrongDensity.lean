import Mathlib
import OAI.Analysis.TracialSplitting.PreparedBlocks
import OAI.Analysis.JiangSu.Nonunital.Regularization
import OAI.Analysis.JiangSu.TensorProducts.FiniteHilbertAmplification
import OAI.Analysis.JiangSu.Excision.PureGNSCommutant

namespace OAI

section

noncomputable section
namespace PureStateExcision
open scoped ComplexOrder InnerProductSpace ENNReal

variable {A H I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype I] [DecidableEq I]

omit [CompleteSpace H] in
lemma scalar_entries_commute
    (P : PiLp 2 (fun _ : I => H) →L[ℂ] PiLp 2 (fun _ : I => H))
    (hP : ∀ i j,∃ z : ℂ,tupleEntry P i j=z • 1) (T : H →L[ℂ] H) :
    Commute P (tupleOp T) := by
  choose z hz using hP
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  change P (tupleOp T x) i=T (P x i)
  rw [tuple_operator_expansion,tuple_operator_expansion P x i,map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [hz i j]
  simp

lemma strong_density_of_scalar_commutant (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hscalar : ∀ T : H →L[ℂ] H,(∀ a,Commute T (π a)) → ∃ z : ℂ,T=z • 1)
    (ξ : PiLp 2 (fun _ : I => H)) (T : H →L[ℂ] H) :
    tupleOp T ξ∈closure (Set.range (fun a => tupleRepresentation π a ξ)) := by
  let ρ := tupleRepresentation (I := I) π
  let R := (orbitLinear ρ ξ).range
  let U := R.topologicalClosure
  have hinv (a : A) : U ∈ Module.End.invtSubmodule (ρ a).toLinearMap :=
    Submodule.topologicalClosure_mem_invtSubmodule (orbit_invariant ρ ξ a)
  let P := U.starProjection
  have hc (a : A) : Commute P (ρ a) := invariant_starProjection_commute ρ U hinv a
  have hs (i j : I) : ∃ z : ℂ,tupleEntry P i j=z • 1 :=
    hscalar (tupleEntry P i j) (commuting_tuple_entries π P hc i j)
  have hPT : Commute P (tupleOp T) := scalar_entries_commute P hs T
  have hξ : ξ∈U := R.le_topologicalClosure (by
    refine ⟨1,?_⟩
    simp [orbitLinear])
  have hPξ : P ξ=ξ := U.starProjection_eq_self_iff.mpr hξ
  have ht : tupleOp T ξ∈U := by
    apply U.starProjection_eq_self_iff.mp
    have he := congrArg (fun S : PiLp 2 (fun _ : I => H) →L[ℂ] PiLp 2 (fun _ : I => H) => S ξ) hPT.eq
    change P (tupleOp T ξ)=tupleOp T (P ξ) at he
    rw [hPξ] at he
    exact he
  exact ht

theorem pure_gns_strong_approximation (f : A →ₚ[ℂ] ℂ) (hf1 : f 1=1)
    (hpure : ofPositiveState f hf1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (ξ : I → f.GNS) (T : f.GNS →L[ℂ] f.GNS) {ε : ℝ} (hε : 0<ε) :
    ∃ a : A,∀ i,‖f.gnsStarAlgHom a (ξ i)-T (ξ i)‖<ε := by
  have hcl := strong_density_of_scalar_commutant f.gnsStarAlgHom
    (pure_gns_scalar_commutant f hf1 hpure) (WithLp.toLp 2 ξ) T
  obtain ⟨y,⟨a,rfl⟩,hy⟩ := Metric.mem_closure_iff.mp hcl ε hε
  refine ⟨a,fun i => ?_⟩
  have hbound := PiLp.norm_apply_le (tupleRepresentation f.gnsStarAlgHom a (WithLp.toLp 2 ξ)-
    tupleOp T (WithLp.toLp 2 ξ)) i
  apply hbound.trans_lt
  simpa only [dist_eq_norm,norm_sub_rev] using hy

end PureStateExcision

end
end

section

noncomputable section
namespace PureStateExcision
open scoped ComplexOrder InnerProductSpace ENNReal

variable {A H I : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable [Fintype I] [DecidableEq I]

 def selfAdjointOrbit (π : A →⋆ₐ[ℂ] (H →L[ℂ] H)) (ξ : PiLp 2 (fun _ : I => H)) :
    selfAdjoint A →ₗ[ℝ] PiLp 2 (fun _ : I => H) where
  toFun a := tupleRepresentation π a ξ
  map_add' a b := by ext i; simp
  map_smul' t a := by
    ext i
    change π (t • (a : A)) (ξ i)=t • π (a : A) (ξ i)
    rw [← Complex.coe_smul, map_smul, smul_apply, Complex.coe_smul]

lemma selfadjoint_strong_density_of_scalar_commutant (π : A →⋆ₐ[ℂ] (H →L[ℂ] H))
    (hscalar : ∀ T : H →L[ℂ] H,(∀ a,Commute T (π a)) → ∃ z : ℂ,T=z • 1)
    (ξ : PiLp 2 (fun _ : I => H)) (T : H →L[ℂ] H) (hT : IsSelfAdjoint T) :
    tupleOp T ξ∈closure (Set.range (fun a : selfAdjoint A => tupleRepresentation π a ξ)) := by
  let : InnerProductSpace ℝ (PiLp 2 (fun _ : I => H)) :=
    InnerProductSpace.rclikeToReal ℂ _
  let R := (selfAdjointOrbit π ξ).range
  change tupleOp T ξ∈R.topologicalClosure
  rw [← R.orthogonal_orthogonal_eq_closure]
  apply (Rᗮ.mem_orthogonal _).mpr
  intro η hη
  let ζ : PiLp 2 (fun _ : I ⊕ I => H) := WithLp.toLp 2 (Sum.elim ξ η)
  let g : PiLp 2 (fun _ : I ⊕ I => H) → ℝ := fun y =>
    ∑ i, (inner ℂ (η i) (y (.inl i))).re + ∑ i, (inner ℂ (y (.inr i)) (ξ i)).re
  have hg : Continuous g := by dsimp [g]; fun_prop
  have hzero (a : A) : g (tupleRepresentation π a ζ)=0 := by
    have hz := (R.mem_orthogonal' η).mp hη
      (tupleRepresentation π (a+star a) ξ) ⟨⟨a+star a,IsSelfAdjoint.add_star_self a⟩,rfl⟩
    rw [real_inner_eq_re_inner ℂ,PiLp.inner_apply] at hz
    change (∑ i,inner ℂ (η i) (tupleRepresentation π (a+star a) ξ i)).re=0 at hz
    rw [Complex.re_sum] at hz
    have hadj (i : I) : inner ℂ (η i) (π (star a) (ξ i))=
        inner ℂ (π a (η i)) (ξ i) := by
      rw [map_star,ContinuousLinearMap.star_eq_adjoint,ContinuousLinearMap.adjoint_inner_right]
    simpa [g,ζ,tupleRepresentation_apply,map_add,inner_add_right,Complex.add_re,
      Finset.sum_add_distrib,hadj] using hz
  have hclosed : IsClosed {y : PiLp 2 (fun _ : I ⊕ I => H) | g y=0} :=
    isClosed_eq hg continuous_const
  have htarget : g (tupleOp T ζ)=0 :=
    hclosed.closure_subset_iff.mpr (by rintro _ ⟨a,rfl⟩; exact hzero a)
      (strong_density_of_scalar_commutant π hscalar ζ T)
  have hsym (i : I) : inner ℂ (T (η i)) (ξ i)=inner ℂ (η i) (T (ξ i)) := by
    rw [← ContinuousLinearMap.adjoint_inner_right]
    rw [← ContinuousLinearMap.star_eq_adjoint,hT.star_eq]
  have hh : (∑ i, (inner ℂ (η i) (T (ξ i))).re)=0 := by
    simp only [g,ζ,tupleOp_apply,Sum.elim_inl,Sum.elim_inr,hsym] at htarget
    linarith
  change (∑ i,inner ℂ (η i) (T (ξ i))).re=0
  simpa only [Complex.re_sum] using hh

theorem pure_gns_selfadjoint_strong_approximation (f : A →ₚ[ℂ] ℂ) (hf1 : f 1=1)
    (hpure : ofPositiveState f hf1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (ξ : I → f.GNS) (T : f.GNS →L[ℂ] f.GNS) (hT : IsSelfAdjoint T)
    {ε : ℝ} (hε : 0<ε) :
    ∃ a : A,IsSelfAdjoint a ∧ ∀ i,‖f.gnsStarAlgHom a (ξ i)-T (ξ i)‖<ε := by
  have hcl := selfadjoint_strong_density_of_scalar_commutant f.gnsStarAlgHom
    (pure_gns_scalar_commutant f hf1 hpure) (WithLp.toLp 2 ξ) T hT
  obtain ⟨y,⟨a,rfl⟩,hy⟩ := Metric.mem_closure_iff.mp hcl ε hε
  refine ⟨a,a.property,fun i => ?_⟩
  have hbound := PiLp.norm_apply_le (tupleRepresentation f.gnsStarAlgHom a (WithLp.toLp 2 ξ)-
    tupleOp T (WithLp.toLp 2 ξ)) i
  apply hbound.trans_lt
  simpa only [dist_eq_norm,norm_sub_rev] using hy

end PureStateExcision

end
end

section

noncomputable section
namespace PureStateExcision
open scoped ComplexOrder ComplexStarModule InnerProductSpace

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

lemma symmetric_rankTwo_maps (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (ξ y : H) (hξ : ‖ξ‖=1)
    (hy : inner ℂ ξ y=0) :
    ∃ T : H →L[ℂ] H,IsSelfAdjoint T ∧ T ξ=y := by
  let T := InnerProductSpace.rankOne ℂ y ξ+InnerProductSpace.rankOne ℂ ξ y
  refine ⟨T,?_,?_⟩
  · simp [T,isSelfAdjoint_iff,ContinuousLinearMap.star_eq_adjoint,
      InnerProductSpace.adjoint_rankOne,add_comm]
  · have hy' : inner ℂ y ξ=0 := inner_eq_zero_symm.mp hy
    simp [T,InnerProductSpace.rankOne_apply,inner_self_eq_norm_sq_to_K,hξ,hy']

lemma pure_state_small_left_error (f : A →ₚ[ℂ] ℂ) (hf1 : f 1=1)
    (hpure : ofPositiveState f hf1∈(realStateCarrier (A := A)).extremePoints ℝ)
    (a : A) (ha : IsSelfAdjoint a) (hf0 : f a=0) {ε : ℝ} (hε : 0<ε) :
    ∃ b : A, (ℜ b : A)=a ∧ ‖f.gnsStarAlgHom b (Pureness.stateGNSVector f)‖<ε := by
  let ξ := Pureness.stateGNSVector f
  let y := Complex.I • (f.gnsStarAlgHom a ξ)
  have hy : inner ℂ ξ y=0 := by
    simp only [y,ξ,inner_smul_right,Pureness.stateGNS_vector_value,hf0,mul_zero]
  obtain ⟨T,hT,hTy⟩ := symmetric_rankTwo_maps f.GNS ξ y (Pureness.stateGNSVector_norm f hf1) hy
  obtain ⟨h,hh,happrox⟩ := pure_gns_selfadjoint_strong_approximation f hf1 hpure
    (fun _ : Unit => ξ) T hT hε
  let b := a+Complex.I • h
  refine ⟨b,?_,?_⟩
  · rw [realPart_apply_coe]
    have he : b+star b=(2 : ℝ) • a := by
      simp only [b,star_add,star_smul,ha.star_eq,hh.star_eq,Complex.star_def,Complex.conj_I]
      simp only [neg_smul]
      module
    rw [he,smul_smul]
    norm_num
  · have he : f.gnsStarAlgHom b ξ=Complex.I • (f.gnsStarAlgHom h ξ-y) := by
      simp only [b,map_add,map_smul,add_apply,smul_apply,y,smul_sub,smul_smul,
        Complex.I_mul_I,neg_one_smul,sub_neg_eq_add]
      abel
    rw [he,norm_smul,Complex.norm_I,one_mul]
    simpa only [hTy] using happrox ()

end PureStateExcision

end
end

end OAI
