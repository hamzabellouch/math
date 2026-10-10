import Mathlib
import OAI.Probability.BinarySweep.TensorBounds.SignedTypeCentrality
import OAI.Probability.BinarySweep.MatrixBounds.SpectralMoment

namespace OAI

noncomputable section

section

open scoped BigOperators Classical ComplexOrder MonoidAlgebra
open Matrix

namespace BinaryCoordinateSweeps
open Density Irrep Representation

lemma euclidean_pow {I : Type*} [Fintype I] [DecidableEq I]
    (M : Matrix I I ℂ) (q : ℕ) : (M^q).toEuclideanLin=M.toEuclideanLin^q := by
  induction q with
  | zero => simp only [pow_zero,Matrix.toLpLin_one,Module.End.one_eq_id]
  | succ q ih => rw [pow_succ,Matrix.toLpLin_mul_same,ih,pow_succ,Module.End.mul_eq_comp]

lemma projected_gram_power {I : Type*} [Fintype I] [DecidableEq I]
    (P M : Matrix I I ℂ) (hP : P.IsHermitian) (hPP : P*P=P) (hPM : P*M=M*P)
    {q : ℕ} (hq : 0 < q) :
    (star (P*M)*(P*M))^q = (star M*M)^q*P := by
  have hs : P*star M=star M*P := by
    have hh := congrArg star hPM
    simpa only [star_mul,show star P=P from hP.eq] using hh.symm
  have hc : Commute (star M*M) P := by
    change star M*M*P=P*(star M*M)
    rw [mul_assoc,← hPM,← mul_assoc,← hs,mul_assoc]
  have he : star (P*M)*(P*M)=(star M*M)*P := by
    simp only [star_mul,show star P=P from hP.eq]
    rw [mul_assoc,← mul_assoc P P M,hPP,hPM,← mul_assoc]
  rw [he,hc.mul_pow,(show IsIdempotentElem P from hPP).pow_eq (ne_of_gt hq)]

lemma trace_mul_projection {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] (S : Submodule ℂ W) (B : W →ₗ[ℂ] W)
    (hS : ∀w∈S, B w∈S) :
    LinearMap.trace ℂ W (B*S.starProjection.toLinearMap)=
      LinearMap.trace ℂ S (B.restrict hS) := by
  have hm (w : W) : (B*S.starProjection.toLinearMap) w∈S :=
    hS _ (S.starProjection_apply_mem w)
  have he : (B*S.starProjection.toLinearMap).restrict (fun w _ => hm w)=B.restrict hS := by
    ext w
    change B (S.starProjection w.val)=B w.val
    rw [Submodule.starProjection_eq_self_iff.mpr w.property]
  rw [← LinearMap.trace_restrict_eq_of_forall_mem S _ hm,he]

namespace Signed
variable {A : Type*} [Fintype A] [DecidableEq A] {n : ℕ}
  {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def signedAverage (p : A → Bool) (w : Equiv.Perm (Fin n) → ℂ) :
    Matrix (Fin n → A) (Fin n → A) ℂ := ∑g, w g • actionMatrix p g

lemma signedAverage_linear (p : A → Bool) (w : Equiv.Perm (Fin n) → ℂ) :
    (signedAverage p w).toEuclideanLin=groupAverage (hilbertTensorRep p n) w := by
  simp only [signedAverage,map_sum,map_smul,actionMatrix_linear,groupAverage]

omit [FiniteDimensional ℂ V] in
lemma isotypicProjection_commutes_average (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) (w : Equiv.Perm (Fin n) → ℂ) :
    isotypicProjection p ρ*signedAverage p w=signedAverage p w*isotypicProjection p ρ := by
  simp only [signedAverage,Finset.mul_sum,Finset.sum_mul,mul_smul_comm,smul_mul_assoc,
    typeProjection_commutes_action]

theorem local_projected_moment (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) (w : Equiv.Perm (Fin n) → ℂ) {q : ℕ} (hq : 0 < q) :
    TraceHolder.matrixMoment q (isotypicProjection p ρ*signedAverage p w)=
      (Module.finrank ℂ (IntertwiningMap ρ (hilbertTensorRep p n)):ℝ)*evenMoment q (groupAverage ρ w) := by
  unfold TraceHolder.matrixMoment
  rw [projected_gram_power _ _ (isotypicProjection_psd p ρ).isHermitian
    (projectionMatrix_idempotent _) (isotypicProjection_commutes_average p ρ w) hq]
  rw [← trace_toEuclideanLinear]
  simp only [Matrix.toLpLin_mul_same,← Module.End.mul_eq_comp,euclidean_pow,
    Matrix.star_eq_conjTranspose,Matrix.toEuclideanLin_conjTranspose_eq_adjoint,signedAverage_linear]
  have hP : (isotypicProjection p ρ).toEuclideanLin=
      (isotypicSpan ρ (hilbertTensorRep p n)).starProjection.toLinearMap := by
    rw [hilbert_isotypic_eq]; exact projectionMatrix_linear _
  rw [hP]
  have hc := even_compatible ρ (hilbertTensorRep p n) w hρ (hilbertTensorRep_unitary p) q
  rw [trace_mul_projection _ _ (isotypic_invariant_of_compatible ρ _ _ _ hc),
    isotypic_trace ρ _ _ _ hc]
  simp only [evenMoment,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero]

lemma hilbert_multiplicity_bound (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible] :
    Module.finrank ℂ (IntertwiningMap ρ (hilbertTensorRep p n)) ≤ (n+1)^((Fintype.card A)^2) := by
  have hd : 0 < Module.finrank ℂ V := by
    let : Nontrivial ρ.asModule := IsSimpleModule.nontrivial ℂ[Equiv.Perm (Fin n)] ρ.asModule
    rw [← ρ.asModuleEquiv.finrank_eq]
    exact Module.finrank_pos
  have h := isotypicSpan_rank_bound p ρ
  rw [← hilbertSubspace_finrank,← hilbert_isotypic_eq p ρ,isotypicSpan_finrank_eq] at h
  exact Nat.le_of_mul_le_mul_left h hd

theorem local_projected_moment_le (p : A → Bool)
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [ρ.IsIrreducible]
    (hρ : ∀g v, ‖ρ g v‖=‖v‖) (w : Equiv.Perm (Fin n) → ℂ) {q : ℕ} (hq : 0 < q) :
    TraceHolder.matrixMoment q (isotypicProjection p ρ*signedAverage p w) ≤
      (n+1:ℝ)^((Fintype.card A)^2)*evenMoment q (groupAverage ρ w) := by
  rw [local_projected_moment p ρ hρ w hq]
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast hilbert_multiplicity_bound p ρ
  · exact (Complex.nonneg_iff.mp (positive_pow (LinearMap.isPositive_adjoint_comp_self _) q).trace_nonneg).1

end Signed
end BinaryCoordinateSweeps

end

open scoped BigOperators Classical

namespace BinaryCoordinateSweeps.Fourier
open Representation

variable (G : Type*) [Group G] [Fintype G]

abbrev RegularSpace := EuclideanSpace ℂ G

def regularMap (g : G) : RegularSpace G →ₗ[ℂ] RegularSpace G where
  toFun v := WithLp.toLp 2 (fun x => v (g⁻¹*x))
  map_add' v w := by ext x; rfl
  map_smul' a v := by ext x; rfl

def regular : Representation ℂ G (RegularSpace G) where
  toFun := regularMap G
  map_one' := by ext v x; simp [regularMap]
  map_mul' g h := by ext v x; simp [regularMap,mul_assoc]

omit [Fintype G] in
@[simp] lemma regular_apply (g : G) (v : RegularSpace G) (x : G) :
    regular G g v x=v (g⁻¹*x) := rfl

lemma regular_unitary (g : G) (v : RegularSpace G) : ‖regular G g v‖=‖v‖ := by
  simp only [EuclideanSpace.norm_eq]
  congr 1
  exact Equiv.sum_comp (Equiv.mulLeft g⁻¹) (fun x => ‖v x‖^2)

lemma regular_character (g : G) :
    (regular G).character g=if g=1 then (Fintype.card G:ℂ) else 0 := by
  rw [Representation.character,LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun G ℂ)]
  by_cases hg : g=1
  · subst g; simp
  · rw [ite_eq_right hg]
    apply Finset.sum_eq_zero
    intro x _
    rw [EuclideanSpace.basisFun_inner,regular_apply,EuclideanSpace.basisFun_apply]
    simp only [PiLp.single_apply]
    have hh : g⁻¹*x≠x := by
      intro he
      have := mul_right_cancel (show g⁻¹*x=1*x from by simpa using he)
      exact hg (inv_eq_one.mp this)
    simp [hh]

lemma regular_multiplicity {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ρ : Representation ℂ G V) :
    Module.finrank ℂ (IntertwiningMap ρ (regular G))=Module.finrank ℂ V := by
  have hc : (Nat.card G:ℂ)≠0 := by
    rw [Nat.card_eq_fintype_card]
    exact_mod_cast Fintype.card_ne_zero
  let : Invertible (Nat.card G:ℂ) := invertibleOfNonzero hc
  have hh := card_inv_mul_sum_char_mul_char_eq_finrank ρ (regular G)
  simp only [regular_character,ite_mul,zero_mul] at hh
  simp only [Finset.sum_ite_eq',Finset.mem_univ,ite_true,inv_one,char_one] at hh
  rw [←Nat.card_eq_fintype_card,←mul_assoc,inv_mul_cancel₀ hc,one_mul] at hh
  exact_mod_cast hh.symm

lemma regular_average_apply (p : G → ℂ) (v : RegularSpace G) (x : G) :
    Irrep.groupAverage (regular G) p v x=∑g,p g*v (g⁻¹*x) := by
  simp [Irrep.groupAverage,LinearMap.sum_apply,LinearMap.smul_apply]

lemma regular_moment_one (p : G → ℂ) :
    Irrep.evenMoment 1 (Irrep.groupAverage (regular G) p)=
      (Fintype.card G:ℝ)*(∑g,‖p g‖^2) := by
  unfold Irrep.evenMoment
  rw [pow_one,LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun G ℂ)]
  simp only [Complex.re_sum,Module.End.mul_apply,LinearMap.adjoint_inner_right,inner_self_eq_norm_sq_to_K]
  have he (x : G) : ‖Irrep.groupAverage (regular G) p ((EuclideanSpace.basisFun G ℂ) x)‖^2=
      ∑g,‖p g‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    have ha (y : G) : Irrep.groupAverage (regular G) p ((EuclideanSpace.basisFun G ℂ) x) y=p (y*x⁻¹) := by
      rw [regular_average_apply]
      simp only [EuclideanSpace.basisFun_apply,PiLp.single_apply]
      have hiff (g : G) : x=g⁻¹*y ↔ g=y*x⁻¹ := by
        constructor <;> intro hh
        · calc g=(g*x)*x⁻¹ := by group
                 _=y*x⁻¹ := by rw [hh]; simp
        · subst g; group
      simp_rw [eq_comm (a:=_⁻¹*y) (b:=x),hiff,mul_ite,mul_one,mul_zero]
      simp
    simp_rw [ha]
    exact Equiv.sum_comp (Equiv.mulRight x⁻¹) (fun g => ‖p g‖^2)
  change (∑i, ((‖Irrep.groupAverage (regular G) p ((EuclideanSpace.basisFun G ℂ) i)‖:ℂ)^2).re)=_
  simp only [←Complex.ofReal_pow,Complex.ofReal_re]
  simp_rw [he]
  simp

end BinaryCoordinateSweeps.Fourier

end

end OAI
