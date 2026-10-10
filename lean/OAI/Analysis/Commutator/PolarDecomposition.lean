import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped InnerProductSpace ComplexOrder Topology

namespace Kadison.Polar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma norm_abs_apply (T : H →L[ℂ] H) (x : H) : ‖CFC.abs T x‖=‖T x‖ := by
  have hs : star (CFC.abs T)=CFC.abs T := (IsSelfAdjoint.of_nonneg (CFC.abs_nonneg T)).star_eq
  have he : inner ℂ (CFC.abs T x) (CFC.abs T x)=inner ℂ (T x) (T x) := by
    rw [←ContinuousLinearMap.adjoint_inner_right,←ContinuousLinearMap.star_eq_adjoint,hs]
    change inner ℂ x ((CFC.abs T*CFC.abs T) x)=_
    rw [CFC.abs_mul_abs,mul_apply_eq_comp,ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  have hn : ‖CFC.abs T x‖^2=‖T x‖^2 := by
    rw [@norm_sq_eq_re_inner ℂ H _ _,@norm_sq_eq_re_inner ℂ H _ _]
    exact congrArg RCLike.re he
  nlinarith [norm_nonneg (CFC.abs T x),norm_nonneg (T x)]

def initial (T : H →L[ℂ] H) : Submodule ℂ H :=
  (LinearMap.range (CFC.abs T).toLinearMap).topologicalClosure

instance (T : H →L[ℂ] H) : CompleteSpace (initial T) :=
  (LinearMap.range (CFC.abs T).toLinearMap).isClosed_topologicalClosure.completeSpace_coe

def absToInitial (T : H →L[ℂ] H) : H →ₗ[ℂ] initial T :=
  (CFC.abs T).toLinearMap.codRestrict (initial T) (fun x =>
    Submodule.le_topologicalClosure _ (LinearMap.mem_range_self _ x))

lemma absToInitial_dense (T : H →L[ℂ] H) : DenseRange (absToInitial T) := by
  let inc : LinearMap.range (CFC.abs T).toLinearMap → initial T :=
    fun x => ⟨x.val,Submodule.le_topologicalClosure _ x.property⟩
  have hi : DenseRange inc := by
    change DenseRange (Set.inclusion (Submodule.le_topologicalClosure _))
    apply (denseRange_inclusion_iff _).2
    exact fun _ h => h
  have hs : Function.Surjective (CFC.abs T).toLinearMap.rangeRestrict := by
    rintro ⟨y,x,rfl⟩
    exact ⟨x,rfl⟩
  exact hi.comp hs.denseRange (continuous_inclusion (Submodule.le_topologicalClosure _))

def initialMap (T : H →L[ℂ] H) : initial T →L[ℂ] H :=
  T.toLinearMap.extendOfNorm (absToInitial T)

lemma initialMap_abs (T : H →L[ℂ] H) (x : H) :
    initialMap T (absToInitial T x)=T x := by
  apply LinearMap.extendOfNorm_eq (absToInitial_dense T)
  refine ⟨1,fun x => ?_⟩
  change ‖T x‖≤1*‖CFC.abs T x‖
  rw [one_mul,norm_abs_apply]

lemma initialMap_norm (T : H →L[ℂ] H) (x : initial T) : ‖initialMap T x‖=‖x‖ := by
  refine (absToInitial_dense T).induction_on x
    (isClosed_eq (initialMap T).continuous.norm continuous_norm) ?_
  intro y
  rw [initialMap_abs]
  exact (norm_abs_apply T y).symm

def partialIsometry (T : H →L[ℂ] H) : H →L[ℂ] H :=
  (initialMap T).comp (initial T).orthogonalProjectionOnto

lemma partialIsometry_mem (T : H →L[ℂ] H) (x : initial T) :
    partialIsometry T x=initialMap T x := by
  exact congrArg (initialMap T)
    (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self x)

lemma factorization (T : H →L[ℂ] H) : partialIsometry T*CFC.abs T=T := by
  ext x
  change partialIsometry T (absToInitial T x)=T x
  rw [partialIsometry_mem,initialMap_abs]

lemma initialMap_adjoint_comp (T : H →L[ℂ] H) :
    (initialMap T).adjoint.comp (initialMap T)=1 :=
  (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mp (initialMap_norm T)

lemma partialIsometry_initial (T : H →L[ℂ] H) :
    star (partialIsometry T)*partialIsometry T=(initial T).starProjection := by
  change (partialIsometry T).adjoint.comp (partialIsometry T)=_
  rw [partialIsometry,ContinuousLinearMap.adjoint_comp,Submodule.adjoint_orthogonalProjectionOnto,
    ContinuousLinearMap.comp_assoc,←ContinuousLinearMap.comp_assoc (initialMap T).adjoint,
    initialMap_adjoint_comp]
  simp only [ContinuousLinearMap.one_def,ContinuousLinearMap.id_comp]
  rfl

lemma partialIsometry_mul_initial (T : H →L[ℂ] H) :
    partialIsometry T*(initial T).starProjection=partialIsometry T := by
  ext x
  change initialMap T ((initial T).orthogonalProjectionOnto ((initial T).starProjection x))=_
  rw [Submodule.starProjection_apply,Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]
  rfl

lemma partialIsometry_final_projection (T : H →L[ℂ] H) :
    IsStarProjection (partialIsometry T*star (partialIsometry T)) := by
  constructor
  · change (partialIsometry T*star (partialIsometry T))*(partialIsometry T*star (partialIsometry T))=_
    calc
      _=(partialIsometry T*(star (partialIsometry T)*partialIsometry T))*star (partialIsometry T) := by noncomm_ring
      _=partialIsometry T*star (partialIsometry T) := by rw [partialIsometry_initial,partialIsometry_mul_initial]
  · exact IsSelfAdjoint.mul_star_self _

lemma initial_invariant (T B : H →L[ℂ] H) (hB : Commute (CFC.abs T) B) :
    ∀ x∈initial T, B x∈initial T := by
  intro x hx
  apply closure_minimal (t := {x : H | B x∈initial T}) ?_ ?_ hx
  · rintro y ⟨z,rfl⟩
    apply Submodule.le_topologicalClosure
    exact ⟨B z,congrArg (fun R : H →L[ℂ] H => R z) hB.eq⟩
  · exact (LinearMap.range (CFC.abs T).toLinearMap).isClosed_topologicalClosure.preimage B.continuous

lemma projection_commutes (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    (B : H →L[ℂ] H) (hB : ∀ x∈P, B x∈P) (hsB : ∀ x∈P, star B x∈P) :
    P.starProjection*B=B*P.starProjection := by
  ext x
  change P.starProjection (B x)=B (P.starProjection x)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hB _ (P.starProjection_apply_mem x)
  · intro w hw
    rw [←map_sub,←ContinuousLinearMap.adjoint_inner_right]
    exact Submodule.starProjection_inner_eq_zero x _ (hsB w hw)

lemma partialIsometry_commutes (T B : H →L[ℂ] H)
    (hB : Commute T B) (hsB : Commute T (star B)) :
    Commute (partialIsometry T) B := by
  have hab : Commute (CFC.abs T) B := hB.cfcAbs_left hsB
  have habs : Commute (CFC.abs T) (star B) := hsB.cfcAbs_left (by simpa using hB)
  have hp := projection_commutes (initial T) B (initial_invariant T B hab)
    (initial_invariant T (star B) habs)
  have hgen : ∀ x : initial T, partialIsometry T (B x)=B (partialIsometry T x) := by
    intro x
    refine (absToInitial_dense T).induction_on x
      (isClosed_eq (by fun_prop) (by fun_prop)) ?_
    · intro y
      have haby := congrArg (fun R : H →L[ℂ] H => R y) hab.eq
      change CFC.abs T (B y)=B (CFC.abs T y) at haby
      have ht := congrArg (fun R : H →L[ℂ] H => R y) hB.eq
      change T (B y)=B (T y) at ht
      have hf : ∀ z, partialIsometry T (CFC.abs T z)=T z := fun z =>
        congrArg (fun R : H →L[ℂ] H => R z) (factorization T)
      change partialIsometry T (B (CFC.abs T y))=B (partialIsometry T (CFC.abs T y))
      rw [←haby,hf,hf]
      exact ht
  have hvp : ∀ x : H, partialIsometry T ((initial T).starProjection x)=partialIsometry T x :=
    fun x => congrArg (fun R : H →L[ℂ] H => R x) (partialIsometry_mul_initial T)
  change partialIsometry T*B=B*partialIsometry T
  ext x
  change partialIsometry T (B x)=B (partialIsometry T x)
  rw [←hvp (B x)]
  rw [show (initial T).starProjection (B x)=B ((initial T).starProjection x) from
    congrArg (fun R : H →L[ℂ] H => R x) hp]
  rw [hgen ⟨(initial T).starProjection x,(initial T).starProjection_apply_mem x⟩,hvp]

theorem partialIsometry_mem_vonNeumann (M : VonNeumannAlgebra H)
    {T : H →L[ℂ] H} (hT : T∈M) : partialIsometry T∈M := by
  change partialIsometry T∈M.carrier
  rw [←M.centralizer_centralizer']
  intro B hB
  have hb : Commute T B := hB T hT
  have hs : Commute T (star B) := by
    simpa only [star_star] using (show Commute (star T) B from hB (star T) (star_mem hT)).star_star
  exact (partialIsometry_commutes T B hb hs).eq.symm

end Kadison.Polar

end

end
end

end OAI
