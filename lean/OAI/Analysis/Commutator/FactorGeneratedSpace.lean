import Mathlib

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace CStarAlgebra

namespace Kadison.CbFactor

variable {A H K : Type*} [CStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]

def generated (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) : Submodule ℂ K :=
  (Submodule.span ℂ {x : K | ∃ a : A,∃ u : H,ρ a (W u)=x}).topologicalClosure

instance (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) : IsClosed (generated ρ W : Set K) :=
  Submodule.isClosed_topologicalClosure _

lemma generated_generator (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (a : A) (u : H) :
    ρ a (W u)∈generated ρ W :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨a,u,rfl⟩)

lemma generated_right (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (u : H) :
    W u∈generated ρ W := by simpa using generated_generator ρ W 1 u

lemma generated_invariant (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (a : A) :
    ∀ x∈generated ρ W,ρ a x∈generated ρ W := by
  intro x hx
  apply closure_minimal (t:={x | ρ a x∈generated ρ W}) ?_
    ((Submodule.isClosed_topologicalClosure _).preimage (ρ a).continuous) hx
  change Submodule.span ℂ {x : K | ∃ b : A,∃ u : H,ρ b (W u)=x} ≤
    (generated ρ W).comap (ρ a).toLinearMap
  apply Submodule.span_le.mpr
  rintro y ⟨b,u,rfl⟩
  change ρ a (ρ b (W u))∈generated ρ W
  simpa only [map_mul,mul_apply_eq_comp] using generated_generator ρ W (a*b) u

lemma generated_projection_commutes (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) (a : A) :
    (generated ρ W).starProjection * ρ a=ρ a * (generated ρ W).starProjection := by
  ext x
  change (generated ρ W).starProjection (ρ a x)=ρ a ((generated ρ W).starProjection x)
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact generated_invariant ρ W a _ ((generated ρ W).starProjection_apply_mem x)
  · intro w hw
    rw [←map_sub,←ContinuousLinearMap.adjoint_inner_right]
    apply Submodule.starProjection_inner_eq_zero x
    simpa only [map_star,ContinuousLinearMap.star_eq_adjoint] using generated_invariant ρ W (star a) w hw

lemma generated_projection_right (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K)) (W : H →L[ℂ] K) :
    (generated ρ W).starProjection.comp W=W := by
  ext x
  exact Submodule.starProjection_eq_self_iff.mpr (generated_right ρ W x)

variable [CompleteSpace H] (π : A →ₐ[ℂ] (H →L[ℂ] H)) (ρ : A →⋆ₐ[ℂ] (K →L[ℂ] K))
  (V W : H →L[ℂ] K)
  (hfactor : ∀ a : A,π a=V.adjoint.comp ((ρ a).comp W))

include hfactor in
lemma factor_intertwines_on_generated (a : A) {x : K} (hx : x∈generated ρ W) :
    π a (V.adjoint x)=V.adjoint (ρ a x) := by
  let D : K →L[ℂ] H := (π a).comp V.adjoint-V.adjoint.comp (ρ a)
  have hd : generated ρ W ≤ D.ker := by
    apply Submodule.topologicalClosure_minimal _ ?_ D.isClosed_ker
    apply Submodule.span_le.mpr
    rintro y ⟨b,u,rfl⟩
    change π a (V.adjoint (ρ b (W u)))-V.adjoint (ρ a (ρ b (W u)))=0
    apply sub_eq_zero.mpr
    have hb := congrArg (fun T : H →L[ℂ] H => T u) (hfactor b)
    have hab := congrArg (fun T : H →L[ℂ] H => T u) (hfactor (a*b))
    simp only [ContinuousLinearMap.comp_apply] at hb hab
    rw [←hb,←mul_apply_eq_comp,←map_mul,hab]
    simp only [map_mul,mul_apply_eq_comp]
  exact sub_eq_zero.mp (hd hx)

def leftCompression : K →L[ℂ] H := V.adjoint.comp (generated ρ W).starProjection

include hfactor in
lemma leftCompression_right : (leftCompression ρ V W).comp W=1 := by
  rw [leftCompression,ContinuousLinearMap.comp_assoc,generated_projection_right]
  simpa [ContinuousLinearMap.one_def] using (hfactor 1).symm

include hfactor in
lemma leftCompression_intertwines (a : A) :
    (π a).comp (leftCompression ρ V W)=(leftCompression ρ V W).comp (ρ a) := by
  ext x
  change π a (V.adjoint ((generated ρ W).starProjection x))=
    V.adjoint ((generated ρ W).starProjection (ρ a x))
  rw [factor_intertwines_on_generated π ρ V W hfactor a ((generated ρ W).starProjection_apply_mem x)]
  congr 1
  exact (congrArg (fun T : K →L[ℂ] K => T x) (generated_projection_commutes ρ W a)).symm

end Kadison.CbFactor

end

end
end

end OAI
