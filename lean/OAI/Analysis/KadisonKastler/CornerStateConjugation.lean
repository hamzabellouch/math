import OAI.Analysis.KadisonKastler.ComplementaryCornerUnitary
import OAI.Analysis.KadisonKastler.CornerStateWeights

namespace OAI

/-! # A single state comparison from two corner conjugations

Normalized corner estimates combine under the unitary formed from
two complementary corner unitaries. The resulting state comparison
is bounded by the sum of the corner errors.
-/

namespace KadisonKastler

open Generator.Tracial

noncomputable section

variable {A : Type*} [CStarAlgebra A]

def sandwichFunctional (φ : A →L[ℂ] ℂ) (u : A) : A →L[ℂ] ℂ :=
  φ.comp (((ContinuousLinearMap.mul ℂ A).flip u).comp
    (ContinuousLinearMap.mul ℂ A (star u)))

@[simp] theorem sandwichFunctional_apply (φ : A →L[ℂ] ℂ) (u x : A) :
    sandwichFunctional φ u x = φ (star u*x*u) := rfl

theorem sandwichFunctional_centralizes (φ : A →L[ℂ] ℂ) (p u : A)
    (hp : IsStarProjection p) (hpu : p*u=u*p)
    (hφ : ∀ x : A, φ (p*x)=φ (x*p)) :
    ∀ x : A, sandwichFunctional φ u (p*x)=sandwichFunctional φ u (x*p) := by
  have hs : star u*p=p*star u := by
    simpa only [star_mul,hp.isSelfAdjoint.star_eq] using congrArg star hpu
  intro x
  change φ (star u*(p*x)*u)=φ (star u*(x*p)*u)
  have hl : star u*(p*x)*u=p*(star u*x*u) := by
    rw [← mul_assoc (star u) p,hs]
    simp only [mul_assoc]
  have hr : star u*(x*p)*u=(star u*x*u)*p := by
    rw [mul_assoc (star u) (x*p),mul_assoc x p,hpu]
    simp only [mul_assoc]
  rw [hl,hr,hφ]

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  {M : VonNeumannAlgebra H}

theorem sandwichFunctional_vectorFunctional (ξ : H) (u : Algebra M) :
    sandwichFunctional (vectorFunctional ξ) u = vectorFunctional (u.val ξ) := by
  ext x
  change inner ℂ ξ (u.val.adjoint (x.val (u.val ξ))) =
    inner ℂ (u.val ξ) (x.val (u.val ξ))
  exact u.val.adjoint_inner_right _ _

theorem cornerFunctional_patched_vector (p : AlgebraProjection M)
    (u v : Algebra M) (hu : star u*u=p.val) (hu' : u*star u=p.val)
    (hv : star v*v=1-p.val) (hv' : v*star v=1-p.val) (ξ : H) :
    cornerFunctional (vectorFunctional ((u+v).val ξ)) p.val =
        sandwichFunctional (vectorFunctional ξ) u ∧
      cornerFunctional (vectorFunctional ((u+v).val ξ)) (1-p.val) =
        sandwichFunctional (vectorFunctional ξ) v := by
  obtain ⟨hpu,_,hqv,_⟩ :=
    complementaryCornerUnitary_compressions p u v hu hu' hv hv'
  constructor
  · rw [cornerFunctional_vectorFunctional p, sandwichFunctional_vectorFunctional]
    congr 1
    exact congrArg (fun a : Algebra M => a.val ξ) hpu
  · rw [cornerFunctional_vectorFunctional (⟨1-p.val,p.property.one_sub⟩ : AlgebraProjection M),
      sandwichFunctional_vectorFunctional]
    congr 1
    exact congrArg (fun a : Algebra M => a.val ξ) hqv

theorem patched_vector_state_centralizes (p : AlgebraProjection M)
    (u v : Algebra M) (hu : star u*u=p.val) (hu' : u*star u=p.val)
    (hv : star v*v=1-p.val) (hv' : v*star v=1-p.val) (ξ : H)
    (hφ : ∀ x : Algebra M, vectorFunctional ξ (p.val*x)=vectorFunctional ξ (x*p.val)) :
    ∀ x : Algebra M, vectorFunctional ((u+v).val ξ) (p.val*x)=
      vectorFunctional ((u+v).val ξ) (x*p.val) := by
  have hc := complementaryCornerUnitary_compressions p u v hu hu' hv hv'
  rw [← sandwichFunctional_vectorFunctional]
  exact sandwichFunctional_centralizes _ _ _ p.property (hc.1.trans hc.2.1.symm) hφ

/-- Once each corner has a normalized comparison, their sum is the required
unitary comparison on the whole algebra. -/
theorem patched_vector_state_norm_le (p : AlgebraProjection M)
    (u v : Algebra M) (hu : star u*u=p.val) (hu' : u*star u=p.val)
    (hv : star v*v=1-p.val) (hv' : v*star v=1-p.val) (ξ ζ : H)
    (hξ : Function.Injective (algebraVectorMap M ξ)) (hnξ : ‖ξ‖=1)
    (hζ : Function.Injective (algebraVectorMap M ζ)) (hnζ : ‖ζ‖=1)
    (hp0 : p.val≠0) (hp1 : p.val≠1)
    (hcξ : ∀ x : Algebra M, vectorFunctional ξ (p.val*x)=vectorFunctional ξ (x*p.val))
    (hcζ : ∀ x : Algebra M, vectorFunctional ζ (p.val*x)=vectorFunctional ζ (x*p.val))
    (δ : ℝ)
    (h₀ : ‖(projectionVectorWeight p ξ)⁻¹ • sandwichFunctional (vectorFunctional ξ) u -
      vectorCornerState p ζ‖ ≤ δ)
    (h₁ : ‖(1-projectionVectorWeight p ξ)⁻¹ • sandwichFunctional (vectorFunctional ξ) v -
      vectorCornerState ⟨1-p.val,p.property.one_sub⟩ ζ‖ ≤ δ) :
    ‖vectorFunctional (M := M) ((u+v).val ξ)-vectorFunctional ζ‖ ≤
      δ+2*|projectionVectorWeight p ξ-projectionVectorWeight p ζ| := by
  have ha := projectionVectorWeight_mem_Ioo p ξ hξ hnξ hp0 hp1
  have hb := projectionVectorWeight_mem_Ioo p ζ hζ hnζ hp0 hp1
  have hbq : 0 < projectionVectorWeight ⟨1-p.val,p.property.one_sub⟩ ζ :=
    projectionVectorWeight_pos _ ζ hζ (sub_ne_zero.mpr hp1.symm)
  have hbqeq : 1-projectionVectorWeight p ζ =
      projectionVectorWeight ⟨1-p.val,p.property.one_sub⟩ ζ := by
    have he := projectionVectorWeight_add_complement p ζ
    rw [hnζ] at he
    linarith
  obtain ⟨hcomp₀,hcomp₁⟩ := cornerFunctional_patched_vector p u v hu hu' hv hv' ξ
  apply twoCorner_state_norm_le
    (vectorFunctional ((u+v).val ξ)) (vectorFunctional ζ)
    ((projectionVectorWeight p ξ)⁻¹ • sandwichFunctional (vectorFunctional ξ) u)
    ((1-projectionVectorWeight p ξ)⁻¹ • sandwichFunctional (vectorFunctional ξ) v)
    (vectorCornerState p ζ) (vectorCornerState ⟨1-p.val,p.property.one_sub⟩ ζ)
    p.val p.property
    (patched_vector_state_centralizes p u v hu hu' hv hv' ξ hcξ) hcζ
    (projectionVectorWeight p ξ) (projectionVectorWeight p ζ) δ ha.1.le ha.2.le
  · rw [hcomp₀,smul_smul,mul_inv_cancel₀ ha.1.ne',one_smul]
  · rw [hcomp₁,smul_smul,mul_inv_cancel₀ (sub_pos.mpr ha.2).ne',one_smul]
  · rw [cornerFunctional_vectorFunctional,weight_smul_vectorCornerState p ζ hb.1]
  · rw [cornerFunctional_vectorFunctional (⟨1-p.val,p.property.one_sub⟩ : AlgebraProjection M),
      hbqeq,weight_smul_vectorCornerState _ ζ hbq]
  · exact vectorCornerState_norm_le p ζ hb.1
  · exact vectorCornerState_norm_le _ ζ hbq
  · exact h₀
  · exact h₁

end

end KadisonKastler

end OAI
