import OAI.Analysis.CoulombTransport.StrictMinimum

namespace OAI

universe uE uF uP

noncomputable section

open Set
open scoped InnerProductSpace

namespace Problem356

variable (E : Type uE) (F : Type uF) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- The sum of the two component inner products, bundled for the usual
(max-norm) product. No inner-product-space instance on the product is used. -/
def stateDual : (E × F) →L[ℝ] ((E × F) →L[ℝ] ℝ) :=
  (((ContinuousLinearMap.compL ℝ (E × F) E ℝ).flip
      (ContinuousLinearMap.fst ℝ E F)).comp
    ((innerSL ℝ).comp (ContinuousLinearMap.fst ℝ E F))) +
  (((ContinuousLinearMap.compL ℝ (E × F) F ℝ).flip
      (ContinuousLinearMap.snd ℝ E F)).comp
    ((innerSL ℝ).comp (ContinuousLinearMap.snd ℝ E F)))

@[simp] theorem stateDual_apply (u v : E × F) :
    stateDual E F u v = ⟪u.1, v.1⟫_ℝ + ⟪u.2, v.2⟫_ℝ := by
  rfl

theorem stateDual_apply_comm (u v : E × F) :
    stateDual E F u v = stateDual E F v u := by
  simp only [stateDual_apply, real_inner_comm]

/-- Differentiating the scalar representative of a product-state gradient. -/
theorem hasFDerivAt_stateDual_comp {P : Type uP} [NormedAddCommGroup P]
    [NormedSpace ℝ P] {G : P → E × F} {G' : P →L[ℝ] E × F} {p : P}
    (hG : HasFDerivAt G G' p) :
    HasFDerivAt (fun q => stateDual E F (G q)) ((stateDual E F).comp G') p :=
  by
  exact HasFDerivAt.comp (𝕜 := ℝ) (g := stateDual E F) p
    ((stateDual E F).hasFDerivAt (x := G p)) hG

/-- The quadratic form of the scalar Hessian agrees with the product-state
coercivity expression, with the argument order used by matrix certificates. -/
theorem stateDual_comp_quadratic (A : (E × F) →L[ℝ] E × F) (v : E × F) :
    ((stateDual E F).comp A) v v =
      ⟪v.1, (A v).1⟫_ℝ + ⟪v.2, (A v).2⟫_ℝ := by
  simp only [ContinuousLinearMap.comp_apply, stateDual_apply, real_inner_comm]

/-- A gradient with positive product-state Jacobian gives strict convexity of
its scalar potential. This bridges matrix coercivity of the stationarity map
to positivity of the scalar Hessian. -/
theorem strictConvexOn_of_positive_stateGradient
    {s : Set (E × F)} {f : E × F → ℝ} {G : E × F → E × F}
    {A : E × F → (E × F) →L[ℝ] E × F}
    (hs : Convex ℝ s) (hsopen : IsOpen s)
    (hf : ∀ z ∈ s, HasFDerivAt f (stateDual E F (G z)) z)
    (hG : ∀ z ∈ s, HasFDerivAt G (A z) z)
    (hpos : ∀ z ∈ s, ∀ v : E × F, v ≠ 0 →
      0 < ⟪v.1, (A z v).1⟫_ℝ + ⟪v.2, (A z v).2⟫_ℝ) :
    StrictConvexOn ℝ s f := by
  apply strictConvexOn_of_positive_hessian hs hsopen hf
    (fun z hz => hasFDerivAt_stateDual_comp E F (hG z hz))
  intro z hz v hv
  simpa only [stateDual_comp_quadratic] using hpos z hz v hv

/-- Vanishing of the product-state gradient gives the scalar stationary
condition needed by the supporting-certificate theorems. -/
theorem hasFDerivAt_zero_of_stateGradient_eq_zero
    {f : E × F → ℝ} {G : E × F → E × F} {z : E × F}
    (hf : HasFDerivAt f (stateDual E F (G z)) z) (hG : G z = 0) :
    HasFDerivAt f (0 : (E × F) →L[ℝ] ℝ) z := by
  simpa only [hG, map_zero] using hf

end Problem356

end

end OAI
