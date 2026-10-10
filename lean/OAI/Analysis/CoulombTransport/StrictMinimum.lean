import Mathlib

namespace OAI

universe uE uP

noncomputable section

open Set Filter
open scoped Topology

namespace Problem356

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A stationary point of a convex differentiable function is a global minimizer
on its convexity domain. -/
theorem convex_isMinOn_of_hasFDerivAt_zero {s : Set E} {f : E → ℝ} {x : E}
    (hf : ConvexOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) : IsMinOn f s x := by
  intro y hy
  have hline := hf.comp_affineMap (AffineMap.lineMap x y)
  have hderiv : HasDerivAt (f ∘ AffineMap.lineMap x y) 0 (0 : ℝ) := by
    have hd' : HasFDerivAt f (0 : E →L[ℝ] ℝ) ((AffineMap.lineMap x y) (0 : ℝ)) := by
      simpa using hd
    have h := hd'.comp_hasDerivAt (0 : ℝ)
      (AffineMap.hasDerivAt_lineMap : HasDerivAt (AffineMap.lineMap x y) (y - x) (0 : ℝ))
    simpa using h
  have hle := hline.le_slope_of_hasDerivAt
    (by simpa using hx) (by simpa using hy) (by norm_num : (0 : ℝ) < 1) hderiv
  simpa [slope_def_field] using hle

/-- Strict convexity upgrades a stationary point to the unique minimum. -/
theorem strictConvex_eq_iff_of_hasFDerivAt_zero {s : Set E} {f : E → ℝ} {x : E}
    (hf : StrictConvexOn ℝ s f) (hx : x ∈ s)
    (hd : HasFDerivAt f (0 : E →L[ℝ] ℝ) x) {y : E} (hy : y ∈ s) :
    f y = f x ↔ y = x := by
  have hmin := convex_isMinOn_of_hasFDerivAt_zero hf.convexOn hx hd
  constructor
  · intro heq
    have hymin : IsMinOn f s y := by
      intro z hz
      change f y ≤ f z
      rw [heq]
      exact hmin hz
    exact hf.eq_of_isMinOn hymin hmin hy hx
  · rintro rfl
    rfl

/-- Strict positivity of second derivatives on nonconstant line segments implies
strict convexity in an arbitrary real normed space. -/
theorem strictConvexOn_of_line_deriv2_pos {s : Set E} {f : E → ℝ}
    (hs : Convex ℝ s) (hf : ContinuousOn f s)
    (hpos : ∀ x ∈ s, ∀ y ∈ s, x ≠ y → ∀ t ∈ Ioo (0 : ℝ) 1,
      0 < deriv (deriv (f ∘ AffineMap.lineMap x y)) t) :
    StrictConvexOn ℝ s f := by
  refine ⟨hs, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hmaps : MapsTo (AffineMap.lineMap x y) (Icc (0 : ℝ) 1) s := by
    intro t ht
    rw [AffineMap.lineMap_apply_module]
    exact hs hx hy (sub_nonneg.mpr ht.2) ht.1 (by ring)
  have hcont : ContinuousOn (f ∘ AffineMap.lineMap x y) (Icc (0 : ℝ) 1) :=
    hf.comp (AffineMap.lineMap x y : ℝ →ᵃ[ℝ] E).differentiable.continuous.continuousOn hmaps
  have hstrict : StrictConvexOn ℝ (Icc (0 : ℝ) 1)
      (f ∘ AffineMap.lineMap x y) := by
    apply strictConvexOn_of_deriv2_pos (convex_Icc _ _) hcont
    intro t ht
    exact hpos x hx y hy hxy t (by simpa using ht)
  have hh := hstrict.2 (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)
    (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (0 : ℝ) ≠ 1)
    ha hb hab
  have ha1 : 1 - b = a := by linarith
  simpa [AffineMap.lineMap_apply_module, ha1] using hh

/-- A positive-definite second Fréchet derivative gives strict convexity on an
open convex domain. The two derivative fields are explicit, so this applies
directly to computed Hessians without rewriting `fderiv`. -/
theorem strictConvexOn_of_positive_hessian {s : Set E} {f : E → ℝ}
    {f' : E → E →L[ℝ] ℝ} {f'' : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hs : Convex ℝ s) (hsopen : IsOpen s)
    (hf : ∀ z ∈ s, HasFDerivAt f (f' z) z)
    (hf' : ∀ z ∈ s, HasFDerivAt f' (f'' z) z)
    (hpos : ∀ z ∈ s, ∀ v : E, v ≠ 0 → 0 < f'' z v v) :
    StrictConvexOn ℝ s f := by
  apply strictConvexOn_of_line_deriv2_pos hs
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
  intro x hx y hy hxy t ht
  have hmaps : MapsTo (AffineMap.lineMap x y) (Icc (0 : ℝ) 1) s := by
    intro u hu
    rw [AffineMap.lineMap_apply_module]
    exact hs hx hy (sub_nonneg.mpr hu.2) hu.1 (by ring)
  have hz : AffineMap.lineMap x y t ∈ s := hmaps ⟨ht.1.le, ht.2.le⟩
  have hnear : ∀ᶠ u in 𝓝 t, AffineMap.lineMap x y u ∈ s :=
    AffineMap.lineMap_continuous.continuousAt.eventually_mem (hsopen.mem_nhds hz)
  have hfirst : deriv (f ∘ AffineMap.lineMap x y) =ᶠ[𝓝 t]
      (fun u => f' (AffineMap.lineMap x y u) (y - x)) := by
    filter_upwards [hnear] with u hu
    exact ((hf _ hu).comp_hasDerivAt u AffineMap.hasDerivAt_lineMap).deriv
  have hsecond : HasDerivAt (fun u : ℝ => f' (AffineMap.lineMap x y u) (y - x))
      (f'' (AffineMap.lineMap x y t) (y - x) (y - x)) t := by
    have hcomp := (hf' _ hz).comp_hasDerivAt t AffineMap.hasDerivAt_lineMap
    simpa using hcomp.clm_apply (hasDerivAt_const t (y - x))
  rw [hfirst.deriv_eq, hsecond.deriv]
  exact hpos _ hz (y - x) (sub_ne_zero.mpr hxy.symm)

/-- A smooth stationary branch in strictly convex state slices defines a smooth
supporting value, and its graph is exactly the contact set. -/
theorem stationary_family_certificate
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} {V : Set E} {n : WithTop ENat}
    {F : P × E → ℝ} {ψ : P → E}
    (hF : ContDiffOn ℝ n F (U ×ˢ V)) (hψ : ContDiffOn ℝ n ψ U)
    (hψV : MapsTo ψ U V)
    (hconv : ∀ p ∈ U, StrictConvexOn ℝ V (fun z => F (p, z)))
    (hstat : ∀ p ∈ U, HasFDerivAt (fun z => F (p, z))
      (0 : E →L[ℝ] ℝ) (ψ p)) :
    ContDiffOn ℝ n (fun p => F (p, ψ p)) U ∧
      ∀ p ∈ U, ∀ z ∈ V,
        F (p, ψ p) ≤ F (p, z) ∧ (F (p, z) = F (p, ψ p) ↔ z = ψ p) := by
  constructor
  · exact hF.comp (contDiffOn_id.prodMk hψ) (fun p hp => ⟨hp, hψV hp⟩)
  · intro p hp z hz
    exact ⟨convex_isMinOn_of_hasFDerivAt_zero (hconv p hp).convexOn
      (hψV hp) (hstat p hp) hz,
      strictConvex_eq_iff_of_hasFDerivAt_zero (hconv p hp) (hψV hp) (hstat p hp) hz⟩

/-- Version of `stationary_family_certificate` using explicit positive Hessians.
This is the analytic supporting-certificate step of the local construction. -/
theorem stationary_family_certificate_of_positive_hessian
    {P : Type uP} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} {V : Set E} {n : WithTop ENat}
    {F : P × E → ℝ} {ψ : P → E}
    {D : P → E → E →L[ℝ] ℝ} {H : P → E → E →L[ℝ] E →L[ℝ] ℝ}
    (hF : ContDiffOn ℝ n F (U ×ˢ V)) (hψ : ContDiffOn ℝ n ψ U)
    (hψV : MapsTo ψ U V) (hV : Convex ℝ V) (hVopen : IsOpen V)
    (hD : ∀ p ∈ U, ∀ z ∈ V, HasFDerivAt (fun z => F (p, z)) (D p z) z)
    (hH : ∀ p ∈ U, ∀ z ∈ V, HasFDerivAt (D p) (H p z) z)
    (hpos : ∀ p ∈ U, ∀ z ∈ V, ∀ v : E, v ≠ 0 → 0 < H p z v v)
    (hstat : ∀ p ∈ U, D p (ψ p) = 0) :
    ContDiffOn ℝ n (fun p => F (p, ψ p)) U ∧
      ∀ p ∈ U, ∀ z ∈ V,
        F (p, ψ p) ≤ F (p, z) ∧ (F (p, z) = F (p, ψ p) ↔ z = ψ p) := by
  apply stationary_family_certificate hF hψ hψV
  · intro p hp
    exact strictConvexOn_of_positive_hessian hV hVopen (hD p hp) (hH p hp) (hpos p hp)
  · intro p hp
    simpa [hstat p hp] using hD p hp (ψ p) (hψV hp)

end Problem356

end

end OAI
