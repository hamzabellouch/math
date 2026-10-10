import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.LocalQuadratic

namespace OAI

section
noncomputable section
                                       
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section

open MvPolynomial
open scoped Topology ContDiff

variable {A : Type} [CommRing A] [Algebra ℂ A]
  [Algebra (MvPolynomial (Fin 2) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) A]
  [Algebra.Etale (MvPolynomial (Fin 2) ℂ) A]

theorem etale_tangent_separates
    (ρ : A →ₐ[ℂ] ℂ)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) = 0)
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ)) (hq₀ : q 0 = ρ)
    (hq : ∀ s : A, AnalyticAt ℂ (fun z => q z s) 0)
    (v : ℂ × ℂ)
    (hv : ∀ i : Fin 2, fderiv ℂ (fun z => q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i))) 0 v = 0) :
    ∀ s : A, fderiv ℂ (fun z => q z s) 0 v = 0 := by
  intro s
  let x := algebraMap (MvPolynomial (Fin 2) ℂ) A (X 0)
  let y := algebraMap (MvPolynomial (Fin 2) ℂ) A (X 1)
  let f := s - algebraMap ℂ A (ρ s)
  have hf : ρ f = 0 := by simp [f]
  obtain ⟨d,a,b,hd,heq⟩ := etale_linear_neighborhood ρ hρ f hf
  have hfun : (fun z => q z d * (q z s - ρ s)) =
      (fun z => q z a * q z x + q z b * q z y) := by
    funext z
    have h := congrArg (q z) heq
    simpa [f, x, y] using h
  have hD := (hq d).differentiableAt.hasFDerivAt.mul
    ((hq s).differentiableAt.hasFDerivAt.sub_const (ρ s))
  change HasFDerivAt (fun z => q z d * (q z s - ρ s)) _ _ at hD
  rw [hfun] at hD
  have hE := ((hq a).differentiableAt.hasFDerivAt.mul
    (hq x).differentiableAt.hasFDerivAt).add
    ((hq b).differentiableAt.hasFDerivAt.mul (hq y).differentiableAt.hasFDerivAt)
  have hh := congrArg (fun L : (ℂ × ℂ) →L[ℂ] ℂ => L v) (hD.unique hE)
  simp only [hq₀, hρ 0, hρ 1, x, y, sub_self, add_zero,
    add_apply, smul_apply, smul_eq_mul,
    hv 0, hv 1, mul_zero, zero_mul] at hh
  exact (mul_eq_zero.mp hh).resolve_left hd

theorem etale_coordinates_analytic_inverse
    (ρ : A →ₐ[ℂ] ℂ)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) = 0)
    (q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ)) (hq₀ : q 0 = ρ)
    (hq : ∀ s : A, AnalyticAt ℂ (fun z => q z s) 0)
    (u w : A)
    (hu : ∀ᶠ z in 𝓝 0, q z u = ρ u + z.1)
    (hw : ∀ᶠ z in 𝓝 0, q z w = ρ w + z.2) :
    ∃ ψ : (ℂ × ℂ) → (ℂ × ℂ), ψ 0 = 0 ∧ AnalyticAt ℂ ψ 0 ∧
      (∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
        q (ψ z) (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) =
          if i = 0 then z.2 else z.1) ∧
      (∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), HasFDerivAt ψ (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
      ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn ψ V := by
  let F : (ℂ × ℂ) → (ℂ × ℂ) := fun z =>
    (q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 1)),
      q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 0)))
  have hF₀ : F 0 = 0 := by simp [F, hq₀, hρ]
  have hF : AnalyticAt ℂ F 0 := (hq _).prod (hq _)
  have hinj : Function.Injective (fderiv ℂ F 0) := by
    change Function.Injective (fderiv ℂ F 0).toLinearMap
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    have hder := ((hq (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 1))).differentiableAt.hasFDerivAt).prodMk
      ((hq (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 0))).differentiableAt.hasFDerivAt)
    have hder' := hder.fderiv
    change fderiv ℂ F 0 = _ at hder'
    rw [hder'] at hv
    have hc : ∀ i : Fin 2, fderiv ℂ (fun z => q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i))) 0 v = 0 := by
      intro i
      fin_cases i
      · exact congrArg Prod.snd hv
      · exact congrArg Prod.fst hv
    have hs := etale_tangent_separates ρ hρ q hq₀ hq v hc
    have hdu : HasFDerivAt (fun z => q z u) (ContinuousLinearMap.fst ℂ ℂ ℂ) 0 := by
      exact ((ContinuousLinearMap.fst ℂ ℂ ℂ).hasFDerivAt.const_add (ρ u)).congr_of_eventuallyEq hu
    have hdw : HasFDerivAt (fun z => q z w) (ContinuousLinearMap.snd ℂ ℂ ℂ) 0 := by
      exact ((ContinuousLinearMap.snd ℂ ℂ ℂ).hasFDerivAt.const_add (ρ w)).congr_of_eventuallyEq hw
    apply Prod.ext
    · change (ContinuousLinearMap.fst ℂ ℂ ℂ) v = 0
      rw [← hdu.fderiv]
      exact hs u
    · change (ContinuousLinearMap.snd ℂ ℂ ℂ) v = 0
      rw [← hdw.fderiv]
      exact hs w
  have hbij : Function.Bijective (fderiv ℂ F 0) :=
    ⟨hinj, (LinearMap.injective_iff_surjective (f := (fderiv ℂ F 0).toLinearMap)).mp hinj⟩
  let e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
    (LinearEquiv.ofBijective (fderiv ℂ F 0).toLinearMap hbij).toContinuousLinearEquiv
  have hder : HasFDerivAt F (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0 := hF.differentiableAt.hasFDerivAt
  have hcont : ContDiffAt ℂ ω F 0 := hF.contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let T := hcont.toOpenPartialHomeomorph F hder hn
  let ψ := hcont.localInverse hder hn
  have hψ₀ : ψ 0 = 0 := by simpa only [hF₀] using hcont.localInverse_apply_image hder hn
  have hψ : AnalyticAt ℂ ψ 0 := by simpa only [hF₀] using (hcont.to_localInverse hder hn).analyticAt
  have ht : (0 : ℂ × ℂ) ∈ T.target := by
    simpa only [hF₀] using hcont.image_mem_toOpenPartialHomeomorph_target hder hn
  have hright : ∀ᶠ z in 𝓝 0, F (ψ z) = z := by
    filter_upwards [T.open_target.mem_nhds ht] with z hz
    exact T.right_inv hz
  refine ⟨ψ,hψ₀,hψ,?_,⟨e.symm, ?_⟩,T.target,T.open_target,ht,T.symm.injOn⟩
  swap
  · have hderψ : HasFDerivAt F (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) (ψ 0) := by
      simpa only [hψ₀] using hder
    have hc := hderψ.comp (0 : ℂ × ℂ) hψ.differentiableAt.hasFDerivAt
    have hi : HasFDerivAt (fun z => F (ψ z)) (ContinuousLinearMap.id ℂ (ℂ × ℂ)) 0 :=
      (hasFDerivAt_id (0 : ℂ × ℂ)).congr_of_eventuallyEq hright
    have heq := hc.unique hi
    apply hψ.differentiableAt.hasFDerivAt.congr_fderiv
    apply ContinuousLinearMap.ext
    intro v
    apply e.injective
    simpa using DFunLike.congr_fun heq v
  filter_upwards [T.open_target.mem_nhds ht] with z hz
  have heq := T.right_inv hz
  change F (ψ z) = z at heq
  intro i
  fin_cases i
  · simpa [F] using congrArg Prod.snd heq
  · simpa [F] using congrArg Prod.fst heq

end
end MaximalSeshadri.QuadraticJets
end


end
end

end OAI
