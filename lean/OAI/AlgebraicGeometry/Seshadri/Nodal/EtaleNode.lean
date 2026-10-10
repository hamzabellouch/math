import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Geometry.EtaleRealization
import OAI.AlgebraicGeometry.Seshadri.Jets.AnalyticNode
import OAI.AlgebraicGeometry.Seshadri.Nodal.QuadraticDiscriminant

namespace OAI

section
noncomputable section
                                   
section

namespace MaximalSeshadri.QuadraticJets
noncomputable section
open MvPolynomial MaximalSeshadri.AlgebraicJets MaximalSeshadri.AnalyticNode
open scoped Topology ContDiff

variable {A : Type} [CommRing A] [Algebra ℂ A]
  [Algebra (MvPolynomial (Fin 2) ℂ) A] [IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) A]
  [Algebra.Etale (MvPolynomial (Fin 2) ℂ) A]

theorem etale_ordinary_node_realization
    (ρ : A →ₐ[ℂ] ℂ)
    (hρ : ∀ i : Fin 2, ρ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) = 0)
    (τ : A →ₐ[ℂ] JetAlgebra (Fin 2) ℂ 3)
    (hτ : (RingHom.ker ρ)^3 ≤ RingHom.ker τ)
    (hcoord : ∀ i, τ (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) =
      Ideal.Quotient.mk _ (X i))
    (f : A) (hf : f ∈ (RingHom.ker ρ)^2) (hdisc : discriminant (τ f) ≠ 0) :
    ∃ q : (ℂ × ℂ) → (A →ₐ[ℂ] ℂ), q 0 = ρ ∧
      (∀ s : A, AnalyticAt ℂ (fun z => q z s) 0) ∧
      ∃ u : (ℂ × ℂ) → ℂ, AnalyticAt ℂ u 0 ∧ u 0 ≠ 0 ∧
        (∀ᶠ z in 𝓝 0, q z f = u z*z.1*z.2) ∧
        (∃ e : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ), HasFDerivAt
          (fun z => (q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 1)),
            q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X 0))))
          (e : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ)) 0) ∧
        ∃ V : Set (ℂ × ℂ), IsOpen V ∧ 0 ∈ V ∧ Set.InjOn q V := by
  let x := algebraMap (MvPolynomial (Fin 2) ℂ) A (X 0)
  let y := algebraMap (MvPolynomial (Fin 2) ℂ) A (X 1)
  obtain ⟨d,a,b,c,hd,hdf⟩ := etale_quadratic_neighborhood ρ hρ f hf
  have hΔ : (ρ b)^2-4*ρ a*ρ c ≠ 0 :=
    quadratic_coefficients_nondegenerate ρ τ hτ x y f d a b c
      (hρ 0) (hρ 1) (hcoord 0) (hcoord 1) hf hd hdf hdisc
  obtain ⟨q,hq₀,hq,hqc⟩ := exists_etale_analytic_chart ρ hρ
  have hΔ' : (q 0 b)^2-4*q 0 c*q 0 a ≠ 0 := by
    rw [hq₀]
    convert hΔ using 1
    ring
  obtain ⟨ψ,u,hψ₀,hψ,hu,hu₀,heq,⟨e,he⟩,V,hV,hV₀,hinj⟩ :=
    analytic_node_normal_form (fun z => q z c) (fun z => q z b) (fun z => q z a)
      (hq c) (hq b) (hq a) hΔ'
  have hqd : AnalyticAt ℂ (fun z => q (ψ z) d) 0 := (hq d).comp_of_eq hψ hψ₀
  have hqd₀ : q (ψ 0) d ≠ 0 := by simpa [hψ₀,hq₀] using hd
  have hqdne : ∀ᶠ z in 𝓝 0, q (ψ z) d ≠ 0 := hqd.continuousAt.eventually_ne hqd₀
  have hqcψ : ∀ᶠ z in 𝓝 0, ∀ i : Fin 2,
      q (ψ z) (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) =
        if i = 0 then (ψ z).2 else (ψ z).1 := by
    have hh : ∀ᶠ z in 𝓝 (ψ 0), ∀ i : Fin 2,
        q z (algebraMap (MvPolynomial (Fin 2) ℂ) A (X i)) =
          if i = 0 then z.2 else z.1 := by simpa only [hψ₀] using hqc
    exact hψ.continuousAt.eventually hh
  have hpair : (fun z => (q (ψ z) y,q (ψ z) x)) =ᶠ[𝓝 0] ψ := by
    filter_upwards [hqcψ] with z hz
    exact Prod.ext (by simpa [y] using hz 1) (by simpa [x] using hz 0)
  obtain ⟨W,hW,hWo,hW₀⟩ := eventually_nhds_iff.mp hpair
  refine ⟨fun z => q (ψ z), by simp [hψ₀,hq₀], ?_,
    (fun z => u z / q (ψ z) d), hu.div hqd hqd₀,
    div_ne_zero hu₀ hqd₀, ?_, ⟨e,he.congr_of_eventuallyEq hpair⟩,
    V ∩ W,hV.inter hWo,⟨hV₀,hW₀⟩,?_⟩
  · intro s
    exact (hq s).comp_of_eq hψ hψ₀
  · filter_upwards [hqcψ,heq,hqdne] with z hz hze hdne
    have h := congrArg (q (ψ z)) hdf
    simp only [map_mul,map_add,map_pow] at h
    change q (ψ z) d * q (ψ z) f =
      q (ψ z) a*(q (ψ z) x)^2 + q (ψ z) b*q (ψ z) x*q (ψ z) y +
        q (ψ z) c*(q (ψ z) y)^2 at h
    rw [show q (ψ z) x = (ψ z).2 by simpa [x] using hz 0,
      show q (ψ z) y = (ψ z).1 by simpa [y] using hz 1] at h
    field_simp [hdne]
    linear_combination h + hze
  · intro z hz w hw heqw
    apply hinj hz.1 hw.1
    rw [← hW z hz.2, ← hW w hw.2]
    exact congrArg (fun r : A →ₐ[ℂ] ℂ => (r y,r x)) heqw
end
end MaximalSeshadri.QuadraticJets
end


end
end

end OAI
