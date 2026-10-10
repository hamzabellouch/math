import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Nodal.NodalBranch

namespace OAI

section
noncomputable section
                                         
section

namespace MaximalSeshadri.NodalLocal
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace

theorem formal_branch_dimension_eq_one {K R : Type*} [Field K] [CommRing R] [IsDomain R]
    (hd : ringKrullDim R ≤ 2) (g : R) (hg : g ≠ 0)
    [hgp : (Ideal.span {g}).IsPrime]
    (φ : R →+* PowerSeries K) (hφg : φ g = 0)
    (hbranch : ∃ a : R, PowerSeries.constantCoeff (φ a) = 0 ∧ φ a ≠ 0) :
    ringKrullDim (R ⧸ Ideal.span {g}) = 1 := by
  apply le_antisymm (principal_curve_dimension_le_one hd g hg)
  have hI : Ideal.span {g} ≤ RingHom.ker φ := (Ideal.span_singleton_le_iff_mem _).mpr hφg
  let ψ := Ideal.Quotient.lift (Ideal.span {g}) φ hI
  let m := RingHom.ker (PowerSeries.constantCoeff.comp ψ)
  have hm : m ≠ ⊥ := by
    obtain ⟨a, ha, han⟩ := hbranch
    intro he
    have ha' : Ideal.Quotient.mk (Ideal.span {g}) a ∈ m := ha
    rw [he, Ideal.mem_bot] at ha'
    have : φ a = 0 := by
      change ψ (Ideal.Quotient.mk (Ideal.span {g}) a) = 0
      rw [ha', map_zero]
    exact han this
  apply Order.one_le_krullDim_iff.mpr
  refine ⟨⟨⊥, Ideal.isPrime_bot⟩, ⟨m, RingHom.ker_isPrime _⟩, ?_⟩
  change (⊥ : Ideal (R ⧸ Ideal.span {g})) < m
  exact bot_lt_iff_ne_bot.mpr hm

open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.FormalCoordinates
open scoped Topology

lemma nodal_principal_dimension_eq_one {R : Type*} [CommRing R] [Algebra ℂ R]
    [IsDomain R] (hd : ringKrullDim R ≤ 2)
    (q : (ℂ × ℂ) → (R →ₐ[ℂ] ℂ)) (hq : ∀ a, AnalyticAt ℂ (fun z => q z a) 0)
    (hs : Function.Surjective ((Ideal.Quotient.mk
      (IsLocalRing.maximalIdeal (MvPowerSeries (Fin 2) ℂ)^2)).comp
      (analyticTaylor q hq).toRingHom))
    (g : R) (hg0 : g ≠ 0) [hgp : (Ideal.span {g}).IsPrime]
    (u : (ℂ × ℂ) → ℂ) (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hg : ∀ᶠ z in 𝓝 0, q z g = u z*z.1*z.2) :
    ringKrullDim (R ⧸ Ideal.span {g}) = 1 := by
  obtain ⟨U,hU,hgU⟩ := bivariateTaylor_node q hq g u hu hu0 hg
  have hw := (bivariate_branch_witnesses (analyticTaylor q hq) hs).1
  have he (a : R) : (binaryEquiv ℂ) (analyticTaylor q hq a) = bivariateTaylor q hq a := by
    rw [bivariateTaylor_eq]; rfl
  simp only [he] at hw
  apply formal_branch_dimension_eq_one hd g hg0
    ((restrictX ℂ).comp (bivariateTaylor q hq)).toRingHom _ hw
  change restrictX ℂ (bivariateTaylor q hq g) = 0
  simp [hgU, nodeEquation]

end
end MaximalSeshadri.NodalLocal

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry TopologicalSpace

lemma subscheme_dimension_ge_affine_chart {X : Scheme}
    (I : X.IdealSheafData) (U : X.affineOpens) :
    ringKrullDim (Γ(X,U.1) ⧸ I.ideal U) ≤ topologicalKrullDim I.subscheme := by
  let := I.subschemeCover.map_prop U
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (I.subschemeCover.f U).isOpenEmbedding.isInducing.topologicalKrullDim_le

end
end MaximalSeshadri.Geometry
end


end
end

end OAI
