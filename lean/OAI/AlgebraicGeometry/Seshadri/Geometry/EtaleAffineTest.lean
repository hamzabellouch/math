import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Interpolation.GermInterpolation
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionGermSystem
import OAI.AlgebraicGeometry.Seshadri.Jets.UniformAnalyticAlgebra
import OAI.AlgebraicGeometry.Seshadri.Interpolation.EtaleQuadrilateral

namespace OAI


                                         
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AnalyticCoordinates MaximalSeshadri.AlgebraicJets
open MaximalSeshadri.ActualInterpolation MaximalSeshadri.LocalComparison

theorem Surface.eventual_etale_affine_section_test (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) :
    ∃ U : S.scheme.affineOpens, ∃ eL : L.sheaf.restrict U.1.ι ≅ O U.1.toScheme,
      ∃ t : Fin 2 → Γ(S.scheme,U.1),
      (MvPolynomial.eval₂Hom (openScalars S.structureMap U.1) t).Etale ∧
      letI : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
      ∃ r₀ : ℕ, 0 < r₀ ∧ ∀ r : ℕ, r₀ ≤ r → ∀ k m : ℕ,
        0 < k → 0 < m → (k:ℝ)*Real.sqrt ((selfIntersection S L:ℝ)/r) < (m:ℝ) →
        ∃ p : Fin r → (Γ(S.scheme,U.1) →ₐ[ℂ] ℂ), Function.Injective p ∧
          ∀ s : O S.scheme ⟶ (L.pow k).sheaf,
            (∀ i, affineCoefficient U (localPowerFrame U.1 eL k) s ∈
              (RingHom.ker (p i))^m) → s = 0 := by
  classical
  obtain ⟨d,hd,y,U,hyU,eL,t,het,q,hq0,hq,hjets,htinj,⟨V,hV,hV0,hqinj⟩,hbound⟩ :=
    S.exists_all_section_quadrilateral_etale L hL
  let : Nonempty U.1 := ⟨⟨y,hyU⟩⟩
  let : Algebra ℂ Γ(S.scheme,U.1) := (openScalars S.structureMap U.1).toAlgebra
  have hft : (openScalars S.structureMap U.1).FiniteType := by
    exact (S.structureMap.finiteType_appLE (isAffineOpen_top _) U.2 (by simp)).comp
      (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv).surjective)
  let : Algebra.FiniteType ℂ Γ(S.scheme,U.1) := (RingHom.finiteType_algebraMap.mp hft)
  obtain ⟨W,hW,hW0,hqat⟩ := exists_uniform_analytic_neighborhood q hq
  let : ∀ k : ℕ, Module ℂ (GlobalSections S.scheme (modulePow S.scheme L.sheaf k)) :=
    fun k => complexSectionModule S.structureMap (L.pow k).sheaf
  let coord (k : ℕ) := affineCoefficientLinear S.structureMap U (localPowerFrame U.1 eL k)
  let C (k : ℕ) := germCoefficients (coord k) q hq
  have hci (k : ℕ) : Function.Injective (C k) :=
    germCoefficients_injective_of_taylor (coord k) q hq
      (affineCoefficientLinear_injective S.structureMap (L.pow k) U _) htinj
  let F (k : ℕ) := LinearMap.range (C k)
  let : ∀ k : ℕ, FiniteDimensional ℂ (F k) := fun k =>
    @Module.Finite.range ℂ _ _ _ _ (complexSectionModule S.structureMap (L.pow k).sheaf)
      _ _ (S.sections_finite L hL (L.pow k)) (C k)
  have hconv : ∀ k c, c ∈ F k → ConvergentSeries c := by
    rintro k c ⟨s,rfl⟩
    exact (analyticCoefficients_spec (analyticPullback q hq (coord k s))).1
  have hH : 0 < (selfIntersection S L:ℝ) := by exact_mod_cast S.selfIntersection_pos L hL
  obtain ⟨T,hT,hweight⟩ := Interpolation.exists_node_weight_range (d:ℝ)
    (selfIntersection S L:ℝ) (by exact_mod_cast hd) hH
  have hbound' : ∀ k, 0 < k → ∀ t, T < t → ∀ e ∈ Interpolation.initialExponentSet (F k) t,
      ((e.1:ℝ),(e.2:ℝ)) ∈ Interpolation.nodeQuadrilateral
        ((k:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)*t/(1+t)))
        ((k:ℝ)*((d:ℝ)*(selfIntersection S L:ℝ)/(1+t))) ((k:ℝ)/d) := by
    intro k hk t ht e he
    obtain ⟨c,⟨s,hs⟩,hc⟩ := he
    have heq := germCoefficients_eq_bivariate (coord k) q hq s
    have hsne : s ≠ 0 := by
      intro hs0
      have hc0 : c = 0 := by rw [← hs,hs0,map_zero]
      exact hc.1 (by rw [hc0]; rfl)
    have HH := hbound k hk s hsne (localPowerFrame U.1 eL k) t (by linarith) e
    apply HH
    change LexInitial (NodalLocal.bivariateCoeff
      (bivariateTaylor q hq (coord k s))) t e
    rw [← heq,hs]
    exact hc
  obtain ⟨r₀,hr₀,htest⟩ := Interpolation.eventual_germ_jet_test (d:ℝ)
    (selfIntersection S L:ℝ) T (by exact_mod_cast hd) hH hT hweight F hconv hbound'
  refine ⟨U,eL,t,het,r₀,hr₀,?_⟩
  intro r hr k m hk hm hkm
  obtain ⟨R,hR,hs,ht⟩ := htest r hr k m hk hm hkm
  obtain ⟨p,hp,-,hzero⟩ := idealPower_test_of_series_test (coord k) q hq (hci k)
    (V ∩ W) (hV.inter hW) ⟨hV0,hW0⟩ (hqinj.mono Set.inter_subset_left)
    (fun z hz => hqat z hz.2) r m R hR hs ht
  exact ⟨p,hp,hzero⟩
end
end MaximalSeshadri.Geometry

end

end OAI
