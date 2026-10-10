import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Divisors.SectionGermSystem
import OAI.AlgebraicGeometry.Seshadri.Jets.BinaryJetDimension

namespace OAI


                                              
section

namespace MaximalSeshadri.Geometry
noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open MaximalSeshadri.Frames MaximalSeshadri.AlgebraicJets MaximalSeshadri.ProjectiveBertini

lemma Surface.sections_finrank (S : Surface) (M : LineBundle S.scheme) :
    letI := complexSectionModule S.structureMap M.sheaf
    Module.finrank ℂ (GlobalSections S.scheme M.sheaf) =
      cohomologyDimension S.structureMap M.sheaf 0 := by
  let := complexSectionModule S.structureMap M.sheaf
  let := Module.compHom (cohomology M.sheaf 0) (baseScalars S.structureMap)
  let e := Ext.linearEquiv₀ (R := Γ(S.scheme,⊤)) (X := structureSheaf S.scheme) (Y := M.sheaf)
  let e' : cohomology M.sheaf 0 ≃ₗ[ℂ] GlobalSections S.scheme M.sheaf :=
    { e.toAddEquiv with map_smul' := fun r x => e.map_smul (baseScalars S.structureMap r) x }
  exact e'.finrank_eq.symm

lemma finite_affine_jet_test {A : Type} [CommRing A] [Algebra ℂ A]
    (t : Fin 2 → A) (het : (MvPolynomial.aeval (R := ℂ) t).toRingHom.Etale)
    (ρ : A →ₐ[ℂ] ℂ) (n : ℕ) :
    ∃ J : A →ₗ[ℂ] (JetIndex (Fin 2) n → ℂ),
      ∀ a, J a = 0 ↔ a ∈ (RingHom.ker ρ)^n := by
  classical
  by_cases hn : n = 0
  · subst n
    refine ⟨0,fun a => ?_⟩
    simp
  let φ := MvPolynomial.aeval (R := ℂ) t
  let := φ.toAlgebra
  let : IsScalarTower ℂ (MvPolynomial (Fin 2) ℂ) A :=
    IsScalarTower.of_algebraMap_eq fun c => (φ.commutes c).symm
  let : Algebra.Etale (MvPolynomial (Fin 2) ℂ) A := RingHom.etale_algebraMap.mp het
  obtain ⟨D,hD⟩ := exists_regular_jet_coeffs (σ := Fin 2) (F := ℂ) (S := A) n (Nat.pos_of_ne_zero hn)
  let J : A →ₗ[ℂ] (JetIndex (Fin 2) n → ℂ) :=
    LinearMap.pi fun d => ρ.toLinearMap.comp ((LinearMap.proj d).comp D)
  refine ⟨J,fun a => ?_⟩
  rw [hD ρ a,funext_iff]
  rfl

theorem Surface.exists_section_with_point_orders (S : Surface)
    (L : LineBundle S.scheme) (hL : L.IsAmple) (M : LineBundle S.scheme)
    {r : ℕ} (U : Fin r → S.scheme.affineOpens)
    (e : ∀ i, M.sheaf.restrict (U i).1.ι ≅ O (U i).1.toScheme)
    (t : ∀ i, Fin 2 → Γ(S.scheme,(U i).1))
    (het : ∀ i, (MvPolynomial.eval₂Hom (openScalars S.structureMap (U i).1) (t i)).Etale)
    (ρ : ∀ i, letI := (openScalars S.structureMap (U i).1).toAlgebra;
      Γ(S.scheme,(U i).1) →ₐ[ℂ] ℂ) (n : Fin r → ℕ)
    (hd : ∑ i, n i*(n i+1) < 2*cohomologyDimension S.structureMap M.sheaf 0) :
    ∃ s : O S.scheme ⟶ M.sheaf, s ≠ 0 ∧
      ∀ i, affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^(n i) := by
  classical
  let := complexSectionModule S.structureMap M.sheaf
  let := S.sections_finite L hL M
  let (i : Fin r) : Algebra ℂ Γ(S.scheme,(U i).1) := (openScalars S.structureMap (U i).1).toAlgebra
  choose J hJ using fun i => finite_affine_jet_test (t i) (het i) (ρ i) (n i)
  let T : GlobalSections S.scheme M.sheaf →ₗ[ℂ] ((i : Fin r) → JetIndex (Fin 2) (n i) → ℂ) :=
    LinearMap.pi fun i => (J i).comp (affineCoefficientLinear S.structureMap (U i) (e i))
  have hT (s : GlobalSections S.scheme M.sheaf) : T s = 0 ↔
      ∀ i, affineCoefficient (U i) (e i) s ∈ (RingHom.ker (ρ i))^(n i) := by
    rw [funext_iff]
    exact forall_congr' fun i => hJ i _
  have hdim : 2 * Module.finrank ℂ ((i : Fin r) → JetIndex (Fin 2) (n i) → ℂ) =
      ∑ i, n i*(n i+1) := by
    let (i : Fin r) : Fintype (JetIndex (Fin 2) (n i)) := Fintype.ofFinite _
    rw [Module.finrank_pi_fintype,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Module.finrank_pi]
    simpa only [Nat.card_eq_fintype_card,Finset.card_univ] using card_binaryJet (n i)
  by_contra hnon
  have hinj : Function.Injective T := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro s hs
    by_contra hn
    exact hnon ⟨s,hn,(hT s).mp hs⟩
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  rw [S.sections_finrank M] at hle
  omega

end
end MaximalSeshadri.Geometry

end


end OAI
