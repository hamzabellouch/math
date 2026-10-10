import Mathlib
import OAI.AlgebraicGeometry.Seshadri.Jets.QuadraticJets
import OAI.AlgebraicGeometry.Seshadri.Jets.CenteredJetChart

namespace OAI

section
noncomputable section
                                             
section

namespace MaximalSeshadri.Projective
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open MaximalSeshadri.Frames MaximalSeshadri.Geometry MaximalSeshadri.ProjectiveBertini
open MaximalSeshadri.AlgebraicJets MaximalSeshadri.QuadraticJets
attribute [local instance] MvPolynomial.gradedAlgebra

variable {K σ : Type} [Field K] [IsAlgClosed K] [Fintype σ] {X : Scheme} {M : X.Modules}

theorem exists_centered_rational_jet [IsIntegral X]
    (g : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 2 g]
    (k : K →+* Γ(X, ⊤)) (s : Option σ → (O X ⟶ M))
    (hs : (⨆ i, SectionOpens.isoOpen (s i)) = ⊤)
    [IsClosedImmersion (sectionsMorphism k s hs)]
    (hbase : sectionsMorphism k s hs ≫ projectiveToSpec = g)
    (p : X) (hp : p ∉ centeredOpen s) :
    ∃ U : X.affineOpens, p ∈ U.1 ∧
      ∃ hU : U.1 ≤ SectionOpens.isoOpen (s none),
        let _ : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
        ∃ i : Fin 2 → σ, ∃ ρ : Γ(X, U.1) →ₐ[K] K,
          ∃ τ : Γ(X, U.1) →ₐ[K] JetAlgebra (Fin 2) K 3,
            (∀ j : σ, ρ (affineSectionRatios s U hU (some j)) = 0) ∧
            RingHom.ker τ = (RingHom.ker ρ)^3 ∧
            (∀ f, jetAugment 3 (by decide) (τ f) = ρ f) ∧
            (∀ j : Fin 2, τ (affineSectionRatios s U hU (some (i j))) =
              -Ideal.Quotient.mk _ (MvPolynomial.X j)) ∧
            (MvPolynomial.eval₂Hom (openScalars g U.1)
              (fun j => -affineSectionRatios s U hU (some (i j)))).Etale ∧
            ∀ c : K, U.1.topIso.hom (U.1.ι.appTop (k c)) = openScalars g U.1 c := by
  obtain ⟨U, hpU, hU, i, hi, hb, hk⟩ := exists_centered_etale_ratios g k s hs hbase p hp
  let : Algebra K Γ(X, U.1) := (openScalars g U.1).toAlgebra
  let a : Option σ → Γ(X, U.1) := affineSectionRatios s U hU
  let : Algebra (MvPolynomial (Fin 2) K) Γ(X, U.1) :=
    (eval₂Hom (openScalars g U.1) (fun j => -a (some (i j)))).toAlgebra
  let : IsScalarTower K (MvPolynomial (Fin 2) K) Γ(X, U.1) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext c
      exact (eval₂Hom_C (openScalars g U.1) _ c).symm)
  let : Algebra.Etale (MvPolynomial (Fin 2) K) Γ(X, U.1) := hi
  let : Algebra.FiniteType K Γ(X, U.1) := Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType K (MvPolynomial (Fin 2) K))
    (inferInstance : Algebra.FiniteType (MvPolynomial (Fin 2) K) Γ(X, U.1))
  let x : PrimeSpectrum Γ(X, U.1) := U.2.isoSpec.hom ⟨p, hpU⟩
  let : x.asIdeal.IsPrime := x.isPrime
  have hpx : U.2.fromSpec x = p := by
    change (U.2.isoSpec.hom ≫ U.2.fromSpec) ⟨p, hpU⟩ = p
    rw [U.2.isoSpec_hom_fromSpec]
    rfl
  have ham (j : σ) : a (some j) ∈ x.asIdeal := by
    by_contra h
    have hx : x ∈ PrimeSpectrum.basicOpen (a (some j)) := h
    rw [← U.2.fromSpec_preimage_basicOpen] at hx
    change U.2.fromSpec x ∈ X.basicOpen (a (some j)) at hx
    rw [hpx] at hx
    exact hp (hb j hx)
  obtain ⟨ρ₀⟩ := exists_point_finite_type (K := K) (R := Γ(X, U.1) ⧸ x.asIdeal)
  let ρ : Γ(X, U.1) →ₐ[K] K := ρ₀.comp (Ideal.Quotient.mkₐ K x.asIdeal)
  have ha (j : σ) : ρ (a (some j)) = 0 := by
    change ρ₀ (Ideal.Quotient.mk _ (a (some j))) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (ham j), map_zero]
  obtain ⟨τ, hτ, haug, hc⟩ :=
    exists_quadratic_jet_of_etale (K := K) (A := Γ(X, U.1)) a ρ ha i hi
  exact ⟨U, hpU, hU, i, ρ, τ, ha, hτ, haug, hc, hi, hk⟩

end
end MaximalSeshadri.Projective
end


end
end

end OAI
