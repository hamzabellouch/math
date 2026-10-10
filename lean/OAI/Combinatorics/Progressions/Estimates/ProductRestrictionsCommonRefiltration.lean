import OAI.Combinatorics.Progressions.Estimates.ProductRestrictionWeightedCommonFactors
import OAI.Combinatorics.Progressions.Linear.CommonProjectionFactorizationBudget

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration
open scoped TensorProduct

theorem exists_productRestrictions_common_refiltered_factorization (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {ι α σ J : Type*} [Fintype ι] [Fintype α] [Fintype σ] [Fintype J]
      {κ β : J → Type*} [∀ j, Fintype (κ j)] [∀ j, Fintype (β j)]
      {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : ι → ℕ}
      (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
      (r : ∀ j, κ j → ι), (∀ j, Function.Injective (r j)) →
    ∀ (e : Basis α ℚ (∀ i, L i)) (ω : α → ℕ)
      (hF : ∀ k, (pi D).filtration.layer k = Submodule.span ℚ (e '' {i | k ≤ ω i}))
      (c : ∀ j, Basis (β j) ℚ (∀ k, L (r j k))) (ν : ∀ j, β j → ℕ)
      (hG : ∀ j k, (pi (fun a => D (r j a))).filtration.layer k =
        Submodule.span ℚ (c j '' {i | k ≤ ν j i}))
      (η : ∀ j, (∀ k, L (r j k)) →ₗ[ℚ] ℚ)
      {H : J → ℕ}, (∀ j, 1 ≤ H j) →
      (∀ j a b, RationalHeightLE
        ((c j).repr (liePiMap (fun k => liePiEval (R := ℚ) (r j k)) (e b)) a) (H j)) →
    ∀ {p : ℝ}, 0 ≤ p → (Fintype.card α : ℝ) ≤ p →
      (∀ j, (Fintype.card (β j) : ℝ) ≤ p) →
      (Fintype.card σ : ℝ) ≤ p → (Fintype.card J : ℝ) ≤ p →
      (∀ j, (H j : ℝ) ≤ Real.exp p) →
      (∀ a b k, rationalLogHeight (e.repr ⁅e a, e b⁆ k) ≤ p) →
    ∀ (T : σ → ℝ), (∀ i, Real.exp ((p + C) ^ C) ≤ T i) →
    ∀ (g : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : σ => 1)),
      (∀ j, (pi (fun k => D (r j k))).filtration.ControlledSymbolFactorization
        (c j) (ν j) (hG j) (η j) T
        ((pi (fun k => D (r j k))).filtration.realPolynomialSymbolHom
          (c j) (ν j) (hG j) (fun _ => 1)
          ⟨⟨(piRealOrbit (fun k => (D (r j k)).filtration) (fun k => g (r j k))).log,
            (piRealOrbit (fun k => (D (r j k)).filtration) (fun k => g (r j k))).property⟩⟩) p) →
      let F := (pi D).filtration
      let joint : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
        ⟨⟨(piRealOrbit (fun i => (D i).filtration) g).log,
          (piRealOrbit (fun i => (D i).filtration) g).property⟩⟩
      let frequency : J → (∀ i, L i) →ₗ[ℚ] ℚ := fun j =>
        (η j).comp (liePiMap (fun k => liePiEval (R := ℚ) (r j k))).toLinearMap
      ∃ (W : LieSubalgebra ℚ F.AssociatedGraded)
        (v : Fin (Fintype.card α) → F.AssociatedGraded)
        (m : ℕ) (e₀ p₀ r₀ : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
        Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
        BasisGradedSubmodule (F.associatedGradedBasis e ω hF) ω W.toSubmodule ∧
        (∀ i k, rationalLogHeight ((F.associatedGradedBasis e ω hF).repr (v i) k) ≤
          (p + C) ^ C) ∧
        (∀ j x, x ∈ F.realGradedRefiltrationLayer W s → realifyFunctional (frequency j) x = 0) ∧
        0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ e₀ * p₀ * r₀ = joint ∧
        (∀ t : σ → ℝ, eval₂ t (F.realGradedSymbolPolynomial e ω hF (fun _ => 1)
          (F.realPolynomialSymbolHom e ω hF (fun _ => 1) p₀).coord) ∈ realificationLieSubalgebra W) ∧
        (∀ a i, |(e.baseChange ℝ).repr
          (coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) a) i| ≤
            Real.exp ((p + C) ^ C) / monomialScale T a) ∧
        ((fun z : (σ →₀ ℕ) × α => (e.baseChange ℝ).repr
          (coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) z.1) z.2) ∈
          realDenominatorGrid m) ∧
        coefficients (e₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
        coefficients (r₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
        coefficients (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 =
          coefficients (joint.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 ∧
        (coefficients (joint.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 →
          ∀ t : σ → ℝ, eval₂ t (p₀.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) ∈
            realificationLieSubalgebra (F.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨A, hA, hlift⟩ := exists_productRestriction_jointOrbit_controlledSymbolFactorization s
  obtain ⟨B, _, hcommon⟩ := exists_common_refiltered_factorization s
  obtain ⟨C, hC, hbudget⟩ := exists_commonProjectionFactorization_budget A B hA
  refine ⟨C, hC, ?_⟩
  intro ι α σ J _ _ _ _ κ β _ _ L _ _ d D r hr e ω hF c ν hG η H hH hentries
    p hp hα hβ hσ hJ hHp hstructure T hT g hfactor
  obtain ⟨hpq, hq, hcost, hheight⟩ := hbudget p hp
  let F := (pi D).filtration
  let joint : (F.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
    ⟨⟨(piRealOrbit (fun i => (D i).filtration) g).log,
      (piRealOrbit (fun i => (D i).filtration) g).property⟩⟩
  let frequency : J → (∀ i, L i) →ₗ[ℚ] ℚ := fun j =>
    (η j).comp (liePiMap (fun k => liePiEval (R := ℚ) (r j k))).toLinearMap
  have hTpos (i : σ) : 0 < T i := (Real.exp_pos _).trans_le (hT i)
  have hTF (i : σ) : Real.exp (((p + A) ^ A + 2) ^ B) ≤ T i :=
    (Real.exp_le_exp.mpr hcost).trans (hT i)
  have hprojected (j : J) : F.ControlledSymbolFactorization e ω hF (frequency j) T
      (F.realPolynomialSymbolHom e ω hF (fun _ => 1) joint) ((p + A) ^ A) :=
    hlift D (r j) (hr j) e ω hF (c j) (ν j) (hG j) (hH j) (hentries j)
      hp hα (hβ j) hσ (hHp j) T hTpos g (η j) (hfactor j)
  obtain ⟨W, v, m, e₀, p₀, r₀, hv, hW, hvH, hfreq, hm, hmp, hprod,
      hmid, he, hR, he0, hr0, hp0, hanchor⟩ :=
    hcommon F e ω hF frequency ((p + A) ^ A) hq (hα.trans hpq)
      (hσ.trans hpq) (hJ.trans hpq) (fun i j k => (hstructure i j k).trans hpq)
      T hTF joint hprojected
  refine ⟨W, v, m, e₀, p₀, r₀, hv, hW, fun i k => (hvH i k).trans hheight,
    hfreq, hm, hmp.trans (Real.exp_le_exp.mpr hcost), hprod, ?_, ?_,
    hR, he0, hr0, hp0, hanchor⟩
  · with_reducible exact hmid
  · intro a i
    exact (he a i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hcost)
      (monomialScale_pos T hTpos a).le)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
