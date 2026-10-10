import OAI.Combinatorics.Progressions.Nilpotent.SimultaneousNiltestFactorization

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_anchored_product_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧
    ∀ {J σ : Type*} [Fintype J] [Fintype σ] [DecidableEq σ] {L : (Bool ⊕ (J × Bool)) → Type*}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Bool ⊕ (J × Bool)) → ℕ}
  [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
  [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
  [TopologicalSpace (ℝ ⊗[ℚ] (∀ i, L i))] [IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, L i))]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] (∀ i, L i))] [T2Space (ℝ ⊗[ℚ] (∀ i, L i))]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (P : (D (.inl true)).Niltest (fun _ : σ => 1)) (P₀ : (D (.inl false)).Niltest (fun _ : σ => 1))
    (U : J → (D (.inl true)).Niltest (fun _ : σ => 1)) (V : J → (D (.inl false)).Niltest (fun _ : σ => 1))
    (A : ∀ j, (D (.inr (j, true))).Niltest (fun _ : σ => 1)) (B : ∀ j, (D (.inr (j, false))).Niltest (fun _ : σ => 1))
    (eta : J → L (.inl true) →ₗ[ℚ] ℚ) (theta : J → L (.inl false) →ₗ[ℚ] ℚ)
    (alpha : ∀ j, L (.inr (j, true)) →ₗ[ℚ] ℚ) (beta : ∀ j, L (.inr (j, false)) →ₗ[ℚ] ℚ)
    {p : ℝ} (_hp : 2 ≤ p) (_hcard : (Fintype.card (Bool ⊕ (J × Bool)) : ℝ) ≤ p)
    (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hD : ∀ i, (D i).GeometryComplexityLE p)
    (_hU : ∀ j, (U j).ComplexityLE p ∧ (U j).orbit = P.orbit ∧ (U j).normBound ≤ 1)
    (_hV : ∀ j, (V j).ComplexityLE p ∧ (V j).orbit = P₀.orbit ∧ (V j).normBound ≤ 1)
    (_hA : ∀ j, (A j).ComplexityLE p ∧ (A j).normBound ≤ 1)
    (_hB : ∀ j, (B j).ComplexityLE p ∧ (B j).normBound ≤ 1)
    (_heta : ∀ j k, rationalLogHeight (eta j ((D (.inl true)).basis k)) ≤ p)
    (_htheta : ∀ j k, rationalLogHeight (theta j ((D (.inl false)).basis k)) ≤ p)
    (_halpha : ∀ j k, rationalLogHeight (alpha j ((D (.inr (j, true))).basis k)) ≤ p)
    (_hbeta : ∀ j k, rationalLogHeight (beta j ((D (.inr (j, false))).basis k)) ≤ p)
    (_hvertU : ∀ j z, z ∈ (D (.inl true)).filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (_hvertV : ∀ j z, z ∈ (D (.inl false)).filtration.realification.subgroup s → ∀ x,
      (V j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (theta j) z.coord : ℝ) : CircleFourier.Circle) * (V j).observable x)
    (_hvertA : ∀ j z, z ∈ (D (.inr (j, true))).filtration.realification.subgroup s → ∀ x,
      (A j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (alpha j) z.coord : ℝ) : CircleFourier.Circle) * (A j).observable x)
    (_hvertB : ∀ j z, z ∈ (D (.inr (j, false))).filtration.realification.subgroup s → ∀ x,
      (B j).observable (z • x) = CircleFourier.character
        ((realifyFunctional (beta j) z.coord : ℝ) : CircleFourier.Circle) * (B j).observable x)
    (weight : ∀ i, Fin (d i) → ℕ)
    (hFlayers : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ ((D i).basis '' {k | j ≤ weight i k}))
    (origin : J → σ → ℤ) (lengths : J → σ → ℕ) (_hlengths : ∀ j i, 0 < lengths j i)
    (_hbias : ∀ j, Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j),
      (U j).eval x * star ((V j).eval x) * (A j).eval x * (B j).eval x‖)
    (side : σ → ℝ) (_hside : ∀ i, Real.exp ((p + C) ^ C) ≤ side i)
    (_hrelative : ∀ j i, Real.exp (-p) * side i ≤ lengths j i),
    let omega := productBasisWeight weight
    let hTotal := pi_layer_span D weight hFlayers
    let orbit := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration)
      (fun i => (anchoredReferenceData P P₀ A B i).orbit)
    let g : ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
      ⟨⟨orbit.log, orbit.property⟩⟩
    let freq := fun j => piFrequency
      (selectedOrbitFrequencies (anchoredFrequencyData eta theta alpha beta j) (anchoredInputs j))
    ∃ (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded)
      (v : Fin (Fintype.card (Σ i, Fin (d i))) → (pi D).filtration.AssociatedGraded)
      (m : ℕ) (κ : (pi D).RealGroup)
      (E b R : ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group),
      Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
      BasisGradedSubmodule ((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal) omega W.toSubmodule ∧
      (∀ i k, rationalLogHeight (((pi D).filtration.associatedGradedBasis (pi D).basis omega hTotal).repr (v i) k) ≤
        (p + C) ^ C) ∧
      (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W s → realifyFunctional (freq j) x = 0) ∧
      0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ κ ∈ (pi D).realLattice ∧
      E * b * R * (pi D).filtration.realification.adaptedConstantGroupHom (fun _ => 1) κ = g ∧
      (∀ α i, |((pi D).basis.baseChange ℝ).repr
        (coefficients (E.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α) i| ≤
          Real.exp ((p + C) ^ C) / monomialScale side α) ∧
      ((fun z : (σ →₀ ℕ) × Fin (Fintype.card (Σ i, Fin (d i))) => ((pi D).basis.baseChange ℝ).repr
        (coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) z.1) z.2) ∈ realDenominatorGrid m) ∧
      coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      coefficients (R.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 ∧
      (∀ α, coefficients (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
        (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ => 1) α)) ∧
      (∀ t : σ → ℝ, eval₂ t (b.coord : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] (∀ i, L i))) ∈
        realificationLieSubalgebra ((pi D).filtration.gradedRefiltrationSubalgebra W)) := by
  obtain ⟨c, _, hfactor⟩ := exists_lattice_normalized_niltest_factorization s hs
  let X : Polynomial ℕ := Polynomial.X
  let Q := (X + 2) ^ 2 + X + (X + (X ^ 2 + X + 3) ^ 2) + X ^ 2 + 4
  let F := Q + (Q + Polynomial.C c) ^ c
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget F
  refine ⟨C, hC, ?_⟩
  intro J σ _ _ _ L _ _ d _ _ _ _ _ _ _ _ D P P₀ U V A B eta theta alpha beta p
    hp hcard hσ hD hU hV hA hB heta htheta halpha hbeta hvertU hvertV hvertA hvertB
    weight hFlayers origin lengths hlengths hbias side hside hrelative
  have hp0 : 0 ≤ p := by linarith
  let q := productNiltestBudget p
  have hpq : p ≤ q := by
    exact (by nlinarith [sq_nonneg p] : p ≤ (p + 2) ^ 2).trans (productNiltestBudget_geometry hp0)
  have hq : 0 ≤ q := hp0.trans hpq
  have hbudget' : q + (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [F, Q, X, q, productNiltestBudget, productObservableLipBudget, Polynomial.eval₂_pow] using hbudget p hp0
  have hcC : (q + c) ^ c ≤ (p + C) ^ C := by linarith
  have hJ : (Fintype.card J : ℝ) ≤ p := by
    have h := hcard
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_bool, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at h
    linarith [Nat.cast_nonneg (α := ℝ) (Fintype.card J)]
  have hsidepos : ∀ i, 0 < side i := fun i => (Real.exp_pos _).trans_le (hside i)
  obtain ⟨S0, S, hS0, hS0c, hS⟩ := exists_anchored_product_family D P P₀ U V A B eta theta alpha beta
    hp hcard hD hU hV hA hB heta htheta halpha hbeta hvertU hvertV hvertA hvertB
  let omega := productBasisWeight weight
  let hTotal := pi_layer_span D weight hFlayers
  let freq := fun j => piFrequency
    (selectedOrbitFrequencies (anchoredFrequencyData eta theta alpha beta j) (anchoredInputs j))
  have hcorr : ∀ j, Real.exp (-q) ≤ ‖𝔼 x ∈ translatedIntegerBox (origin j) (lengths j), (S j).eval x‖ := by
    intro j
    apply (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans
    simpa only [(hS j).2.2.2.1] using hbias j
  have hrel : ∀ j i, Real.exp (-q) * side i ≤ lengths j i := fun j i =>
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hpq)) (hsidepos i).le).trans (hrelative j i)
  obtain ⟨W, v, m, κ, E, b, R, hv, hW, hheight, hfreq, hm, hmp, hκ, hebr,
      hE, hR, hb0, hR0, hcoeff, hvalues⟩ :=
    hfactor (pi D) omega hTotal S0 S (fun j => (hS j).1) freq q hq hS0c.1
      (by exact (show (Fintype.card σ : ℝ) ≤ p from hσ).trans hpq)
      (hJ.trans hpq) (fun j => (hS j).2.2.1)
      (fun j k => ((hS j).2.2.2.2.1 k).trans hpq) (fun j => (hS j).2.2.2.2.2)
      origin lengths hlengths hcorr side (fun i => (Real.exp_le_exp.mpr hcC).trans (hside i)) hrel
  let orbit := NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration)
    (fun i => (anchoredReferenceData P P₀ A B i).orbit)
  let g : ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group :=
    ⟨⟨orbit.log, orbit.property⟩⟩
  have hg : (⟨⟨S0.orbit.log, S0.orbit.property⟩⟩ :
      ((pi D).filtration.realification.adaptedPolynomialFiltration (fun _ : σ => 1)).Group) = g := by
    apply NilpotentLieBCHGroup.ext
    apply Subtype.ext
    exact congrArg (fun o : (pi D).filtration.realification.PolynomialOrbit (fun _ : σ => 1) => o.log) hS0
  refine ⟨W, v, m, κ, E, b, R, hv, hW, (fun i k => (hheight i k).trans hcC), hfreq, hm,
    hmp.trans (Real.exp_le_exp.mpr hcC), hκ, hebr.trans hg, ?_, hR, hb0, hR0, hcoeff, hvalues⟩
  intro α i
  exact (hE α i).trans (div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hcC)
    (monomialScale_pos side hsidepos α).le)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
