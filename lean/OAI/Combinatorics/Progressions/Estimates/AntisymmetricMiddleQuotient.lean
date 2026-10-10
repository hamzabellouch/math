import OAI.Combinatorics.Progressions.Estimates.AdaptedDiagramNativeExternalNet

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold NilpotentLieBCHGroup VectorPolynomial

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra

structure NativeAntisymmetricMiddleQuotient {p : ℝ}
    {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {N : ℕ}
    (V : NativeAntisymmetricOrbitFactors W N p) (q : ℝ) where
  model : RationalFilteredNilmanifold
    ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra)
    2 (finrank ℚ ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra))
  filtration : model.filtration =
    (pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltration V.subalgebra
  lattice : model.lattice = (pi (fun _ : Fin 8 => W.model)).lattice.comap
    (NilpotentLieBCHGroup.map
      (hnil := ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltration
        V.subalgebra).lowerCentralSeries_eq_bot)
      ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra).incl)
  complexity : model.GeometryComplexityLE q
  inclusion_height : ∀ i j, rationalLogHeight
    ((pi (fun _ : Fin 8 => W.model)).basis.repr (model.basis i : Fin 8 → W.L) j) ≤ q
  orbit : model.filtration.realification.PolynomialOrbit (fun _ : Fin 4 => 1)
  inclusion : ∀ x : Fin 4 → ℤ,
    realificationMap (hnil := model.filtration.lowerCentralSeries_eq_bot)
      (hM := (pi (fun _ : Fin 8 => W.model)).filtration.lowerCentralSeries_eq_bot)
      ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra).incl
      (model.filtration.realification.polynomialOrbitEval (fun _ => 1) x orbit) =
        (pi (fun _ : Fin 8 => W.model)).filtration.adaptedPolynomialRealValueHom
          (fun _ : Fin 4 => 1) (fun i => (x i : ℝ)) V.middle
  quotientDim : ℕ
  quotientDim_le : quotientDim ≤ finrank ℚ
    ((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra)
  quotient : RationalFilteredNilmanifold
    (((pi (fun _ : Fin 8 => W.model)).filtration.gradedRefiltrationSubalgebra V.subalgebra) ⧸
      model.filtration.layerIdeal 2) 1 quotientDim
  quotient_filtration : quotient.filtration = model.filtration.quotientTop
  quotient_lattice : quotient.lattice = model.lattice.map
    (model.filtration.quotientStepHom (model.filtration.layerIdeal 2) le_rfl)
  quotient_complexity : quotient.GeometryComplexityLE q
  projection_height : ∀ i j, rationalLogHeight (quotient.basis.repr
    (lieQuotientMap (model.filtration.layerIdeal 2) (model.basis i)) j) ≤ q
  projectedOrbit : quotient.filtration.realification.PolynomialOrbit (fun _ : Fin 4 => 1)
  projected_degree : DegreeLE (fun _ : Fin 4 => 1) 1 projectedOrbit.log
  projection : ∀ x : Fin 4 → ℤ,
    quotient.filtration.realification.polynomialOrbitEval (fun _ => 1) x projectedOrbit =
      realificationMap (hnil := model.filtration.lowerCentralSeries_eq_bot)
        (hM := quotient.filtration.lowerCentralSeries_eq_bot)
        (lieQuotientMap (model.filtration.layerIdeal 2))
        (model.filtration.realification.polynomialOrbitEval (fun _ => 1) x orbit)

theorem exists_antisymmetric_middle_quotient :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ}
      (W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p)
      {N : ℕ} (V : NativeAntisymmetricOrbitFactors W N p), 0 ≤ p →
      Nonempty (NativeAntisymmetricMiddleQuotient V ((p + C) ^ C)) := by
  obtain ⟨A, _, hmodel⟩ := exists_antisymmetric_middle_model
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (X + Polynomial.C A) ^ A
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T + (T + 3) ^ 11)
  refine ⟨C, hC, ?_⟩
  intro p W N V hp
  obtain ⟨E, hEF, hEL, hE, hinc, g, hg⟩ := hmodel W V hp
  let t := p + (p + A) ^ A
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hAt : (p + A) ^ A ≤ t := le_add_of_nonneg_left hp
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hproj, _⟩ :=
    E.exists_controlled_top_quotient ht (hE.mono E hAt)
  have hsum : t + (t + 3) ^ 11 ≤ (p + C) ^ C := by
    simpa [T, X, t, Polynomial.eval₂_pow] using hbudget p hp
  have htC : t ≤ (p + C) ^ C := (le_add_of_nonneg_right (by positivity)).trans hsum
  have hQC : (t + 3) ^ 11 ≤ (p + C) ^ C := (le_add_of_nonneg_left ht).trans hsum
  have h5 : (t + 3) ^ 5 ≤ (t + 3) ^ 11 := pow_le_pow_right₀ (by linarith) (by decide)
  let gbar := E.topQuotientOrbit Q hQF g
  exact ⟨{
    model := E
    filtration := hEF
    lattice := hEL
    complexity := hE.mono E (hAt.trans htC)
    inclusion_height := fun i j => (hinc i j).trans (hAt.trans htC)
    orbit := g
    inclusion := hg
    quotientDim := n
    quotientDim_le := hn
    quotient := Q
    quotient_filtration := hQF
    quotient_lattice := hQL
    quotient_complexity := hQ.mono Q hQC
    projection_height := fun i j => (hproj i j).trans (h5.trans hQC)
    projectedOrbit := gbar
    projected_degree := gbar.degreeLE
    projection := fun x => E.topQuotientOrbit_eval Q hQF g x }⟩

end Erdos3

end

end OAI
