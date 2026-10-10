import OAI.Combinatorics.Progressions.Linear.ExternalFamilyPrecenterProjectionData

namespace OAI

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators Classical

theorem exists_quantitative_kernel_projection_budget :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ Ω G : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [Fintype Ω] [Fintype G]
      {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
      (T : D.Niltest w) (p : ℝ), 0 ≤ p → T.UnitIntervalValued → T.ComplexityLE p →
      ∀ (P : Submodule ℚ L), P ≤ D.filtration.layer s →
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights G) (path : Ω → G → D.Space) (weight : Ω → G → ℂ),
      (∀ a x, ‖weight a x‖ ≤ Real.exp p) →
      (∀ a ∈ productive,
        Real.exp (-p) ≤ ((localLaw a).complexMean (fun x => weight a x * T.observable (path a x))).re) →
      ∃ (J : Type) (inst : Fintype J), letI := inst
      ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w)
        (code : Fin (finrank ℚ P) → Option J) (S : D.Niltest w) (retained : Finset Ω),
        (Fintype.card J : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ (p + 2) ^ C) ∧
        (∀ j, (U j).ComplexityLE ((p + 2) ^ C) ∧ (U j).orbit = T.orbit) ∧
        (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          (U j).observable (z • x) =
            character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x) ∧
        S.UnitIntervalValued ∧ S.ComplexityLE ((p + 2) ^ C) ∧ S.orbit = T.orbit ∧
        (∀ z : D.RealGroup, z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
          ∀ x, S.observable (z • x) = S.observable x) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        ∀ a ∈ retained,
          (∀ i j, code i = some j → Real.exp (-((p + 2) ^ C)) <
            ‖(localLaw a).complexMean (fun x => weight a x * (U j).observable (path a x))‖) ∧
          Real.exp (-((p + 2) ^ C)) ≤
            ((localLaw a).complexMean (fun x => weight a x * S.observable (path a x))).re := by
  let X : Polynomial ℕ := Polynomial.X
  let Q := 2 * X + 8
  let A := (Q + 3) ^ 9 + 2 * Q + 2
  let V := 2 * A * (2 * A + 2) ^ 4 + ((2 * A + 2) ^ 4 + A + (Q + 3) ^ 5 + 2) ^ 4
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_fixed_power_budget
    (Q + 2 * V + X + 10 + X * (V + 1))
  refine ⟨C, hC, ?_⟩
  intro L σ Ω G _ _ s d _ _ _ _ _ _ D w T p hp hT hTc P hP outer productive localLaw path weight hweight hscore
  let : FiniteDimensional ℚ L := D.basis.finiteDimensional_of_finite
  let q := 2 * p + 8
  let v := verticalDecompositionBudget q
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hv : 0 ≤ v := verticalDecompositionBudget_nonneg hq
  have hprod : 0 ≤ p * (v + 1) := by positivity
  have hb : q + 2 * v + p + 10 + p * (v + 1) ≤ (p + 2) ^ C := by
    simpa [X, Q, A, V, q, v, verticalDecompositionBudget, centralActionBudget,
      Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + 2) ^ C := by linarith
  have hvC : v ≤ (p + 2) ^ C := by linarith
  have htC : p + v + 8 ≤ (p + 2) ^ C := by linarith
  have hnC : p * (v + 1) ≤ (p + 2) ^ C := by linarith
  have hsC : p + 1 ≤ (p + 2) ^ C := by linarith
  obtain ⟨J, inst, eta, U, hJ, hheight, hU, hvert, hint, happrox, heval⟩ :=
    T.exists_vertical_decomposition_preserving_bounds hq (hTc.mono hpq)
      (Real.exp_pos (-q)) (by rw [Real.exp_neg, inv_inv])
  let := inst
  have hsmall := frequency_projection_error_bound hp hJ
  obtain ⟨code, S, retained, hS, hSc, hSo, hSinv, hretained, hmass, hlocal⟩ :=
    T.exists_common_positive_kernel_projection hT hTc P hP eta U hvert outer productive
      localLaw path weight (Real.exp_nonneg p) (Real.exp_nonneg (-(p + v + 8))) hweight
      (fun x => by simpa only [norm_sub_rev] using happrox x) hscore hsmall
  have hdim : (finrank ℚ P : ℝ) ≤ p := by
    have h := Submodule.finrank_le P
    rw [finrank_eq_card_basis D.basis, Fintype.card_fin] at h
    exact (Nat.cast_le.mpr h).trans hTc.1.1
  refine ⟨J, inst, eta, U, code, S, retained,
    hJ.trans (Real.exp_le_exp.mpr hvC), fun j i => (hheight j i).trans hvC,
    fun j => ⟨(hU j).1.mono hqC, (hU j).2.1⟩, hvert, hS,
    hSc.mono (hpq.trans hqC), hSo, hSinv, hretained, ?_, ?_⟩
  · exact (mass_div_frequency_count (outer.mass_nonneg productive) hp hv hdim hJ hnC).trans hmass
  · intro a ha
    obtain ⟨hpivot, hpositive⟩ := hlocal a ha
    refine ⟨fun i j hij => (Real.exp_le_exp.mpr (neg_le_neg htC)).trans_lt (hpivot i j hij), ?_⟩
    exact ((Real.exp_le_exp.mpr (by linarith : -((p + 2) ^ C) ≤ -p - 1)).trans
      (exp_sub_one_le_half_exp (-p))).trans hpositive

end Erdos3

end

section

namespace Erdos3

open Module CircleFourier
open scoped TensorProduct BigOperators Classical

theorem exists_fixed_observable_family_kernel_projection :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ Ω G : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [Fintype Ω] [Fintype G]
      {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
      (T : D.Niltest w) (tests : Ω → D.Niltest w),
      (∀ a, (tests a).observable = T.observable) →
      ∀ p : ℝ, 0 ≤ p → T.UnitIntervalValued → T.ComplexityLE p →
      ∀ (P : Submodule ℚ L), P ≤ D.filtration.layer s →
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights G) (point : Ω → G → σ → ℤ)
        (weight : Ω → G → ℂ),
      (∀ a t, ‖weight a t‖ ≤ Real.exp p) →
      (∀ a ∈ productive, Real.exp (-p) ≤
        ((localLaw a).complexMean (fun t => weight a t * (tests a).eval (point a t))).re) →
      ∃ (J : Type) (inst : Fintype J), letI := inst
      ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w)
        (code : Fin (finrank ℚ P) → Option J) (S : D.Niltest w) (retained : Finset Ω),
        (Fintype.card J : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ (p + 2) ^ C) ∧
        (∀ j, (U j).ComplexityLE ((p + 2) ^ C) ∧ (U j).orbit = T.orbit) ∧
        (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          (U j).observable (z • x) =
            character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
              (U j).observable x) ∧
        S.UnitIntervalValued ∧ S.ComplexityLE ((p + 2) ^ C) ∧ S.orbit = T.orbit ∧
        (∀ z : D.RealGroup, z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
          ∀ x, S.observable (z • x) = S.observable x) ∧
        (∀ a, (S.withOrbit (tests a).orbit).UnitIntervalValued ∧
          (S.withOrbit (tests a).orbit).ComplexityLE ((p + 2) ^ C) ∧
          (S.withOrbit (tests a).orbit).orbit = (tests a).orbit ∧
          (S.withOrbit (tests a).orbit).observable = S.observable) ∧
        (∀ a j, ((U j).withOrbit (tests a).orbit).ComplexityLE ((p + 2) ^ C) ∧
          ((U j).withOrbit (tests a).orbit).orbit = (tests a).orbit ∧
          ((U j).withOrbit (tests a).orbit).observable = (U j).observable) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        ∀ a ∈ retained,
          (∀ i j, code i = some j → Real.exp (-((p + 2) ^ C)) <
            ‖(localLaw a).complexMean (fun t =>
              weight a t * ((U j).withOrbit (tests a).orbit).eval (point a t))‖) ∧
          Real.exp (-((p + 2) ^ C)) ≤
            ((localLaw a).complexMean (fun t =>
              weight a t * (S.withOrbit (tests a).orbit).eval (point a t))).re := by
  obtain ⟨C, hC, hproject⟩ := exists_quantitative_kernel_projection_budget
  refine ⟨C, hC, ?_⟩
  intro L σ Ω G _ _ s d _ _ _ _ _ _ D w T tests hobs p hp hT hTc P hP
    outer productive localLaw point weight hweight hscore
  let path : Ω → G → D.Space := fun a t => QuotientGroup.mk
    (D.filtration.realification.polynomialOrbitEval w (point a t) (tests a).orbit)
  have heval (a : Ω) (t : G) : (tests a).eval (point a t) = T.observable (path a t) := by
    change (tests a).observable _ = T.observable _
    rw [hobs a]
  obtain ⟨J, inst, eta, U, code, S, retained, hJ, heta, hU, hvert,
      hS, hSc, hSo, hinvariant, hretained, hmass, hlocal⟩ :=
    hproject T p hp hT hTc P hP outer productive localLaw path weight hweight
      (by simpa only [heval] using hscore)
  let _ := inst
  refine ⟨J, inst, eta, U, code, S, retained, hJ, heta, hU, hvert,
    hS, hSc, hSo, hinvariant, ?_, ?_, hretained, hmass, ?_⟩
  · intro a
    exact ⟨hS, hSc, rfl, rfl⟩
  · intro a j
    exact ⟨(hU j).1, rfl, rfl⟩
  · intro a ha
    exact hlocal a ha

theorem exists_fixed_observable_family_kernel_projection_real :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {L σ Ω G : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [Fintype Ω] [Fintype G]
      {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}
      (F : D.Space → ℂ) (tests : Ω → D.Niltest w) (p : ℝ), 0 ≤ p →
      (∀ a, (tests a).observable = F ∧ (tests a).UnitIntervalValued ∧
        (tests a).ComplexityLE p) →
      ∀ (P : Submodule ℚ L), P ≤ D.filtration.layer s →
      ∀ (outer : FiniteProbabilityWeights Ω) (productive : Finset Ω)
        (localLaw : Ω → FiniteProbabilityWeights G) (point : Ω → G → σ → ℤ)
        (score : Ω → G → ℝ),
      (∀ a t, |score a t| ≤ 1) →
      (∀ a ∈ productive, Real.exp (-p) ≤
        (localLaw a).mean (fun t => score a t * ((tests a).eval (point a t)).re)) →
      ∃ (J : Type) (inst : Fintype J), letI := inst
      ∃ (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest w)
        (code : Fin (finrank ℚ P) → Option J) (S : D.Niltest w) (retained : Finset Ω),
        (Fintype.card J : ℝ) ≤ Real.exp ((p + 2) ^ C) ∧
        (∀ j i, rationalLogHeight (eta j (D.basis i)) ≤ (p + 2) ^ C) ∧
        (∀ j, (U j).ComplexityLE ((p + 2) ^ C)) ∧
        (∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
          (U j).observable (z • x) =
            character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) *
              (U j).observable x) ∧
        S.UnitIntervalValued ∧ S.ComplexityLE ((p + 2) ^ C) ∧
        (∀ z : D.RealGroup, z.coord ∈ (frequencyCodeKernel P eta code).baseChange ℝ →
          ∀ x, S.observable (z • x) = S.observable x) ∧
        (∀ a, (S.withOrbit (tests a).orbit).UnitIntervalValued ∧
          (S.withOrbit (tests a).orbit).ComplexityLE ((p + 2) ^ C) ∧
          (S.withOrbit (tests a).orbit).orbit = (tests a).orbit ∧
          (S.withOrbit (tests a).orbit).observable = S.observable) ∧
        (∀ a j, ((U j).withOrbit (tests a).orbit).ComplexityLE ((p + 2) ^ C) ∧
          ((U j).withOrbit (tests a).orbit).orbit = (tests a).orbit ∧
          ((U j).withOrbit (tests a).orbit).observable = (U j).observable) ∧
        retained ⊆ productive ∧
        outer.mass productive * Real.exp (-((p + 2) ^ C)) ≤ outer.mass retained ∧
        ∀ a ∈ retained,
          (∀ i j, code i = some j → Real.exp (-((p + 2) ^ C)) <
            ‖(localLaw a).complexMean (fun t =>
              (score a t : ℂ) * ((U j).withOrbit (tests a).orbit).eval (point a t))‖) ∧
          Real.exp (-((p + 2) ^ C)) ≤ (localLaw a).mean (fun t =>
            score a t * ((S.withOrbit (tests a).orbit).eval (point a t)).re) := by
  obtain ⟨C, hC, hproject⟩ := exists_fixed_observable_family_kernel_projection
  refine ⟨C, hC, ?_⟩
  intro L σ Ω G _ _ s d _ _ _ _ _ _ D w F tests p hp htests P hP
    outer productive localLaw point score hscore hpositive
  have hnonempty : Nonempty Ω := by
    by_contra h
    have _ : IsEmpty Ω := not_nonempty_iff.mp h
    simpa using outer.total
  let a₀ : Ω := Classical.choice hnonempty
  have hobs (a : Ω) : (tests a).observable = (tests a₀).observable :=
    (htests a).1.trans (htests a₀).1.symm
  have hweight (a : Ω) (t : G) : ‖(score a t : ℂ)‖ ≤ Real.exp p := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using
      (hscore a t).trans (Real.one_le_exp hp)
  have hpositive' (a : Ω) (ha : a ∈ productive) : Real.exp (-p) ≤
      ((localLaw a).complexMean (fun t =>
        (score a t : ℂ) * (tests a).eval (point a t))).re := by
    simpa only [FiniteProbabilityWeights.complexMean_re, Complex.re_ofReal_mul] using
      hpositive a ha
  obtain ⟨J, inst, eta, U, code, S, retained, hJ, heta, hU, hvert,
      hS, hSc, _, hinvariant, hSloc, hUloc, hretained, hmass, hlocal⟩ :=
    hproject (tests a₀) tests hobs p hp (htests a₀).2.1 (htests a₀).2.2
      P hP outer productive localLaw point (fun a t => (score a t : ℂ)) hweight hpositive'
  let _ := inst
  refine ⟨J, inst, eta, U, code, S, retained, hJ, heta, fun j => (hU j).1,
    hvert, hS, hSc, hinvariant, hSloc, hUloc, hretained, hmass, ?_⟩
  intro a ha
  refine ⟨(hlocal a ha).1, ?_⟩
  simpa only [FiniteProbabilityWeights.complexMean_re, Complex.re_ofReal_mul] using
    (hlocal a ha).2

end Erdos3

end

end OAI
