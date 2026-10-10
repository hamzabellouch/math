import OAI.Combinatorics.Progressions.Estimates.CommonNativeSquareFactors

namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators NNReal

theorem exists_fixed_anchored_quotient_modes (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {X σ : Type*} {L : Bool → Type*}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : Bool → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      (w : σ → ℕ), (∀ i, 0 < w i) →
      ∀ (T : ∀ i, (D i).Niltest w) (p : ℝ), 0 ≤ p →
      (∀ i, (T i).ComplexityLE p) → (∀ i, ((T i).normBound : ℝ) ≤ 1) →
      ∀ (χ : ∀ i, (D i).RealGroup → CircleFourier.Circle),
      (∀ i z, z ∈ (D i).filtration.realification.subgroup (s + 1) → ∀ x,
        (T i).observable (z • x) = character (χ i z) * (T i).observable x) →
      ∃ (n : Bool → ℕ)
        (Q : ∀ i, RationalFilteredNilmanifold ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1)) s (n i))
        (weight : ∀ i, Fin (n i) → ℕ),
        (∀ i j, (Q i).filtration.layer j = Submodule.span ℚ ((Q i).basis '' {k | j ≤ weight i k})) ∧
        (∀ i, (Q i).GeometryComplexityLE (squareGeometryBudget p)) ∧
        ∃ A : (Q true).Niltest w,
          A.normBound = (T true).normBound ^ 2 ∧ A.ComplexityLE ((p + C) ^ C) ∧
          (∀ x, A.eval x = (T true).eval x * star ((T true).eval x)) ∧
          ∀ a b : σ → ℤ, ∃ B : (Q false).Niltest w,
            B.normBound = (T false).normBound ^ 2 ∧ B.ComplexityLE ((p + C) ^ C) ∧
            (∀ x, B.eval x = (T false).eval (x + a) * star ((T false).eval (x + b))) ∧
            ∀ (I : Finset X), I.Nonempty → ∀ (sample : X → σ → ℤ) (U : X → ℂ),
            (∀ x ∈ I, ‖U x‖ ≤ 1) →
            Real.exp (-p) ≤ ‖𝔼 x ∈ I, U x *
              ((T true).eval (sample x) * star ((T true).eval (sample x))) *
              ((T false).eval (sample x + a) * star ((T false).eval (sample x + b)))‖ →
            ∃ (eta : ((D true).filtration.squareLieSubalgebra ⧸
                (D true).filtration.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
              (eta' : ((D false).filtration.squareLieSubalgebra ⧸
                (D false).filtration.squareFiltration.layerIdeal (s + 1)) →ₗ[ℚ] ℚ)
              (V : (Q true).Niltest w) (W : (Q false).Niltest w),
              V.orbit = A.orbit ∧ W.orbit = B.orbit ∧
              V.ComplexityLE ((p + C) ^ C) ∧ W.ComplexityLE ((p + C) ^ C) ∧
              (V.normBound : ℝ) ≤ 1 ∧ (W.normBound : ℝ) ≤ 1 ∧
              (∀ k, rationalLogHeight (eta ((Q true).basis k)) ≤ (p + C) ^ C) ∧
              (∀ k, rationalLogHeight (eta' ((Q false).basis k)) ≤ (p + C) ^ C) ∧
              (∀ z, z ∈ (Q true).filtration.realification.subgroup s → ∀ x,
                V.observable (z • x) = character ((realifyFunctional eta z.coord : ℝ) : CircleFourier.Circle) *
                  V.observable x) ∧
              (∀ z, z ∈ (Q false).filtration.realification.subgroup s → ∀ x,
                W.observable (z • x) = character ((realifyFunctional eta' z.coord : ℝ) : CircleFourier.Circle) *
                  W.observable x) ∧
              Real.exp (-((p + C) ^ C)) ≤ ‖𝔼 x ∈ I, U x * V.eval (sample x) * W.eval (sample x)‖ := by
  obtain ⟨c, _, hsquare⟩ := exists_adapted_uniform_two_shift_square s
  obtain ⟨k, _, hmodes⟩ := exists_native_vertical_pair_power
  let P₀ : Polynomial ℕ := Polynomial.X + (Polynomial.X + Polynomial.C c) ^ c + 1
  let P : Polynomial ℕ := P₀ + (P₀ + Polynomial.C k) ^ k
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro X σ L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ w hw T p hp hT hcap χ hvert
  let q := p + (p + c) ^ c + 1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have hn : 0 ≤ (p + c) ^ c := by positivity
    dsimp [q]
    linarith
  have hsquareq : (p + c) ^ c ≤ q := by dsimp [q]; linarith
  have hb : q + (q + k) ^ k ≤ (p + C) ^ C := by
    simpa [P, P₀, q, Polynomial.eval₂_pow] using hbudget p hp
  have hk0 : 0 ≤ (q + k) ^ k := by positivity
  have hqC : q ≤ (p + C) ^ C := by linarith
  have hkC : (q + k) ^ k ≤ (p + C) ^ C := by linarith
  choose n Q weight hlayers hgeom hbuild using
    fun i : Bool => hsquare (D i) p hp w hw (T i) (hT i)
  obtain ⟨A, hAn, hAc, hAv⟩ := hbuild true (χ true) (hvert true) 0 0
  have hAval (x : σ → ℤ) : A.eval x = (T true).eval x * star ((T true).eval x) := by
    simpa only [add_zero] using hAv x
  have hAcap : (A.normBound : ℝ) ≤ 1 := by
    rw [hAn, NNReal.coe_pow]
    exact pow_le_one₀ (T true).normBound.coe_nonneg (hcap true)
  refine ⟨n, Q, weight, hlayers, hgeom, A, hAn, hAc.mono (hsquareq.trans hqC), hAval, ?_⟩
  intro a b
  obtain ⟨B, hBn, hBc, hBv⟩ := hbuild false (χ false) (hvert false) a b
  have hBcap : (B.normBound : ℝ) ≤ 1 := by
    rw [hBn, NNReal.coe_pow]
    exact pow_le_one₀ (T false).normBound.coe_nonneg (hcap false)
  refine ⟨B, hBn, hBc.mono (hsquareq.trans hqC), hBv, ?_⟩
  intro I hI sample U hU hcorr
  have hc : Real.exp (-q) ≤ ‖𝔼 x ∈ I, U x * A.eval (sample x) * B.eval (sample x)‖ := by
    apply (Real.exp_le_exp.mpr (neg_le_neg hpq)).trans
    simpa only [hAval, hBv] using hcorr
  obtain ⟨eta, eta', V, W, hVc, hVo, hVn, hWc, hWo, hWn, hVheight, hWheight, hVvert, hWvert, hbias⟩ :=
    hmodes (Q true) (Q false) A B q hq (hAc.mono hsquareq) (hBc.mono hsquareq)
      hAcap hBcap I hI sample U hU hc
  refine ⟨eta, eta', V, W, hVo, hWo, hVc.mono hkC, hWc.mono hkC, ?_, ?_,
    (fun i => (hVheight i).trans hkC), (fun i => (hWheight i).trans hkC), hVvert, hWvert,
    (Real.exp_le_exp.mpr (neg_le_neg hkC)).trans hbias⟩
  · rw [hVn]
    exact hAcap
  · rw [hWn]
    exact hBcap

end Erdos3

end

end OAI
