import OAI.Combinatorics.Progressions.Sampling.CoefficientUniformPerturbationSampling
import OAI.Combinatorics.Progressions.Sampling.SquareSamplingAccuracy

namespace OAI

section

namespace Erdos3.VectorPolynomial
open MeasureTheory
open scoped BigOperators Classical NNReal

theorem exists_coefficient_uniform_small_error (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P target : ℝ}, 0 ≤ P → 0 ≤ target → (Fintype.card I : ℝ) ≤ P →
    (Fintype.card (Option K × I) : ℝ) ≤ P →
    (Fintype.card (CoefficientAmbientIndex K J) : ℝ) ≤ P →
    ∀ (U : ∀ j, Submodule ℝ (J j → ℝ))
    [CompactSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ)),
    (∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j)) →
    ∀ (hm : ∀ j e, coefficients (p j) e ∈ U j)
    {T : Type*} [Fintype T] (period : T → ℕ), (∀ t, 0 < period t) →
    (∀ t, (period t : ℝ) ≤ Real.exp P) →
    ∀ (D : ℕ), 0 < D → (∀ a b, period a * period b ∣ D) →
    ∀ (stride : I → ℕ), (∀ i, 0 < stride i) → (∀ i, (stride i : ℝ) ≤ Real.exp P) →
    ∀ {R ρ : ℝ}, 0 < ρ → 1 / ρ ≤ Real.exp P →
    ∀ (H : I → ℝ), (∀ i, Real.exp ((P + target + A) ^ A) ≤ H i) →
    (∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j)) →
    Real.exp ((P + target + A) ^ A) ≤ R →
    ∀ (G : Finset (ColumnResiduePattern (Option K) I stride)), G.Nonempty →
    ∀ (V : Option K × I → ℝ) (_hV : ∀ z, 0 < V z), (∀ z, ρ * H z.2 ≤ V z) →
    (0 < ∑' z, selectedResidueSmoothWeight stride G V z) →
    ∀ (coeff : T → ℂ) (f : T → (CoefficientAmbientIndex K J → UnitAddCircle) → ℂ)
    (L : T → ℝ≥0), (∀ t, LipschitzWith (L t) (f t)) → (∀ t z, ‖f t z‖ ≤ 1) →
    (∀ t, (L t : ℝ) ≤ Real.exp P) → (∑ t, ‖coeff t‖) ≤ Real.exp P →
    ∀ (actual : (Option K × I → ℤ) → ℂ)
    (reference : CoefficientTorus (K := K) U → ℂ),
    Integrable (fun z => ‖reference z‖ ^ 2) μ →
    (∫ z, ‖reference z‖ ^ 2 ∂μ) ≤ Real.exp (-(target + 20)) →
    (∀ z, ‖actual z - ∑ t, coeff t * f t (coefficientAmbientTorus U
      (affineCoefficientCoverSample U p hm (period t) (fun k j => (z (k,j) : ℝ))))‖ ≤ Real.exp (-(target + 20))) →
    (∀ z, ‖reference z - ∑ t, coeff t * f t ((D / period t) • coefficientAmbientTorus U z)‖ ≤ Real.exp (-(target + 20))) →
    selectedResidueDensityMass stride G V (fun z => ‖actual z‖ ^ 2) ≤
      Real.exp (-target) := by
  obtain ⟨A₀, _, hsample⟩ := exists_coefficient_uniform_perturbation_sampling m
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_eval_budget
    (((2 : Polynomial ℕ) * Polynomial.X + 20 + Polynomial.C A₀) ^ A₀)
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ P target hP htarget hn hd hdim U _ _ _ μ _ _ p hp hm T _ period hperiod hperiodP D hD hdiv
    stride hs hstride R ρ hρ hρP H hsize hrank hR G hG V hV hwidth hZ coeff f L hf hfb hLP hcoeff
    actual reference href hE hactual hreference
  let B := 2 * P + target + 20
  let ε := Real.exp (-(target + 2 * P + 20))
  have hPB : P ≤ B := by dsimp [B]; linarith
  have hB : 0 ≤ B := hP.trans hPB
  have hePB := Real.exp_le_exp.mpr hPB
  have hε : 0 < ε := Real.exp_pos _
  have hεB : 1 / ε ≤ Real.exp B := by
    dsimp [ε, B]
    rw [one_div, ← Real.exp_neg, neg_neg]
    exact Real.exp_le_exp.mpr (by ring_nf; exact le_refl _)
  have hcost : (B + A₀) ^ A₀ ≤ (P + target + A) ^ A := by
    have hpoly := hbudget (P + target) (add_nonneg hP htarget)
    have hb : B ≤ 2 * (P + target) + 20 := by dsimp [B]; linarith
    apply (pow_le_pow_left₀ (by positivity : 0 ≤ B + A₀) (show B + (A₀ : ℝ) ≤ 2 * (P + target) + 20 + A₀ by linarith) A₀).trans
    simpa [Polynomial.eval₂_pow] using hpoly
  have hh := hsample hB (hn.trans hPB) (hd.trans hPB) (hdim.trans hPB) U μ p hp hm
    period hperiod (fun t => (hperiodP t).trans hePB) D hD hdiv stride hs
    (fun i => (hstride i).trans hePB) hρ hε (hρP.trans hePB) hεB H
    (fun i => (Real.exp_le_exp.mpr hcost).trans (hsize i)) hrank
    ((Real.exp_le_exp.mpr hcost).trans hR) G hG V hV hwidth hZ coeff f L hf hfb
    (fun t => (hLP t).trans hePB) actual reference href hE hactual hreference
  apply hh.trans
  have ha := squareSamplingAccuracy_bound htarget (Real.exp_pos (-(target + 20))).le
    (Finset.sum_nonneg (fun t _ => norm_nonneg (coeff t))) (le_refl (0 : ℝ)) hε.le
    (le_refl _) (le_refl _) hcoeff (Real.exp_pos (-(target + 2 * P + 20))).le (le_refl ε)
  simpa only [mul_zero, zero_add] using ha

end Erdos3.VectorPolynomial

end

end OAI
