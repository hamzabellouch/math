import OAI.Combinatorics.Progressions.Fourier.AnchoredCoefficientFourierNormalization
import OAI.Combinatorics.Progressions.Fourier.SiteFourierHaarMean
import OAI.Combinatorics.Progressions.Probability.ProbabilityIntegralApproximation

namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_anchored_affine_coefficient_haar_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    (origin : Option K → I → ℝ)
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        coefficientTorusFourierSum U frequency c
          (affineSampleCoefficientTorus U p _hm (origin + fun k j => (z (k, j) : ℝ)))) -
      (∫ x, coefficientTorusFourierSum U frequency c x ∂μ)‖ ≤ ε := by
  obtain ⟨A, hA, hnormalization⟩ := exists_anchored_affine_coefficient_fourier_normalization m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ origin J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  obtain ⟨hZ, hnorm⟩ := hnormalization origin hP hn hd U hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  rw [coefficientTorusFourierSum_integral]
  simpa only [coefficientTorusFourierSum, coefficientTorusCharacter_sample U _ p hp hm] using hnorm

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped BigOperators Classical

theorem exists_anchored_affine_coefficient_haar_approximation (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    (origin : Option K → I → ℝ)
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (_hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (f : CoefficientTorus (K := K) U → ℂ) (_hf : Integrable f μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖f x - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        f (affineSampleCoefficientTorus U p _hm (origin + fun k j => (z (k, j) : ℝ)))) -
      (∫ x, f x ∂μ)‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hcomparison⟩ := exists_anchored_affine_coefficient_haar_comparison m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ origin J _ F _ P hP hn hd U _ _ μ _ _ C hC hCP frequency hbound c B hB hBP hcoefficients
    p hp hm stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth f hf η hη happrox
  obtain ⟨hZ, hcomp⟩ := hcomparison origin hP hn hd U μ hC hCP frequency hbound c hB hBP hcoefficients
    p hp hm stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  let g := coefficientTorusFourierSum U frequency c
  let sample (z : Option K × I → ℤ) := affineSampleCoefficientTorus U p hm (origin + fun k j => (z (k, j) : ℝ))
  let E (a : CoefficientTorus (K := K) U → ℂ) :=
    ∑' z, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) * a (sample z)
  have hfirst := selectedResidueSmoothPMF_approximation stride G V hV hZ
    (fun _ => 1) (fun z => f (sample z)) (fun z => g (sample z)) hη
    (fun _ _ => by simp) (fun z _ => happrox (sample z))
  simp only [one_mul] at hfirst
  have hlast := probability_integral_approximation μ g f
    (coefficientTorusFourierSum_integrable U frequency c μ) hf
    (fun x => by simpa only [norm_sub_rev] using happrox x)
  have htri := norm_sub_le_norm_sub_add_norm_sub (E f) (E g) (∫ x, f x ∂μ)
  have htri' := norm_sub_le_norm_sub_add_norm_sub (E g) (∫ x, g x ∂μ) (∫ x, f x ∂μ)
  change ‖E f - E g‖ ≤ η at hfirst
  change ‖E g - ∫ x, g x ∂μ‖ ≤ ε at hcomp
  change ‖E f - ∫ x, f x ∂μ‖ ≤ 2 * η + ε
  linarith

end Erdos3.VectorPolynomial

end

end OAI
