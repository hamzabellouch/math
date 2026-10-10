import OAI.Combinatorics.Progressions.Estimates.PhysicalSingleSiteCommonCover

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open VectorPolynomial MeasureTheory
open scoped BigOperators Classical

theorem exists_affine_site_cover_tilted_comparison (m r : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    (root : K → ℤ) (difference : Fin r → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    [MeasurableSpace (SiteTorus (Finset (Fin r)) U)] [BorelSpace (SiteTorus (Finset (Fin r)) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    {C : ℝ} (_hC : 0 ≤ C) (_hCP : C ≤ Real.exp P)
    (frequency : Bool → F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ b a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency b a j d t : ℝ)| ≤ C)
    (c : Bool → F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : ∀ b, (∑ a, ‖c b a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (q : ℕ) (_hq : 0 < q) (_hqP : (q : ℝ) ≤ Real.exp P)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ ε : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hε : 0 < ε)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hεP : 1 / ε ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ) (_hD : Integrable D μ)
    (_hDmass : (∫ x, D x ∂μ) = 1) (_hD0 : ∀ x, 0 ≤ D x)
    (f : SiteTorus (Finset (Fin r)) U → ℂ) (_hf : Measurable f)
    (_hfbound : ∀ x, ‖f x‖ ≤ 1)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ b x,
      ‖(D x : ℂ) * (if b then f (coefficientSiteTorusMap U (fun s k => affineSite root difference s (some k)) x) else 1) - coefficientTorusFourierSum U (frequency b) (c b) x‖ ≤ η)
    (_hsmall : 2 * η + ε ≤ 1 / 2),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ∃ hDpos : 0 < selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p hm q (fun k j => (z (k, j) : ℝ)))),
    |selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p hm q (fun k j => (z (k, j) : ℝ)))) - 1| ≤ 2 * η + ε ∧
    (1 / 2 ≤ selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p hm q (fun k j => (z (k, j) : ℝ))))) ∧
    (selectedResidueDensityMass stride G V
      (fun z => D (affineCoefficientCoverSample U p hm q (fun k j => (z (k, j) : ℝ)))) ≤ 3 / 2) ∧
    ‖(∑' z, ((selectedResidueDensityPMF stride G V hV hZ
        (fun z => D (affineCoefficientCoverSample U p hm q (fun k j => (z (k, j) : ℝ))))
        (fun _z => _hD0 _) hDpos z).toReal : ℂ) *
          f (affineCoveredSiteSample U root difference q p hm (fun k j => (z (k, j) : ℝ)))) -
      (∫ x, (D x : ℂ) * f (coefficientSiteTorusMap U (fun s k => affineSite root difference s (some k)) x) ∂μ)‖ ≤ 4 * (2 * η + ε) := by
  obtain ⟨A, hA, hcomparison⟩ := exists_affine_coefficient_cover_tilted_comparison m
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hd U root difference _ _ _ _ μ _ _
    C hC hCP frequency hbound c B hB hBP hcoefficients p hp hm q hq hqP
    stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR G hG V hV hwidth
    D hD hDmass hD0 f hf hfbound η hη happrox hsmall
  let g : CoefficientTorus (K := K) U → ℂ := fun x =>
    f (coefficientSiteTorusMap U (fun s k => affineSite root difference s (some k)) x)
  have hg : AEStronglyMeasurable g μ :=
    (hf.comp (coefficientSiteTorusMap_continuous U _).measurable).aestronglyMeasurable
  obtain ⟨hZ, hDpos, hmass, hlower, hupper, he⟩ :=
    hcomparison hP hn hd U μ hC hCP frequency hbound c hB hBP hcoefficients
      p hp hm q hq hqP stride hs hS hSP hρ hε hρP hεP hstride H hsize hrank hR
      G hG V hV hwidth D hD hDmass hD0 g hg (fun _ => hfbound _) hη happrox hsmall
  refine ⟨hZ, hDpos, hmass, hlower, hupper, ?_⟩
  simpa only [g, coefficientSiteTorusMap_coverSample U root difference q p hp hm] using he

end Erdos3.BooleanCubeKernel

end

end OAI
