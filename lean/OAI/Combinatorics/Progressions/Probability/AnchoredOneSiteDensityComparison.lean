import OAI.Combinatorics.Progressions.Lattices.AnchoredResidueProjectionTransfer

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

theorem exists_anchored_affine_oneSite_density_comparison (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    (anchor : Option K × I → ℤ)
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ))
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (root : K → ℤ) (difference : Fin 0 → K → ℤ)
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin 0)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
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
    (H : I → ℝ)
    (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ i, HasLayerSamplingRank (i.val + 1) H R (U i) (p i))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (Q : MvPolynomial (Option K × I) ℝ) (_hQ : Q.totalDegree ≤ 0)
    (test : Finset (Fin 0) → (I → ℝ) → ℂ) (_htest : ∀ t v, ‖test t v‖ ≤ 1)
    (G : Finset (ColumnResiduePattern (Option K) I stride)) (_hG : G.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (D : CoefficientTorus (K := K) U → ℝ)
    (_hD : ∀ y, Integrable (fun x => D (coefficientFiberMap U root y x)) μ)
    {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η),
    ∃ hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x,
    ‖(∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => ((anchor + z) (k, j) : ℝ)) *
          (D (affineSampleCoefficientTorus U p _hm (fun k j => ((anchor + z) (k, j) : ℝ))) : ℂ))) -
      (∑' z : Option K × I → ℤ, ((selectedResidueSmoothPMF stride G V hV hZ z).toReal : ℂ) *
        (layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => ((anchor + z) (k, j) : ℝ)) *
          ((coefficientFiberAverage U μ root D (coefficientEvaluationTorus U root
            (affineSampleCoefficientTorus U p _hm (fun k j => ((anchor + z) (k, j) : ℝ)))) : ℝ) : ℂ)))‖ ≤ 2 * η + ε := by
  obtain ⟨A, hA, hprojection⟩ := exists_anchored_affine_cube_fourier_projection m 0
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ anchor J _ F _ P hP hn hd U _ _ μ _ _ root difference
    L C hL hC hLP hCP hsite frequency hbound c B hB hBP hcoefficients p hp hm
    stride hs R S ρ ε hS hSP hρ hε hρP hεP hstride H hsize hrank hR Q hQ test htest
    G hG V hV hwidth D hD η hη happrox
  obtain ⟨hZ, he⟩ := hprojection anchor hP hn hd U root difference linearIndependent_empty_type
    hL hC hLP hCP hsite frequency hbound c hB hBP hcoefficients p hp hm stride hs
    hS hSP hρ hε hρP hεP hstride H hsize hrank hR Q hQ test htest G hG V hV hwidth
  refine ⟨hZ, ?_⟩
  exact anchored_selectedResidue_oneSite_density_error anchor U root difference frequency c μ D hη happrox hD p hp hm
    stride G V hV hZ
    (fun z => layeredSiteWeight Q (fun s => affineSite root difference s) test (fun k j => ((anchor + z) (k, j) : ℝ)))
    (fun z => layeredSiteWeight_norm_le Q _ test htest _) he

end Erdos3.BooleanCubeKernel

end

end OAI
