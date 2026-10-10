import OAI.Combinatorics.Progressions.Estimates.ShiftedProductTestError
import OAI.Combinatorics.Progressions.Lattices.AffineCubeCoveredProjection

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial
open scoped BigOperators

theorem exists_density_covered_physical_comparison (m q : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ {I K : Type*}
    [Fintype I] [DecidableEq I] [Fintype K]
    {J : Fin m → Type*} [∀ j, Fintype (J j)] {F : Type*} [Fintype F]
    {P : ℝ} (_hP : 0 ≤ P) (_hn : (Fintype.card I : ℝ) ≤ P)
    (_hK : (Fintype.card K : ℝ) ≤ P) (_hd : (Fintype.card (Option K × I) : ℝ) ≤ P)
    (U : ∀ j, Submodule ℝ (J j → ℝ)) (root : K → ℤ) (difference : Fin q → K → ℤ)
    (_hlin : LinearIndependent ℝ (fun i k => (difference i k : ℝ)))
    {L C : ℝ} (_hL : 0 ≤ L) (_hC : 0 ≤ C) (_hLP : L ≤ Real.exp P) (_hCP : C ≤ Real.exp P)
    (_hsite : ∀ (s : Finset (Fin q)) k, |((affineSite root difference s (some k) : ℤ) : ℝ)| ≤ L)
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ)
    (_hbound : ∀ a j d, d.degree ≤ j.val + 1 → ∀ t, |(frequency a j d t : ℝ)| ≤ C)
    (c : F → ℂ) {B : ℝ} (_hB : 0 ≤ B) (_hBP : B ≤ Real.exp P)
    (_hcoefficients : (∑ a, ‖c a‖) ≤ B)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (_hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j) (base : I → ℤ)
    (stride : I → ℕ) (_hs : ∀ k, 0 < stride k)
    {R S ρ δ : ℝ} (_hS : 0 ≤ S) (_hSP : S ≤ Real.exp P) (_hρ : 0 < ρ) (_hδ : 0 < δ)
    (_hρP : 1 / ρ ≤ Real.exp P) (_hδP : 1 / δ ≤ Real.exp P)
    (_hstride : ∀ k, (stride k : ℝ) ≤ S)
    (H : I → ℝ) (_hsize : ∀ k, Real.exp ((P + A) ^ A) ≤ H k)
    (_hrank : ∀ j, HasLayerSamplingRank (j.val + 1) H R (U j) (p j))
    (_hR : Real.exp ((P + A) ^ A) ≤ R)
    (test : Finset (Fin q) → (I → ℝ) → ℂ) (_htest : ∀ s x, ‖test s x‖ ≤ 1)
    (T : Finset (ColumnResiduePattern (Option K) I stride)) (_hT : T.Nonempty)
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z) (_hwidth : ∀ z, ρ * H z.2 ≤ V z)
    (density : CoefficientTorus (K := K) U → ℝ) {η : ℝ} (_hη : 0 ≤ η)
    (_happrox : ∀ x, ‖(density x : ℂ) - coefficientTorusFourierSum U frequency c x‖ ≤ η),
    let pa := fun j => translate (fun i => (base i : ℝ)) (p j)
    let hma := fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j)
    ∃ D : ℕ, 0 < D ∧ (D : ℝ) ≤ Real.exp ((P + A) ^ A) ∧
    ∃ b : F → ∀ j, Matrix (Finset (Fin q)) (J j) ℤ,
      (∀ a j s t, |(b a j s t : ℝ)| ≤ Real.exp ((P + A) ^ A)) ∧
    ∃ hZ : 0 < ∑' z, selectedResidueSmoothWeight stride T V z,
    ∀ {Y : Type*} [Countable Y] [MeasurableSpace Y] [MeasurableSingletonClass Y]
      (index : (Option K × I → ℤ) → Y) (reconstruct : Y → I → (Unit ⊕ Fin q) → ℤ),
    (∀ z, reconstruct (index z) = physicalCubeRootDifferences root (Matrix.of difference) base z) →
    ∀ (proxy : Y → ℝ), Integrable proxy Measure.count →
    ∀ {ε Z : ℝ}, 0 < Z →
      (∫ v, |(((selectedResidueSmoothPMF stride T V hV hZ).map index) v).toReal - proxy v|
        ∂Measure.count) ≤ ε →
      ‖(∑' z, ((selectedResidueSmoothPMF stride T V hV hZ z).toReal : ℂ) *
          (physicalCubeSiteTest test (physicalCubeRootDifferences root (Matrix.of difference) base z) *
            (density (affineSampleCoefficientTorus U pa hma (fun k i => (z (k, i) : ℝ))) : ℂ))) / (Z : ℂ) -
        (∫ v, (proxy v : ℂ) * physicalCubeCoveredTest U root difference D p hm frequency b c test (reconstruct v)
          ∂Measure.count) / (Z : ℂ)‖ ≤ (η + δ + (∑ a, ‖c a‖) * ε) / Z := by
  obtain ⟨A, hA, hprojection⟩ := exists_affine_cube_covered_projection m q
  refine ⟨A, hA, ?_⟩
  intro I K _ _ _ J _ F _ P hP hn hK hd U root difference hlin L C hL hC hLP hCP hsite
    frequency hbound c B hB hBP hcoefficients p hp hm base stride hs R S ρ δ hS hSP hρ hδ hρP hδP
    hstride H hsize hrank hR test htest T hT V hV hwidth density η hη happrox
  let pa := fun j => translate (fun i => (base i : ℝ)) (p j)
  let hma := fun j => coefficients_translate_mem (U j) (fun i => (base i : ℝ)) (p j) (hm j)
  have hpa (j) : DegreeLE (1 : I → ℕ) (j.val + 1) (pa j) :=
    degreeLE_translate (1 : I → ℕ) (fun _ => by norm_num) _ (p j) (hp j)
  have hra (j) : HasLayerSamplingRank (j.val + 1) H R (U j) (pa j) :=
    (hasLayerSamplingRank_translate_iff (fun i => (base i : ℝ)) (j.val + 1) H R (U j) (p j) (hp j)).mpr (hrank j)
  obtain ⟨D, hD, hDP, b, hb, hZ, hproj⟩ := hprojection hP hn hK hd U root difference hlin
    hL hC hLP hCP hsite frequency hbound c hB hBP hcoefficients pa hpa hma stride hs
    hS hSP hρ hδ hρP hδP hstride H hsize hra hR 0 (by simp)
    (fun s x => test s ((fun i => (base i : ℝ)) + x)) (fun s x => htest s _) T hT V hV hwidth
  refine ⟨D, hD, hDP, b, hb, hZ, ?_⟩
  intro Y _ _ _ index reconstruct houtput proxy hg ε Z hZnorm himage
  have happ (z : Option K × I → ℤ) :
      ‖(density (affineSampleCoefficientTorus U pa hma (fun k i => (z (k, i) : ℝ))) : ℂ) -
        affineCubeFourierSum frequency pa c (fun k i => (z (k, i) : ℝ))‖ ≤ η := by
    simpa only [coefficientTorusFourierSum, coefficientTorusCharacter_sample U _ pa hpa hma,
      affineCubeFourierSum] using happrox (affineSampleCoefficientTorus U pa hma (fun k i => (z (k, i) : ℝ)))
  have h := selectedResidue_covered_reconstruction_comparison U root difference D p hm frequency b c test htest base
    stride T V hV hZ (fun z => density (affineSampleCoefficientTorus U pa hma (fun k i => (z (k, i) : ℝ))))
    index reconstruct houtput proxy hg hη hZnorm (fun z _ => happ z) hproj himage
  simpa only [layeredSiteWeight_physicalCube] using h

end Erdos3.BooleanCubeKernel

end

end OAI
