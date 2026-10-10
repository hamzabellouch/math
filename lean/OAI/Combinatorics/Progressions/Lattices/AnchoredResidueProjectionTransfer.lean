import OAI.Combinatorics.Progressions.Linear.ProductOneSiteProjectionCap

namespace OAI

section

namespace Erdos3.BooleanCubeKernel

open MeasureTheory VectorPolynomial

theorem anchored_selectedResidue_oneSite_density_error {I K F : Type*} [Fintype I] [Fintype K] [Fintype F]
    (anchor : Option K × I → ℤ)
    {m : ℕ} {J : Fin m → Type*} [∀ j, Fintype (J j)] (U : ∀ j, Submodule ℝ (J j → ℝ))
    (t : K → ℤ) (difference : Fin 0 → K → ℤ)
    [MeasurableSpace (CoefficientTorus (K := K) U)] [BorelSpace (CoefficientTorus (K := K) U)]
    (frequency : F → ∀ j, (K →₀ ℕ) → J j → ℤ) (c : F → ℂ)
    (μ : Measure (CoefficientTorus (K := K) U)) [μ.IsAddLeftInvariant] [IsProbabilityMeasure μ]
    (D : CoefficientTorus (K := K) U → ℝ) {η ε : ℝ} (hη : 0 ≤ η)
    (happrox : ∀ x, ‖coefficientTorusFourierSum U frequency c x - (D x : ℂ)‖ ≤ η)
    (hD : ∀ y, Integrable (fun x => D (coefficientFiberMap U t y x)) μ)
    (p : ∀ j, VectorPolynomial I ℝ (J j → ℝ))
    (hp : ∀ j, DegreeLE (1 : I → ℕ) (j.val + 1) (p j))
    (hm : ∀ j d, coefficients (p j) d ∈ U j)
    (stride : I → ℕ) (G : Finset (ColumnResiduePattern (Option K) I stride))
    (V : Option K × I → ℝ) (hV : ∀ z, 0 < V z)
    (hZ : 0 < ∑' x, selectedResidueSmoothWeight stride G V x)
    (w : (Option K × I → ℤ) → ℂ) (hw : ∀ x, ‖w x‖ ≤ 1)
    (hprojection : ‖(∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
      (w x * affineCubeFourierSum frequency p c (fun k j => ((anchor + x) (k, j) : ℝ)))) -
      ∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
        (w x * affineCubeFourierProjection U t difference frequency p c (fun k j => ((anchor + x) (k, j) : ℝ)))‖ ≤ ε) :
    ‖(∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
      (w x * (D (affineSampleCoefficientTorus U p hm (fun k j => ((anchor + x) (k, j) : ℝ))) : ℂ))) -
      ∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) *
        (w x * ((coefficientFiberAverage U μ t D (coefficientEvaluationTorus U t
          (affineSampleCoefficientTorus U p hm (fun k j => ((anchor + x) (k, j) : ℝ)))) : ℝ) : ℂ))‖ ≤ 2 * η + ε := by
  let prob := selectedResidueFiniteLaw stride G V hV hZ
  have hmean (f : (Option K × I → ℤ) → ℂ) : prob.complexMean (fun x => f x.val) =
      ∑' x, ((selectedResidueSmoothPMF stride G V hV hZ x).toReal : ℂ) * f x :=
    selectedResidueFiniteLaw_complexMean stride G V hV hZ f
  have hw' : prob.mean (fun x => ‖w x.val‖) ≤ 1 :=
    (prob.mean_mono (fun x => hw x.val)).trans_eq (prob.mean_const 1)
  have he := oneSiteDensity_projection_error (ε := ε) U t difference frequency c μ D hη happrox p hp hm
    prob (fun x k j => ((anchor + x.val) (k, j) : ℝ)) (fun x => w x.val) (fun _ _ => hD _) hw'
    (by
      rw [hmean (fun x => w x * affineCubeFourierSum frequency p c (fun k j => ((anchor + x) (k, j) : ℝ))),
        hmean (fun x => w x * affineCubeFourierProjection U t difference frequency p c (fun k j => ((anchor + x) (k, j) : ℝ)))]
      exact hprojection)
  rw [hmean (fun x => w x * (D (affineSampleCoefficientTorus U p hm (fun k j => ((anchor + x) (k, j) : ℝ))) : ℂ)),
    hmean (fun x => w x * ((coefficientFiberAverage U μ t D (coefficientEvaluationTorus U t
      (affineSampleCoefficientTorus U p hm (fun k j => ((anchor + x) (k, j) : ℝ)))) : ℝ) : ℂ))] at he
  simpa only [mul_one] using he

end Erdos3.BooleanCubeKernel

end

end OAI
