import OAI.Geometry.RCD.Metric.FiniteSignedRadon
import OAI.Geometry.RCD.Coordinates.CoordinateBilinear

namespace OAI

/-! # The positive finite-dimensional density of a Bochner measure

The density describes only the absolutely continuous part. The original
positive measure, including its singular part, is retained.
-/

open Set Filter MeasureTheory TopologicalSpace
open scoped BigOperators

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] {m : ℕ}

def bochnerRadonDensity (M : PositiveBilinearMeasure X (Euclidean m)) (x : X) :
    Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] ℝ :=
  coordinateBilinear (fun i j =>
    (M.bilinear (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)).rnDeriv μ x)

theorem bochnerRadonDensity_rep (M : PositiveBilinearMeasure X (Euclidean m))
    (a b : Euclidean m) :
    (M.bilinear a b).rnDeriv μ =ᵐ[μ] fun x => bochnerRadonDensity μ M x a b := by
  classical
  let e (i : Fin m) : Euclidean m := EuclideanSpace.single i 1
  have hform : coordinateBilinear (fun i j => M.bilinear (e i) (e j))=M.bilinear := by
    apply (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext
    intro i
    apply (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext
    intro j
    simp [coordinateBilinear,EuclideanSpace.basisFun_apply,e]
  have he := congrArg (fun F : Euclidean m →ₗ[ℝ] Euclidean m →ₗ[ℝ] SignedMeasure X => F a b) hform
  rw [coordinateBilinear_apply] at he
  rw [← he]
  have hi (i : Fin m) := signed_rnDeriv_sum_smul μ Finset.univ (fun j => a i*b j)
    (fun j => M.bilinear (e i) (e j))
  filter_upwards [signed_rnDeriv_sum μ Finset.univ
    (fun i => ∑ j : Fin m, (a i*b j) • M.bilinear (e i) (e j)),ae_all_iff.mpr hi] with x hx hy
  rw [hx]
  simp only [bochnerRadonDensity,coordinateBilinear_apply,smul_eq_mul]
  exact Finset.sum_congr rfl (fun i _ => hy i)

omit [SigmaFinite μ] in
theorem bochnerRadonDensity_symmetric (M : PositiveBilinearMeasure X (Euclidean m))
    (x : X) (a b : Euclidean m) :
    bochnerRadonDensity μ M x a b=bochnerRadonDensity μ M x b a := by
  apply coordinateBilinear_symmetric
  intro i j
  rw [M.symmetric]

omit [SigmaFinite μ] in
private theorem bochner_diagonal_rnDeriv_nonneg (M : PositiveBilinearMeasure X (Euclidean m))
    (a : Euclidean m) : ∀ᵐ x ∂μ, 0≤(M.bilinear a a).rnDeriv μ x := by
  let j : JordanDecomposition X := ⟨M.measure a,0,Measure.MutuallySingular.zero_right⟩
  have hj : (M.bilinear a a).toJordanDecomposition=j := by
    apply SignedMeasure.toJordanDecomposition_eq
    simpa only [j,JordanDecomposition.toSignedMeasure,Measure.toSignedMeasure_zero,sub_zero] using
      (M.measure_toSignedMeasure a).symm
  filter_upwards [Measure.rnDeriv_zero μ] with x hx
  change 0≤((M.bilinear a a).toJordanDecomposition.posPart.rnDeriv μ x).toReal-
    ((M.bilinear a a).toJordanDecomposition.negPart.rnDeriv μ x).toReal
  rw [hj]
  change 0≤((M.measure a).rnDeriv μ x).toReal-((0 : Measure X).rnDeriv μ x).toReal
  rw [hx]
  simpa only [Pi.zero_apply,ENNReal.toReal_zero,sub_zero] using ENNReal.toReal_nonneg

/-- One null set suffices for every real direction in the finite span. -/
theorem bochnerRadonDensity_nonneg (M : PositiveBilinearMeasure X (Euclidean m)) :
    ∀ᵐ x ∂μ, ∀ a : Euclidean m, 0≤bochnerRadonDensity μ M x a a := by
  classical
  have hfixed (a : Euclidean m) : ∀ᵐ x ∂μ, 0≤bochnerRadonDensity μ M x a a := by
    filter_upwards [bochner_diagonal_rnDeriv_nonneg μ M a,bochnerRadonDensity_rep μ M a a] with x hx he
    rwa [← he]
  obtain ⟨D,hD,hdense⟩ := exists_countable_dense (Euclidean m)
  let : Countable D := hD.to_subtype
  filter_upwards [ae_all_iff.mpr (fun a : D => hfixed a)] with x hx
  have hc : Continuous (fun a : Euclidean m => bochnerRadonDensity μ M x a a) := by
    simp only [bochnerRadonDensity,coordinateBilinear_apply,smul_eq_mul]
    fun_prop
  have hclosed : IsClosed {a : Euclidean m | 0≤bochnerRadonDensity μ M x a a} :=
    isClosed_le continuous_const hc
  have hsub : D ⊆ {a : Euclidean m | 0≤bochnerRadonDensity μ M x a a} :=
    fun a ha => hx ⟨a,ha⟩
  have hall := closure_minimal hsub hclosed
  rw [hdense.closure_eq] at hall
  exact fun a => hall (mem_univ a)

end RegularPointCoordinates

end

end OAI
