import OAI.Analysis.Mahler.CoordinateEuclidean
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

namespace OAI

noncomputable section
open Set MeasureTheory WithLp
open scoped ENNReal
namespace MahlerStokes

/-- Interleaved real coordinates: index 2i is real and index 2i+1 imaginary. -/
def interleavedEuclidean (n : ℕ) :
    EuclideanSpace ℝ (Fin (n*2)) ≃ₗᵢ[ℝ] EuclideanSpace ℂ (Fin n) where
  toFun x := toLp 2 (fun i => ⟨x (finProdFinEquiv (i,0)), x (finProdFinEquiv (i,1))⟩)
  invFun z := toLp 2 (fun j => if (finProdFinEquiv.symm j).2 = 0 then
    (z (finProdFinEquiv.symm j).1).re else (z (finProdFinEquiv.symm j).1).im)
  left_inv x := by
    ext j
    obtain ⟨⟨i,k⟩, rfl⟩ := finProdFinEquiv.surjective j
    fin_cases k <;> simp
  right_inv z := by
    ext i; simp
  map_add' x y := by ext i; rfl
  map_smul' c x := by
    ext i : 1
    apply Complex.ext <;> simp [Complex.real_smul]
  norm_map' x := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
    rw [← Equiv.sum_comp finProdFinEquiv]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fin.sum_univ_two, Complex.sq_norm]
    simp only [Complex.normSq_apply, pow_two]
    rfl

/-- The same coordinate map on the ordinary Pi space used by the Stokes integrals. -/
def complexCoordinates (n : ℕ) :
    (Fin (n*2) → ℝ) ≃L[ℝ] EuclideanSpace ℂ (Fin n) :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n*2) => ℝ)).symm.trans
    (interleavedEuclidean n).toContinuousLinearEquiv

lemma complexCoordinates_apply (n : ℕ) (x : Fin (n*2) → ℝ) (i : Fin n) :
    complexCoordinates n x i = ⟨x (finProdFinEquiv (i,0)), x (finProdFinEquiv (i,1))⟩ := rfl

/-- Euclidean volume is transported with factor exactly one. -/
theorem measurePreserving_complexCoordinates (n : ℕ) :
    MeasurePreserving (complexCoordinates n) := by
  exact (interleavedEuclidean n).measurePreserving.comp
    (PiLp.volume_preserving_toLp (Fin (n*2)))

/-- The coordinate squared radius is exactly the complex Euclidean squared norm. -/
theorem norm_complexCoordinates_sq (n : ℕ) (x : Fin (n*2) → ℝ) :
    ‖complexCoordinates n x‖^2 = radiusSq x := by
  rw [radiusSq_eq_euclidean_norm_sq]
  exact congrArg (fun t : ℝ => t^2) ((interleavedEuclidean n).norm_map _)

/-- The coordinate map sends the ordered real basis to x_i,y_i without a
sign or scale change. -/
theorem complexCoordinates_basis (n : ℕ) (i : Fin n) (b : Fin 2) :
    complexCoordinates n (Pi.single (finProdFinEquiv (i,b)) 1) =
      EuclideanSpace.single i (if b = 0 then 1 else Complex.I) := by
  ext j : 1
  rw [complexCoordinates_apply]
  by_cases hij : i = j
  · subst j
    fin_cases b <;> simp <;> rfl
  · have hji : j ≠ i := Ne.symm hij
    fin_cases b <;> simp [hji] <;> rfl

 theorem interleavedIndex_val (n : ℕ) (i : Fin n) (b : Fin 2) :
    (finProdFinEquiv (i,b)).val = 2*i.val+b.val := by
  change b.val+2*i.val = _
  omega

/-- Ordinary real density integrals in the explicit interleaved coordinates. -/
theorem setIntegral_complexCoordinates (n : ℕ) (S : Set (EuclideanSpace ℂ (Fin n)))
    (f : EuclideanSpace ℂ (Fin n) → ℝ) :
    (∫ x in (complexCoordinates n) ⁻¹' S, f (complexCoordinates n x)) = ∫ z in S, f z :=
  (measurePreserving_complexCoordinates n).setIntegral_preimage_emb
    (complexCoordinates n).toHomeomorph.toMeasurableEquiv.measurableEmbedding f S

/-- Nonnegative mass integrals transport even when the mass is infinite. -/
theorem setLIntegral_complexCoordinates (n : ℕ) (S : Set (EuclideanSpace ℂ (Fin n)))
    (f : EuclideanSpace ℂ (Fin n) → ℝ≥0∞) :
    (∫⁻ x in (complexCoordinates n) ⁻¹' S, f (complexCoordinates n x)) = ∫⁻ z in S, f z :=
  (measurePreserving_complexCoordinates n).setLIntegral_comp_preimage_emb
    (complexCoordinates n).toHomeomorph.toMeasurableEquiv.measurableEmbedding f S

 theorem coordBall_complexCoordinates (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    coordBall (n*2) r = (complexCoordinates n) ⁻¹' Metric.ball 0 r := by
  ext x
  simp only [mem_preimage, Metric.mem_ball, dist_zero_right]
  change radiusSq x < r^2 ↔ ‖complexCoordinates n x‖ < r
  rw [← norm_complexCoordinates_sq]
  exact sq_lt_sq₀ (norm_nonneg _) hr

 theorem coordClosedBall_complexCoordinates (n : ℕ) {r : ℝ} (hr : 0 ≤ r) :
    coordClosedBall (n*2) r = (complexCoordinates n) ⁻¹' Metric.closedBall 0 r := by
  ext x
  simp only [mem_preimage, Metric.mem_closedBall, dist_zero_right]
  change radiusSq x ≤ r^2 ↔ ‖complexCoordinates n x‖ ≤ r
  rw [← norm_complexCoordinates_sq]
  exact sq_le_sq₀ (norm_nonneg _) hr

end MahlerStokes

end

end OAI
