import Mathlib
import OAI.Geometry.PrescribedRicci.MatrixDifferentialNew

namespace OAI

/-! Kahler Cofactor Divergence. -/

noncomputable section
open Matrix Filter Set Topology
open scoped ContDiff ComplexOrder Matrix.Norms.Elementwise
namespace Anticanonical.SourceSmooth
namespace KaehlerMetric
variable {d : ℕ} {X : Type*} [TopologicalSpace X] {A : ComplexAtlas d X}

abbrev coordinateVector (j : Fin d) : Coordinates d := Pi.single j 1

lemma pair_coordinate (M : Matrix (Fin d) (Fin d) ℂ) (j k : Fin d) :
    star (coordinateVector j) ⬝ᵥ (M *ᵥ coordinateVector k) = M j k := by
  change star (Pi.single j 1) ⬝ᵥ (M *ᵥ Pi.single k 1) = _
  rw [Pi.star_single, star_one, single_dotProduct, one_mul]
  change M j ⬝ᵥ Pi.single k 1 = M j k
  rw [dotProduct_single, mul_one]

lemma fundamentalForm_coordinate (M : Matrix (Fin d) (Fin d) ℂ) (j k : Fin d) :
    ComplexAtlas.fundamentalForm M (coordinateVector j) (coordinateVector k) = (M j k).im := by
  simp only [ComplexAtlas.fundamentalForm, pair_coordinate]

lemma fundamentalForm_I_coordinate (M : Matrix (Fin d) (Fin d) ℂ) (j k : Fin d) :
    ComplexAtlas.fundamentalForm M (Complex.I • coordinateVector j) (coordinateVector k) =
      -(M j k).re := by
  simp only [ComplexAtlas.fundamentalForm, star_smul, smul_dotProduct, pair_coordinate]
  simp [smul_eq_mul]

lemma fundamentalForm_coordinate_I (M : Matrix (Fin d) (Fin d) ℂ) (j k : Fin d) :
    ComplexAtlas.fundamentalForm M (coordinateVector j) (Complex.I • coordinateVector k) =
      (M j k).re := by
  simp only [ComplexAtlas.fundamentalForm, mulVec_smul, dotProduct_smul, pair_coordinate]
  simp [smul_eq_mul]

lemma fundamentalForm_I_I (M : Matrix (Fin d) (Fin d) ℂ) (j k : Fin d) :
    ComplexAtlas.fundamentalForm M (Complex.I • coordinateVector j)
      (Complex.I • coordinateVector k) = (M j k).im := by
  simp only [ComplexAtlas.fundamentalForm, star_smul, mulVec_smul, smul_dotProduct,
    dotProduct_smul, pair_coordinate]
  simp [smul_eq_mul, Complex.mul_im]

def fundamentalFormCLM (u v : Coordinates d) : Matrix (Fin d) (Fin d) ℂ →L[ℝ] ℝ :=
  LinearMap.toContinuousLinearMap
    { toFun := fun M => ComplexAtlas.fundamentalForm M u v
      map_add' := by
        intro M N
        exact fundamentalForm_add M N u v
      map_smul' := by
        intro c M
        simp [ComplexAtlas.fundamentalForm, smul_mulVec, dotProduct_smul] }

lemma fundamentalForm_fderiv (g : KaehlerMetric A) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target) (u v w : Coordinates d) :
    fderiv ℝ (fun y => ComplexAtlas.fundamentalForm (g.matrix i y) v w) z u =
      ComplexAtlas.fundamentalForm (fderiv ℝ (g.matrix i) z u) v w := by
  have hg := ((g.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz)).differentiableAt
    (by simp)
  exact congrArg (fun L : Coordinates d →L[ℝ] ℝ => L u)
    (((fundamentalFormCLM v w).hasFDerivAt.comp z hg.hasFDerivAt).fderiv)

lemma derivative_closed (g : KaehlerMetric A) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target) (u v w : Coordinates d) :
    ComplexAtlas.fundamentalForm (fderiv ℝ (g.matrix i) z u) v w +
      ComplexAtlas.fundamentalForm (fderiv ℝ (g.matrix i) z v) w u +
      ComplexAtlas.fundamentalForm (fderiv ℝ (g.matrix i) z w) u v = 0 := by
  simpa only [g.fundamentalForm_fderiv i hz] using g.closed i z hz u v w

def conjugateTransposeCLM : Matrix (Fin d) (Fin d) ℂ →L[ℝ] Matrix (Fin d) (Fin d) ℂ :=
  LinearMap.toContinuousLinearMap
    { toFun := Matrix.conjTranspose
      map_add' := Matrix.conjTranspose_add
      map_smul' := by intro c M; simp }

lemma derivative_hermitian (g : KaehlerMetric A) (i : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart i).target) (u : Coordinates d) :
    (fderiv ℝ (g.matrix i) z u).IsHermitian := by
  have he : (fun y => (g.matrix i y)ᴴ) =ᶠ[nhds z] g.matrix i := by
    filter_upwards [(A.chart i).open_target.mem_nhds hz] with y hy
    exact (g.positive i y hy).isHermitian
  have hg := ((g.smooth i).contDiffAt ((A.chart i).open_target.mem_nhds hz)).differentiableAt
    (by simp)
  have hd := congrArg (fun L : Coordinates d →L[ℝ] Matrix (Fin d) (Fin d) ℂ => L u)
    he.fderiv_eq
  have hs := ((conjugateTransposeCLM (d := d)).hasFDerivAt.comp z hg.hasFDerivAt).fderiv
  have hs' : fderiv ℝ (fun y => (g.matrix i y)ᴴ) z u =
      (fderiv ℝ (g.matrix i) z u)ᴴ :=
    congrArg (fun L : Coordinates d →L[ℝ] Matrix (Fin d) (Fin d) ℂ => L u) hs
  exact hs'.symm.trans hd

def barDerivative (f : Coordinates d → Matrix (Fin d) (Fin d) ℂ)
    (z : Coordinates d) (j : Fin d) : Matrix (Fin d) (Fin d) ℂ :=
  (2 : ℂ)⁻¹ • (fderiv ℝ f z (coordinateVector j) +
    Complex.I • fderiv ℝ f z (Complex.I • coordinateVector j))

lemma barDerivative_symm (g : KaehlerMetric A) (a : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart a).target) (i j k : Fin d) :
    barDerivative (g.matrix a) z i j k = barDerivative (g.matrix a) z j i k := by
  have h1 := g.derivative_closed a hz (coordinateVector i) (coordinateVector j)
    (Complex.I • coordinateVector k)
  have h2 := g.derivative_closed a hz (Complex.I • coordinateVector i)
    (Complex.I • coordinateVector j) (Complex.I • coordinateVector k)
  have h3 := g.derivative_closed a hz (coordinateVector i) (coordinateVector j)
    (coordinateVector k)
  have h4 := g.derivative_closed a hz (Complex.I • coordinateVector i)
    (Complex.I • coordinateVector j) (coordinateVector k)
  simp only [fundamentalForm_coordinate, fundamentalForm_I_coordinate,
    fundamentalForm_coordinate_I, fundamentalForm_I_I] at h1 h2 h3 h4
  have hr := congrArg Complex.re ((g.derivative_hermitian a hz (coordinateVector j)).apply i k)
  have hi := congrArg Complex.im ((g.derivative_hermitian a hz (coordinateVector j)).apply i k)
  have hIr := congrArg Complex.re
    ((g.derivative_hermitian a hz (Complex.I • coordinateVector j)).apply i k)
  have hIi := congrArg Complex.im
    ((g.derivative_hermitian a hz (Complex.I • coordinateVector j)).apply i k)
  simp only [Complex.star_def, Complex.conj_re, Complex.conj_im] at hr hi hIr hIi
  apply Complex.ext
  · simp only [barDerivative, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
    norm_num
    linarith
  · simp only [barDerivative, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
    norm_num
    linarith

lemma barDerivative_comp {f : Coordinates d → Matrix (Fin d) (Fin d) ℂ}
    {F : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ}
    {z : Coordinates d} (hf : DifferentiableAt ℝ f z)
    (hF : DifferentiableAt ℂ F (f z)) (j : Fin d) :
    barDerivative (F ∘ f) z j = fderiv ℂ F (f z) (barDerivative f z j) := by
  have hd := ((hF.hasFDerivAt.restrictScalars ℝ).comp z hf.hasFDerivAt).fderiv
  unfold barDerivative
  have h1 := congrArg (fun L : Coordinates d →L[ℝ] Matrix (Fin d) (Fin d) ℂ =>
    L (coordinateVector j)) hd
  have h2 := congrArg (fun L : Coordinates d →L[ℝ] Matrix (Fin d) (Fin d) ℂ =>
    L (Complex.I • coordinateVector j)) hd
  calc
    _ = (2 : ℂ)⁻¹ • (fderiv ℂ F (f z) (fderiv ℝ f z (coordinateVector j)) +
        Complex.I • fderiv ℂ F (f z) (fderiv ℝ f z (Complex.I • coordinateVector j))) :=
      congrArg₂ (fun U V : Matrix (Fin d) (Fin d) ℂ => (2 : ℂ)⁻¹ • (U + Complex.I • V)) h1 h2
    _ = _ := by
      simp only [map_smul (fderiv ℂ F (f z)), map_add (fderiv ℂ F (f z))]

private lemma sum_swap_outer_inner (f : Fin d → Fin d → Fin d → ℂ) :
    ∑ i, ∑ j, ∑ k, f i j k = ∑ k, ∑ j, ∑ i, f i j k := by
  calc
    _ = ∑ j, ∑ i, ∑ k, f i j k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, f i j k := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

lemma cofactor_cancellation (B : Matrix (Fin d) (Fin d) ℂ)
    (C : Fin d → Matrix (Fin d) (Fin d) ℂ)
    (hC : ∀ i j k, C i j k = C j i k) (k : Fin d) :
    ∑ i, ((B * C i).trace * B k i - (B * C i * B) k i) = 0 := by
  rw [Finset.sum_sub_distrib, sub_eq_zero]
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_mul]
  rw [sum_swap_outer_inner]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  rw [hC l i j]
  ring

theorem weightedInverse_divergence (g : KaehlerMetric A) (a : Fin A.count)
    {z : Coordinates d} (hz : z ∈ (A.chart a).target) (k : Fin d) :
    ∑ i, barDerivative (MongeAmpere.weightedInverse ∘ g.matrix a) z i k i = 0 := by
  have hg := ((g.smooth a).contDiffAt ((A.chart a).open_target.mem_nhds hz)).differentiableAt
    (by simp)
  have hdet : IsUnit (g.matrix a z).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt (g.positive a z hz).det_pos)
  simp only [barDerivative_comp hg (MongeAmpere.differentiableAt_weightedInverse _ hdet),
    MongeAmpere.fderiv_weightedInverse_apply _ _ hdet, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul]
  rw [← Finset.mul_sum]
  rw [cofactor_cancellation _ _ (g.barDerivative_symm a hz)]
  exact mul_zero _

end KaehlerMetric
end Anticanonical.SourceSmooth

end

end OAI
