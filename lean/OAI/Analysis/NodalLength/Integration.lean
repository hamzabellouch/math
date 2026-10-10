import OAI.Analysis.NodalLength.Model

namespace OAI

noncomputable section
open scoped ContDiff Bundle ENNReal
open Bundle Manifold MeasureTheory

namespace SharpNodal
namespace Carleman

open scoped ContDiff Topology
open MeasureTheory

abbrev Smooth (f : Plane → ℝ) : Prop := ContDiff ℝ ∞ f

lemma smooth_partial {f : Plane → ℝ} (hf : Smooth f) (i : Fin 2) :
    Smooth (coordPartial f i) := by
  exact (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).clm_apply contDiff_const

lemma compact_partial {f : Plane → ℝ} (hf : HasCompactSupport f) (i : Fin 2) :
    HasCompactSupport (coordPartial f i) :=
  hf.fderiv_apply ℝ (EuclideanSpace.single i 1)

lemma partial_mul {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (i : Fin 2) (x : Plane) :
    coordPartial (fun y => f y * g y) i x =
      coordPartial f i x * g x + f x * coordPartial g i x := by
  unfold coordPartial
  rw [fderiv_fun_mul (hf.differentiable (by simp)).differentiableAt
    (hg.differentiable (by simp)).differentiableAt]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

lemma integrable_mul_compact_right {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport g) : Integrable (fun x => f x * g x) := by
  exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_left

lemma integral_mul_partial {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport g) (i : Fin 2) :
    (∫ x, f x * coordPartial g i x) = -(∫ x, coordPartial f i x * g x) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact integrable_mul_compact_right (smooth_partial hf i) hg hc
  · exact integrable_mul_compact_right hf (smooth_partial hg i) (compact_partial hc i)
  · exact integrable_mul_compact_right hf hg hc
  · intro x _
    exact (hf.differentiable (by simp)).differentiableAt
  · intro x _
    exact (hg.differentiable (by simp)).differentiableAt

lemma partial_partial {f : Plane → ℝ} (hf : Smooth f) (i j : Fin 2) (x : Plane) :
    coordPartial (coordPartial f i) j x =
      coordPartial (coordPartial f j) i x := by
  have hdf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (by simp : (∞ : ℕ∞ω) + 1 ≤ (∞ : ℕ∞ω))).differentiable
      (by simp)
  have h (a b : Fin 2) : coordPartial (coordPartial f a) b x =
      fderiv ℝ (fderiv ℝ f) x (EuclideanSpace.single b 1) (EuclideanSpace.single a 1) := by
    unfold coordPartial
    rw [fderiv_clm_apply hdf.differentiableAt (differentiableAt_const _)]
    simp
  rw [h i j, h j i]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))).eq _ _

lemma partial_add {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (i : Fin 2) (x : Plane) :
    coordPartial (fun y => f y + g y) i x =
      coordPartial f i x + coordPartial g i x := by
  unfold coordPartial
  rw [fderiv_fun_add (hf.differentiable (by simp)).differentiableAt
    (hg.differentiable (by simp)).differentiableAt]
  rfl

lemma partial_const_mul {f : Plane → ℝ} (hf : Smooth f) (c : ℝ)
    (i : Fin 2) (x : Plane) :
    coordPartial (fun y => c * f y) i x = c * coordPartial f i x := by
  unfold coordPartial
  rw [fderiv_const_mul (hf.differentiable (by simp)).differentiableAt]
  rfl

lemma integral_coeff_mul_partial_square {a v : Plane → ℝ}
    (ha : Smooth a) (hv : Smooth v) (hc : HasCompactSupport v) (i : Fin 2) :
    2 * (∫ x, a x * v x * coordPartial v i x) =
      -(∫ x, coordPartial a i x * (v x * v x)) := by
  have h := integral_mul_partial ha (hv.mul hv) hc.mul_right i
  calc
    2 * (∫ x, a x * v x * coordPartial v i x) =
        ∫ x, a x * coordPartial (fun y => v y * v y) i x := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [partial_mul hv hv]
      ring
    _ = _ := h

lemma integrable_mul_compact_left {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport f) : Integrable (fun x => f x * g x) := by
  exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_right

lemma integral_partial_mul {f g : Plane → ℝ} (hf : Smooth f) (hg : Smooth g)
    (hc : HasCompactSupport f) (i : Fin 2) :
    (∫ x, coordPartial f i x * g x) = -(∫ x, f x * coordPartial g i x) := by
  simpa only [mul_comm] using integral_mul_partial hg hf hc i

lemma integral_partial_mul_mul {f g h : Plane → ℝ}
    (hf : Smooth f) (hg : Smooth g) (hh : Smooth h) (hc : HasCompactSupport f)
    (i : Fin 2) :
    (∫ x, coordPartial f i x * g x * h x) =
      -(∫ x, f x * coordPartial g i x * h x) -
        (∫ x, f x * g x * coordPartial h i x) := by
  have hI₁ := integrable_mul_compact_left (hf.mul (smooth_partial hg i)) hh
    hc.mul_right
  have hI₂ := integrable_mul_compact_left (hf.mul hg) (smooth_partial hh i) hc.mul_right
  calc
    (∫ x, coordPartial f i x * g x * h x) =
        ∫ x, coordPartial f i x * (g x * h x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      ring
    _ = -(∫ x, f x * coordPartial (fun y => g y * h y) i x) :=
      integral_partial_mul hf (hg.mul hh) hc i
    _ = -(∫ x, (f x * coordPartial g i x * h x) +
        (f x * g x * coordPartial h i x)) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      rw [partial_mul hg hh]
      ring
    _ = _ := by rw [integral_add hI₁ hI₂]; ring

lemma laplacian_transport_pair {T v : Plane → ℝ}
    (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) (i j : Fin 2) :
    -4 * (∫ x, coordPartial (coordPartial v i) i x *
        coordPartial T j x * coordPartial v j x) -
      2 * (∫ x, coordPartial (coordPartial v i) i x *
        coordPartial (coordPartial T j) j x * v x) =
      4 * (∫ x, coordPartial (coordPartial T j) i x *
        coordPartial v i x * coordPartial v j x) -
      (∫ x, coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x *
        (v x * v x)) := by
  have h1 := integral_partial_mul_mul (smooth_partial hv i) (smooth_partial hT j)
    (smooth_partial hv j) (compact_partial hc i) i
  have h2 := integral_partial_mul_mul (smooth_partial hv i)
    (smooth_partial (smooth_partial hT j) j) hv (compact_partial hc i) i
  have h3 := integral_coeff_mul_partial_square (smooth_partial hT j)
    (smooth_partial hv i) (compact_partial hc i) j
  have h4 := integral_coeff_mul_partial_square
    (smooth_partial (smooth_partial (smooth_partial hT j) j) i) hv hc i
  have hmix : coordPartial (coordPartial v j) i = coordPartial (coordPartial v i) j :=
    funext (partial_partial hv j i)
  rw [hmix] at h1
  simp only [mul_comm, mul_left_comm, mul_assoc] at h1 h2 h3 h4 ⊢
  linarith only [h1, h2, h3, h4]

lemma multiplication_transport_pair {a T v : Plane → ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v)
    (i : Fin 2) :
    -4 * (∫ x, a x * coordPartial T i x * v x * coordPartial v i x) -
      2 * (∫ x, a x * coordPartial (coordPartial T i) i x * (v x * v x)) =
      2 * (∫ x, coordPartial a i x * coordPartial T i x * (v x * v x)) := by
  have h := integral_coeff_mul_partial_square (ha.mul (smooth_partial hT i)) hv hc i
  have hI₁ := integrable_mul_compact_right
    ((smooth_partial ha i).mul (smooth_partial hT i)) (hv.mul hv) hc.mul_right
  have hI₂ := integrable_mul_compact_right
    (ha.mul (smooth_partial (smooth_partial hT i) i)) (hv.mul hv) hc.mul_right
  have hsplit : (∫ x, coordPartial (fun y => a y * coordPartial T i y) i x *
      (v x * v x)) =
      (∫ x, coordPartial a i x * coordPartial T i x * (v x * v x)) +
      (∫ x, a x * coordPartial (coordPartial T i) i x * (v x * v x)) := by
    rw [← integral_add hI₁ hI₂]
    apply integral_congr_ae
    filter_upwards [] with x
    rw [partial_mul ha (smooth_partial hT i)]
    ring
  rw [hsplit] at h
  linarith only [h]

def euclideanLaplacian (f : Plane → ℝ) (x : Plane) : ℝ :=
  ∑ i : Fin 2, coordPartial (coordPartial f i) i x

def skewPart (T v : Plane → ℝ) (x : Plane) : ℝ :=
  ∑ i : Fin 2, (-2 * coordPartial T i x * coordPartial v i x -
    coordPartial (coordPartial T i) i x * v x)

lemma smooth_laplacian {f : Plane → ℝ} (hf : Smooth f) :
    Smooth (euclideanLaplacian f) :=
  ContDiff.sum fun i _ => smooth_partial (smooth_partial hf i) i

lemma compact_laplacian {f : Plane → ℝ} (hf : HasCompactSupport f) :
    HasCompactSupport (euclideanLaplacian f) := by
  convert (HasCompactSupport.finset_sum (s := Finset.univ)
      (fun i _ => compact_partial (compact_partial hf i) i)) using 1
  rfl

lemma smooth_skew {T v : Plane → ℝ} (hT : Smooth T) (hv : Smooth v) :
    Smooth (skewPart T v) := by
  apply ContDiff.sum
  intro i _
  exact ((contDiff_const.mul (smooth_partial hT i)).mul (smooth_partial hv i)).sub
    ((smooth_partial (smooth_partial hT i) i).mul hv)

lemma compact_skew {T v : Plane → ℝ} (hv : HasCompactSupport v) :
    HasCompactSupport (skewPart T v) := by
  convert (HasCompactSupport.finset_sum (s := Finset.univ) (fun i _ =>
      ((compact_partial hv i).mul_left (f := fun x => -2 * coordPartial T i x)).sub
        (hv.mul_left (f := coordPartial (coordPartial T i) i)))) using 1
  rfl

lemma integral_sum_mul {ι : Type*} (s : Finset ι) {f : ι → Plane → ℝ} {g : Plane → ℝ}
    (hf : ∀ i ∈ s, Smooth (f i)) (hg : Smooth g) (hc : HasCompactSupport g) :
    (∫ x, (∑ i ∈ s, f i x) * g x) = ∑ i ∈ s, ∫ x, f i x * g x := by
  simp_rw [Finset.sum_mul]
  exact integral_finsetSum s fun i hi => integrable_mul_compact_right (hf i hi) hg hc

lemma integral_mul_sum {ι : Type*} (s : Finset ι) {f : Plane → ℝ} {g : ι → Plane → ℝ}
    (hf : Smooth f) (hg : ∀ i ∈ s, Smooth (g i))
    (hc : ∀ i ∈ s, HasCompactSupport (g i)) :
    (∫ x, f x * (∑ i ∈ s, g i x)) = ∑ i ∈ s, ∫ x, f x * g i x := by
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum s fun i hi => integrable_mul_compact_right hf (hg i hi) (hc i hi)

lemma integral_skew_component {f T v : Plane → ℝ}
    (hf : Smooth f) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v)
    (i : Fin 2) :
    2 * (∫ x, f x * (-2 * coordPartial T i x * coordPartial v i x -
      coordPartial (coordPartial T i) i x * v x)) =
    -4 * (∫ x, f x * coordPartial T i x * coordPartial v i x) -
      2 * (∫ x, f x * coordPartial (coordPartial T i) i x * v x) := by
  have hI₁ := integrable_mul_compact_right (hf.mul (smooth_partial hT i))
    (smooth_partial hv i) (compact_partial hc i)
  have hI₂ := integrable_mul_compact_right
    (hf.mul (smooth_partial (smooth_partial hT i) i)) hv hc
  have hF : (∫ x, f x * (-2 * coordPartial T i x * coordPartial v i x -
      coordPartial (coordPartial T i) i x * v x)) =
      -2 * (∫ x, f x * coordPartial T i x * coordPartial v i x) -
      (∫ x, f x * coordPartial (coordPartial T i) i x * v x) := by
    calc
      _ = ∫ x, -2 * (f x * coordPartial T i x * coordPartial v i x) -
          f x * coordPartial (coordPartial T i) i x * v x := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := by rw [integral_sub (hI₁.const_mul (-2)) hI₂, integral_const_mul]
  rw [hF]
  ring

lemma integral_skew {f T v : Plane → ℝ}
    (hf : Smooth f) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) :
    2 * (∫ x, f x * skewPart T v x) =
      ∑ i : Fin 2, (-4 * (∫ x, f x * coordPartial T i x * coordPartial v i x) -
        2 * (∫ x, f x * coordPartial (coordPartial T i) i x * v x)) := by
  unfold skewPart
  rw [integral_mul_sum Finset.univ hf
    (fun i _ => ((contDiff_const.mul (smooth_partial hT i)).mul
      (smooth_partial hv i)).sub ((smooth_partial (smooth_partial hT i) i).mul hv))
    (fun i _ => ((compact_partial hc i).mul_left).sub hc.mul_left)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_skew_component hf hT hv hc i

lemma laplacian_transport {T v : Plane → ℝ}
    (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) :
    2 * (∫ x, euclideanLaplacian v x * skewPart T v x) =
      ∑ j : Fin 2, ∑ i : Fin 2,
        (4 * (∫ x, coordPartial (coordPartial T j) i x *
          coordPartial v i x * coordPartial v j x) -
        (∫ x, coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x *
          (v x * v x))) := by
  rw [integral_skew (smooth_laplacian hv) hT hv hc]
  apply Finset.sum_congr rfl
  intro j _
  have h1 : (∫ x, euclideanLaplacian v x * coordPartial T j x * coordPartial v j x) =
      ∑ i : Fin 2, ∫ x, coordPartial (coordPartial v i) i x *
        coordPartial T j x * coordPartial v j x := by
    simp only [mul_assoc, euclideanLaplacian]
    exact integral_sum_mul Finset.univ
      (fun i _ => smooth_partial (smooth_partial hv i) i)
      ((smooth_partial hT j).mul (smooth_partial hv j)) (compact_partial hc j).mul_left
  have h2 : (∫ x, euclideanLaplacian v x * coordPartial (coordPartial T j) j x * v x) =
      ∑ i : Fin 2, ∫ x, coordPartial (coordPartial v i) i x *
        coordPartial (coordPartial T j) j x * v x := by
    simp only [mul_assoc, euclideanLaplacian]
    exact integral_sum_mul Finset.univ
      (fun i _ => smooth_partial (smooth_partial hv i) i)
      ((smooth_partial (smooth_partial hT j) j).mul hv) hc.mul_left
  rw [h1, h2, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact laplacian_transport_pair hT hv hc i j

lemma multiplication_transport {a T v : Plane → ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) :
    2 * (∫ x, (a x * v x) * skewPart T v x) =
      ∑ i : Fin 2, 2 * (∫ x, coordPartial a i x * coordPartial T i x * (v x * v x)) := by
  rw [integral_skew (ha.mul hv) hT hv hc]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    multiplication_transport_pair ha hT hv hc i

lemma transport_commutator {a T v : Plane → ℝ}
    (ha : Smooth a) (hT : Smooth T) (hv : Smooth v) (hc : HasCompactSupport v) :
    2 * (∫ x, (euclideanLaplacian v x + a x * v x) * skewPart T v x) =
      (∑ j : Fin 2, ∑ i : Fin 2,
        (4 * (∫ x, coordPartial (coordPartial T j) i x *
          coordPartial v i x * coordPartial v j x) -
        (∫ x, coordPartial (coordPartial (coordPartial (coordPartial T j) j) i) i x *
          (v x * v x)))) +
      ∑ i : Fin 2, 2 * (∫ x, coordPartial a i x * coordPartial T i x * (v x * v x)) := by
  have hI₁ := integrable_mul_compact_right (smooth_laplacian hv) (smooth_skew hT hv)
    (compact_skew hc)
  have hI₂ := integrable_mul_compact_right (ha.mul hv) (smooth_skew hT hv)
    (compact_skew hc)
  simp_rw [add_mul]
  rw [integral_add hI₁ hI₂, mul_add, laplacian_transport hT hv hc,
    multiplication_transport ha hT hv hc]


end Carleman
end SharpNodal

end

end OAI
