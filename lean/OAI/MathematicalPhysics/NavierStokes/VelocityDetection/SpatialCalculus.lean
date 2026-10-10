import OAI.MathematicalPhysics.NavierStokes.VelocityDetection.SpatialDTranslate

namespace OAI

noncomputable section
namespace VelocityDetection.SpatialCalculus
open scoped BigOperators Topology ContDiff
open Set Function Filter
open MeasureTheory

abbrev partialD {n : ℕ} (i : Fin n) (f : Coord n → ℝ) : Coord n → ℝ :=
  spatialD i (fun _ => f) 0

theorem partialD_eq_fderiv {n : ℕ} (i : Fin n) {f : Coord n → ℝ}
    (hf : Differentiable ℝ f) (X : Coord n) :
    partialD i f X = fderiv ℝ f X (Pi.single i 1) := spatialD_eq_fderiv i 0 X (hf X)

theorem continuous_partialD {n : ℕ} (i : Fin n) {f : Coord n → ℝ}
    (hf : ContDiff ℝ 1 f) : Continuous (partialD i f) := by
  have heq : partialD i f = fun X => fderiv ℝ f X (Pi.single i 1) :=
    funext (partialD_eq_fderiv i (hf.differentiable (by norm_num)))
  rw [heq]
  exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem contDiff_partialD {n : ℕ} (i : Fin n) {f : Coord n → ℝ}
    (hf : ContDiff ℝ 2 f) : ContDiff ℝ 1 (partialD i f) := by
  have heq : partialD i f = fun X => fderiv ℝ f X (Pi.single i 1) :=
    funext (partialD_eq_fderiv i (hf.differentiable (by norm_num)))
  rw [heq]
  exact (hf.fderiv_right (show (1 : ℕ∞ω) + 1 ≤ 2 by norm_num)).clm_apply contDiff_const

theorem compactSupport_partialD {n : ℕ} (i : Fin n) {f : Coord n → ℝ}
    (hf : Differentiable ℝ f) (hfc : HasCompactSupport f) :
    HasCompactSupport (partialD i f) := by
  have heq : partialD i f = fun X => fderiv ℝ f X (Pi.single i 1) :=
    funext (partialD_eq_fderiv i hf)
  rw [heq]
  exact hfc.fderiv_apply ℝ _

theorem partialD_mul {n : ℕ} (i : Fin n) {f g : Coord n → ℝ}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (X : Coord n) :
    partialD i (fun Y => f Y * g Y) X = partialD i f X * g X + f X * partialD i g X := by
  change partialD i (f * g) X = _
  simp only [partialD_eq_fderiv i (hf.mul hg), partialD_eq_fderiv i hf,
    partialD_eq_fderiv i hg]
  change fderiv ℝ (f * g) X (Pi.single i 1) = _
  rw [fderiv_mul (hf X) (hg X)]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem continuous_laplacian {n : ℕ} {f : Coord n → ℝ}
    (hf : ContDiff ℝ 2 f) : Continuous (laplacian (fun _ => f) 0) := by
  exact continuous_finsetSum Finset.univ
    (fun i _ => continuous_partialD i (contDiff_partialD i hf))

theorem compactSupport_laplacian {n : ℕ} {f : Coord n → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    HasCompactSupport (laplacian (fun _ => f) 0) := by
  have hi (i : Fin n) : HasCompactSupport (partialD i (partialD i f)) :=
    compactSupport_partialD i ((contDiff_partialD i hf).differentiable (by norm_num))
      (compactSupport_partialD i (hf.differentiable (by norm_num)) hfc)
  have heq : laplacian (fun _ => f) 0 = ∑ i : Fin n, partialD i (partialD i f) := by
    ext X
    simp only [Finset.sum_apply]
    rfl
  rw [heq]
  exact HasCompactSupport.finset_sum (fun i _ => hi i)

theorem fderiv_apply_eq_sum {n : ℕ} {f : Coord n → ℝ}
    (hf : Differentiable ℝ f) (X v : Coord n) :
    fderiv ℝ f X v = ∑ i : Fin n, v i * partialD i f X := by
  have hv : v = ∑ i : Fin n, v i • Pi.single i (1 : ℝ) := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    simp [mul_ite]
  conv_lhs => rw [hv, map_sum]
  simp only [map_smul, smul_eq_mul, partialD_eq_fderiv _ hf]

theorem integral_mul_partialD {n : ℕ} (i : Fin n) {f g : Coord n → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hfc : HasCompactSupport f) :
    (∫ X, f X * partialD i g X) = -(∫ X, partialD i f X * g X) := by
  have hdf := hf.differentiable (by norm_num)
  have hdg := hg.differentiable (by norm_num)
  have hfc' := compactSupport_partialD i hdf hfc
  have hifg : Integrable (fun X => f X * g X) :=
    (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hfc.mul_right
  have hif'g : Integrable (fun X => partialD i f X * g X) :=
    ((continuous_partialD i hf).mul hg.continuous).integrable_of_hasCompactSupport hfc'.mul_right
  have hifg' : Integrable (fun X => f X * partialD i g X) :=
    (hf.continuous.mul (continuous_partialD i hg)).integrable_of_hasCompactSupport hfc.mul_right
  simp_rw [partialD_eq_fderiv i hdf, partialD_eq_fderiv i hdg] at hif'g hifg' ⊢
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hif'g hifg' hifg
    (fun X _ => hdf X) (fun X _ => hdg X)

theorem integral_mul_partialD_twice {n : ℕ} (i : Fin n) {f g : Coord n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hfc : HasCompactSupport f) :
    (∫ X, f X * partialD i (partialD i g) X) =
      ∫ X, partialD i (partialD i f) X * g X := by
  have hf1 := hf.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hg1 := hg.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  rw [integral_mul_partialD i hf1 (contDiff_partialD i hg) hfc]
  rw [integral_mul_partialD i (contDiff_partialD i hf) hg1
    (compactSupport_partialD i (hf.differentiable (by norm_num)) hfc), neg_neg]

theorem integral_mul_laplacian {n : ℕ} {f g : Coord n → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hfc : HasCompactSupport f) :
    (∫ X, f X * laplacian (fun _ => g) 0 X) =
      ∫ X, laplacian (fun _ => f) 0 X * g X := by
  have hdf := hf.differentiable (by norm_num)
  have hf' (i : Fin n) := contDiff_partialD i hf
  have hg' (i : Fin n) := contDiff_partialD i hg
  have hi (i : Fin n) : Integrable (fun X => f X * partialD i (partialD i g) X) :=
    (hf.continuous.mul (continuous_partialD i (hg' i))).integrable_of_hasCompactSupport hfc.mul_right
  have hj (i : Fin n) : Integrable (fun X => partialD i (partialD i f) X * g X) :=
    ((continuous_partialD i (hf' i)).mul hg.continuous).integrable_of_hasCompactSupport
      (compactSupport_partialD i ((hf' i).differentiable (by norm_num))
        (compactSupport_partialD i hdf hfc)).mul_right
  change (∫ X, f X * ∑ i : Fin n, partialD i (partialD i g) X) =
    ∫ X, (∑ i : Fin n, partialD i (partialD i f) X) * g X
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [integral_finsetSum _ (fun i _ => hi i), integral_finsetSum _ (fun i _ => hj i)]
  exact Finset.sum_congr rfl (fun i _ => integral_mul_partialD_twice i hf hg hfc)

theorem integral_mul_transport {n : ℕ} {f g : Coord n → ℝ} {a : Coord n → Coord n}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g)
    (ha : ∀ i, ContDiff ℝ 1 (fun X => a X i)) (hfc : HasCompactSupport f)
    (hdiv : ∀ X, (∑ i, partialD i (fun Y => a Y i) X) = 0) :
    (∫ X, f X * (∑ i, a X i * partialD i g X)) =
      -(∫ X, (∑ i, a X i * partialD i f X) * g X) := by
  have hdf := hf.differentiable (by norm_num)
  have hi (i : Fin n) : Integrable (fun X => f X * (a X i * partialD i g X)) :=
    (hf.continuous.mul ((ha i).continuous.mul (continuous_partialD i hg))).integrable_of_hasCompactSupport
      hfc.mul_right
  have hj (i : Fin n) : Integrable (fun X =>
      (partialD i f X * a X i + f X * partialD i (fun Y => a Y i) X) * g X) :=
    (((continuous_partialD i hf).mul (ha i).continuous).add
      (hf.continuous.mul (continuous_partialD i (ha i)))).mul hg.continuous
      |>.integrable_of_hasCompactSupport
        (((compactSupport_partialD i hdf hfc).mul_right).add hfc.mul_right).mul_right
  have hparts (i : Fin n) : (∫ X, f X * (a X i * partialD i g X)) =
      -(∫ X, (partialD i f X * a X i + f X * partialD i (fun Y => a Y i) X) * g X) := by
    simpa only [partialD_mul i hdf ((ha i).differentiable (by norm_num)), mul_assoc] using
      integral_mul_partialD i (hf.mul (ha i)) hg hfc.mul_right
  calc
    _ = ∑ i, ∫ X, f X * (a X i * partialD i g X) := by
      simp_rw [Finset.mul_sum]
      exact integral_finsetSum _ (fun i _ => hi i)
    _ = -(∫ X, ∑ i,
        (partialD i f X * a X i + f X * partialD i (fun Y => a Y i) X) * g X) := by
      simp_rw [hparts]
      rw [integral_finsetSum _ (fun i _ => hj i), Finset.sum_neg_distrib]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro X
      dsimp only
      rw [← Finset.sum_mul, Finset.sum_add_distrib, ← Finset.mul_sum, hdiv X, mul_zero, add_zero]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem weak_scalar_equation {n : ℕ} {φ ρ r g : Coord n → ℝ}
    {a : Coord n → Coord n} {ν : ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hρ : ContDiff ℝ 2 ρ) (hg : Continuous g)
    (ha : ∀ i, ContDiff ℝ 1 (fun X => a X i))
    (hdiv : ∀ X, (∑ i, partialD i (fun Y => a Y i) X) = 0)
    (heq : ∀ X, r X + (∑ i, a X i * partialD i ρ X) =
      ν * laplacian (fun _ => ρ) 0 X + g X) :
    (∫ X, φ X * r X) = (∫ X, (∑ i, a X i * partialD i φ X) * ρ X) +
      ν * (∫ X, laplacian (fun _ => φ) 0 X * ρ X) + ∫ X, φ X * g X := by
  have hφ1 := hφ.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hρ1 := hρ.of_le (show (1 : ℕ∞ω) ≤ 2 by norm_num)
  have hd : Integrable (fun X => φ X * laplacian (fun _ => ρ) 0 X) :=
    (hφ.continuous.mul (continuous_laplacian hρ)).integrable_of_hasCompactSupport hφc.mul_right
  have hs : Integrable (fun X => φ X * g X) :=
    (hφ.continuous.mul hg).integrable_of_hasCompactSupport hφc.mul_right
  have haρ : Continuous (fun X => ∑ i, a X i * partialD i ρ X) :=
    continuous_finsetSum Finset.univ
      (fun i _ => (ha i).continuous.mul (continuous_partialD i hρ1))
  have ht : Integrable (fun X => φ X * (∑ i, a X i * partialD i ρ X)) :=
    (hφ.continuous.mul haρ).integrable_of_hasCompactSupport hφc.mul_right
  have hid : (∫ X, φ X * r X) =
      (∫ X, ν * (φ X * laplacian (fun _ => ρ) 0 X) + φ X * g X -
        φ X * (∑ i, a X i * partialD i ρ X)) := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro X
    have h := congrArg (φ X * ·) (heq X)
    dsimp only at h ⊢
    linear_combination h
  rw [hid, integral_sub (f := fun X => ν * (φ X * laplacian (fun _ => ρ) 0 X) + φ X * g X)
      ((hd.const_mul ν).add hs) ht,
    integral_add (hd.const_mul ν) hs, integral_const_mul,
    integral_mul_transport hφ1 hρ1 ha hφc hdiv,
    integral_mul_laplacian hφ hρ hφc]
  ring

end VelocityDetection.SpatialCalculus
end

end OAI
