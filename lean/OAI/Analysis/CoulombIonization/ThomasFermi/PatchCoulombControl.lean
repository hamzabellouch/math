import Mathlib
import OAI.Analysis.CoulombIonization.Variational.CoulombNear
import OAI.Analysis.CoulombIonization.ThomasFermi.PatchGapMeasurable

namespace OAI

noncomputable section

namespace CoulombAnalysis

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory

lemma tfCoulombL_pair_sq_le (R : ℝ) (f g : TFLp (ballMeasure R)) :
    (tfCoulombL R f g)^2 ≤ tfCoulombL R f f*tfCoulombL R g g := by
  have hn (t : ℝ) : 0 ≤ tfCoulombL R f f*(t*t)+(-2*tfCoulombL R f g)*t+tfCoulombL R g g := by
    have hh := tfCoulombL_nonneg R (t • f-g)
    simp only [map_sub,map_smul,sub_apply,smul_apply,smul_eq_mul] at hh
    rw [tfCoulombL_symmetric R g f] at hh
    nlinarith
  have hd := discrim_le_zero hn
  unfold discrim at hd
  nlinarith

lemma tfPatchGap_coulomb_le (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) :
    tfCoulombL R (σ-tfPatchMinimizer R T hT Φ) (σ-tfPatchMinimizer R T hT Φ) ≤
      2*tfPatchGap R T hT Φ σ := by
  have hn : 0 ≤ ∫ z, max (tfBallPotential R (tfPatchMinimizer R T hT Φ) z-Φ z) 0*σ z ∂ballMeasure R :=
    integral_nonneg_of_ae (hσ.mono fun _ h => mul_nonneg (le_max_right _ _) h)
  unfold tfPatchGap
  linarith

theorem tfPatchGap_pair_control (R T : ℝ) (hT : 0 < T) (Φ : TFField R)
    {σ : TFLp (ballMeasure R)} (hσ : NonnegDensity σ) (f : TFLp (ballMeasure R)) :
    (tfCoulombL R f (σ-tfPatchMinimizer R T hT Φ))^2 ≤
      2*tfCoulombL R f f*tfPatchGap R T hT Φ σ := by
  exact (tfCoulombL_pair_sq_le R f _).trans (by
    have hh := mul_le_mul_of_nonneg_left (tfPatchGap_coulomb_le R T hT Φ hσ) (tfCoulombL_nonneg R f)
    nlinarith)

open MeasureTheory Set InnerProductSpace Laplacian
open scoped BigOperators

lemma compact_partial_integration_by_parts {f g : TFSpace → ℝ}
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hcg : HasCompactSupport g)
    (v : TFSpace) :
    (∫ x, f x*fderiv ℝ g x v) = -(∫ x, fderiv ℝ f x v*g x) := by
  have hdf : Continuous (fun x => fderiv ℝ f x v) :=
    (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hdg : Continuous (fun x => fderiv ℝ g x v) :=
    (hg.continuous_fderiv (by norm_num)).clm_apply continuous_const
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((hdf.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left)
    ((hf.continuous.mul hdg).integrable_of_hasCompactSupport (hcg.fderiv_apply ℝ v).mul_left)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left)
    (fun x _ => (hf.differentiable (by norm_num)).differentiableAt)
    (fun x _ => (hg.differentiable (by norm_num)).differentiableAt)

def tfPartial (f : TFSpace → ℝ) (i : Fin 3) (x : TFSpace) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

lemma tfPartial_contDiff {f : TFSpace → ℝ} (hf : ContDiff ℝ 2 f) (i : Fin 3) :
    ContDiff ℝ 1 (tfPartial f i) :=
  (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).clm_apply contDiff_const

lemma tfPartial_continuous {f : TFSpace → ℝ} (hf : ContDiff ℝ 1 f) (i : Fin 3) :
    Continuous (tfPartial f i) :=
  (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const

lemma tfPartial_compact {f : TFSpace → ℝ} (hf : HasCompactSupport f) (i : Fin 3) :
    HasCompactSupport (tfPartial f i) := hf.fderiv_apply ℝ _

lemma tfLaplacian_eq {f : TFSpace → ℝ} (hf : ContDiff ℝ 2 f) :
    Δ f = fun x => ∑ i : Fin 3, tfPartial (tfPartial f i) i x := by
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis f (EuclideanSpace.basisFun (Fin 3) ℝ)]
  funext x
  apply Finset.sum_congr rfl
  intro i _
  simp only [EuclideanSpace.basisFun_apply,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,tfPartial]
  exact (fderiv_apply_const_scalar
    ((hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞)+1 ≤ 2)).differentiable
      (by norm_num)).differentiableAt _ _).symm

lemma tfLaplacian_continuous {f : TFSpace → ℝ} (hf : ContDiff ℝ 2 f) :
    Continuous (Δ f) := by
  rw [tfLaplacian_eq hf]
  exact continuous_finsetSum _ (fun i _ => tfPartial_continuous (tfPartial_contDiff hf i) i)

lemma tfLaplacian_compact {f : TFSpace → ℝ} (hf : ContDiff ℝ 2 f)
    (hcf : HasCompactSupport f) : HasCompactSupport (Δ f) := by
  rw [tfLaplacian_eq hf]
  have he : (fun x => ∑ i : Fin 3, tfPartial (tfPartial f i) i x) =
      ∑ i : Fin 3, tfPartial (tfPartial f i) i := by
    funext x
    simp only [Finset.sum_apply]
  rw [he]
  exact HasCompactSupport.finset_sum
    (s := Finset.univ) (f := fun i : Fin 3 => tfPartial (tfPartial f i) i)
    (fun i _ => tfPartial_compact (tfPartial_compact hcf i) i)

lemma compact_second_partial_green {f g : TFSpace → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g)
    (i : Fin 3) :
    (∫ x, f x*tfPartial (tfPartial g i) i x) =
      ∫ x, tfPartial (tfPartial f i) i x*g x := by
  have h1 := compact_partial_integration_by_parts (hf.of_le (by norm_num))
    (tfPartial_contDiff hg i) (tfPartial_compact hcg i) (EuclideanSpace.single i 1)
  have h2 := compact_partial_integration_by_parts (tfPartial_contDiff hf i)
    (hg.of_le (by norm_num)) hcg (EuclideanSpace.single i 1)
  change (∫ x, f x*tfPartial (tfPartial g i) i x) =
    -(∫ x, tfPartial f i x*tfPartial g i x) at h1
  change (∫ x, tfPartial f i x*tfPartial g i x) =
    -(∫ x, tfPartial (tfPartial f i) i x*g x) at h2
  rw [h1,h2,neg_neg]

theorem compact_laplacian_green {f g : TFSpace → ℝ}
    (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hcg : HasCompactSupport g) :
    (∫ x, f x*Δ g x) = ∫ x, Δ f x*g x := by
  rw [tfLaplacian_eq hf,tfLaplacian_eq hg]
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [integral_finsetSum Finset.univ (μ := volume)
    (f := fun i x => f x*tfPartial (tfPartial g i) i x) (fun i _ =>
    (hf.continuous.mul (tfPartial_continuous (tfPartial_contDiff hg i) i)).integrable_of_hasCompactSupport
      (tfPartial_compact (tfPartial_compact hcg i) i).mul_left)]
  rw [integral_finsetSum Finset.univ (μ := volume)
    (f := fun i x => tfPartial (tfPartial f i) i x*g x) (fun i _ =>
    ((tfPartial_continuous (tfPartial_contDiff hf i) i).mul hg.continuous).integrable_of_hasCompactSupport hcg.mul_left)]
  apply Finset.sum_congr rfl
  intro i _
  exact compact_second_partial_green hf hg hcg i

theorem compact_laplacian_energy {f : TFSpace → ℝ}
    (hf : ContDiff ℝ 2 f) (hcf : HasCompactSupport f) :
    (∫ x, f x*Δ f x) = -(∑ i : Fin 3, ∫ x, (tfPartial f i x)^2) := by
  rw [tfLaplacian_eq hf]
  simp only [Finset.mul_sum]
  rw [integral_finsetSum Finset.univ (μ := volume)
    (f := fun i x => f x*tfPartial (tfPartial f i) i x) (fun i _ =>
    (hf.continuous.mul (tfPartial_continuous (tfPartial_contDiff hf i) i)).integrable_of_hasCompactSupport
      (tfPartial_compact (tfPartial_compact hcf i) i).mul_left),←Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [tfPartial,pow_two] using compact_partial_integration_by_parts
    (hf.of_le (by norm_num)) (tfPartial_contDiff hf i) (tfPartial_compact hcf i) (EuclideanSpace.single i 1)

end CoulombAnalysis

end

end OAI
