import Mathlib
import OAI.Probability.SKRatio.Matrices.GaussianCoordinates
import OAI.Probability.SKRatio.Matrices.GaussianQuadratic
import OAI.Probability.SKRatio.Matrices.GOERegression
import OAI.Probability.SKRatio.Quantization.BinCoefficients

namespace OAI

noncomputable section
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

abbrev Coordinates (ι : Type*) := (ι × ι) ⊕ ι

def radicalSq (σ : ι → α) (C K : α → α → ℝ) (s : α → ℝ) (a : α) : ℝ :=
  binVariance σ C a+∑ d, K a d^2*s d

omit [DecidableEq α] in
lemma radicalSq_nonneg (σ : ι → α) (C K : α → α → ℝ) {s : α → ℝ}
    (hs : ∀ a, 0 ≤ s a) (a : α) : 0≤radicalSq σ C K s a :=
  add_nonneg (binVariance_nonneg _ _ _) (Finset.sum_nonneg (fun d _ => mul_nonneg (sq_nonneg _) (hs d)))

def residualCoeff (σ : ι → α) (C K : α → α → ℝ) (δ : ℝ) (u : ι → ℝ) : Coordinates ι → ℝ
  | Sum.inl (i,j) => δ/sqrt 2*residualMatrix σ C K u i j
  | Sum.inr _ => 0

def comparisonCoeff (σ : ι → α) (C K : α → α → ℝ) (s : α → ℝ) (δ : ℝ)
    (u : ι → ℝ) : Coordinates ι → ℝ
  | Sum.inl _ => 0
  | Sum.inr i => δ*sqrt (radicalSq σ C K s (σ i))*u i

omit [DecidableEq α] in
lemma coeff_orthogonal (σ : ι → α) (C K : α → α → ℝ) (s : α → ℝ) (δ : ℝ)
    (u z : ι → ℝ) :
    (∑ k, (comparisonCoeff σ C K s δ u k-comparisonCoeff σ C K s δ z k)*
      (residualCoeff σ C K δ u k-residualCoeff σ C K δ z k))=0 := by
  simp [Fintype.sum_sum_type,residualCoeff,comparisonCoeff]

lemma comparisonCoeff_increment (σ : ι → α) (C K : α → α → ℝ) (δ : ℝ)
    {s : α → ℝ} (hs : ∀ a, 0 ≤ s a) {u z : ι → ℝ}
    (hu : overlap σ u u=s) (hz : overlap σ z z=s) :
    (∑ k, (comparisonCoeff σ C K s δ u k-comparisonCoeff σ C K s δ z k)^2)=
      2*δ^2*∑ a, (s a-overlap σ u z a)*radicalSq σ C K s a := by
  simp only [Fintype.sum_sum_type,comparisonCoeff,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero,zero_add]
  have he (i : ι) : (δ*sqrt (radicalSq σ C K s (σ i))*u i-δ*sqrt (radicalSq σ C K s (σ i))*z i)^2 =
      δ^2*(u i-z i)^2*radicalSq σ C K s (σ i) := by
    rw [←mul_sub,mul_pow,mul_pow,sq_sqrt (radicalSq_nonneg σ C K hs _)]
    ring
  simp_rw [he]
  rw [sum_weighted σ (fun i => δ^2*(u i-z i)^2) (radicalSq σ C K s),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  have hf : sum σ (fun i => δ^2*(u i-z i)^2) a =
      δ^2*(overlap σ u u a+overlap σ z z a-2*overlap σ u z a) := by
    unfold overlap sum
    simp only [mul_sub,mul_add,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hf,hu,hz]
  ring

lemma coeff_increment_le {σ : ι → α} (C K : α → α → ℝ)
    (hK : ∀ a d, K a d=K d a) (δ : ℝ) {u z : ι → ℝ} {s : α → ℝ}
    (hu : ZeroSum σ u) (hz : ZeroSum σ z)
    (hus : overlap σ u u=s) (hzs : overlap σ z z=s) :
    (∑ k, (residualCoeff σ C K δ u k-residualCoeff σ C K δ z k)^2) ≤
      ∑ k, (comparisonCoeff σ C K s δ u k-comparisonCoeff σ C K s δ z k)^2 := by
  have hs : ∀ a, 0 ≤ s a := fun a => hus ▸ overlap_self_nonneg σ u a
  rw [comparisonCoeff_increment σ C K δ hs hus hzs]
  simp only [Fintype.sum_sum_type,residualCoeff,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero,add_zero,Fintype.sum_prod_type]
  have hex : (∑ i, ∑ j, (δ/sqrt 2*residualMatrix σ C K u i j-δ/sqrt 2*residualMatrix σ C K z i j)^2) =
      (δ^2/2)*(∑ i, ∑ j, (residualMatrix σ C K u i j-residualMatrix σ C K z i j)^2) := by
    simp only [←mul_sub,mul_pow,div_pow,sq_sqrt (by norm_num : (0:ℝ)≤2),Finset.mul_sum]
  rw [hex]
  have hh := mul_le_mul_of_nonneg_left (residualMatrix_increment C K hK hu hz hus hzs)
    (show 0≤δ^2/2 by positivity)
  dsimp only [radicalSq]
  convert hh using 1
  first | rfl | ring

omit [Fintype ι] [Fintype α] [DecidableEq α] in
lemma continuous_residualCoeff (σ : ι → α) (C K : α → α → ℝ) (δ : ℝ) :
    Continuous (residualCoeff σ C K δ) := by
  apply continuous_pi
  intro k
  cases k with
  | inl ij =>
    dsimp [residualCoeff,residualMatrix,linearMatrix,quadraticMatrix]
    fun_prop
  | inr i => exact continuous_const

omit [DecidableEq α] in
lemma continuous_comparisonCoeff (σ : ι → α) (C K : α → α → ℝ) (s : α → ℝ) (δ : ℝ) :
    Continuous (comparisonCoeff σ C K s δ) := by
  apply continuous_pi
  intro k
  cases k with
  | inl ij => exact continuous_const
  | inr i => exact continuous_const.mul (continuous_apply i)

def blockNorm (σ : ι → α) (a : α) (g : Coordinates ι → ℝ) : ℝ :=
  sqrt (sum σ (fun i => g (Sum.inr i)^2) a)

omit [Fintype α] in
lemma blockNorm_memLp (σ : ι → α) (a : α) :
    MemLp (blockNorm σ a) 2 (SKRatioGaussian.gaussianCoordinates (Coordinates ι)) := by
  apply SKRatioGaussian.memLp_sqrt_of_nonneg
  · apply integrable_finsetSum
    intro i _
    exact (SKRatioClock.Regression.coordinate_hasLaw (Sum.inr i : Coordinates ι)).hasGaussianLaw.memLp_two.integrable_sq
  · intro g
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [Fintype α] in
lemma blockNorm_mean_le (σ : ι → α) (a : α) :
    (∫ g, blockNorm σ a g ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι)) ≤
      sqrt ((Finset.univ.filter (fun i => σ i=a)).card : ℝ) := by
  have h := SKRatioGaussian.integral_abs_le_sqrt_sq (blockNorm_memLp σ a)
  have he (g : Coordinates ι → ℝ) : blockNorm σ a g^2=sum σ (fun i => g (.inr i)^2) a :=
    sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  simp_rw [he,abs_of_nonneg (show 0≤blockNorm σ a _ from sqrt_nonneg _)] at h
  have hm : (∫ g, sum σ (fun i => g (.inr i)^2) a ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι)) =
      (Finset.univ.filter (fun i => σ i=a)).card := by
    change (∫ g, ∑ i with σ i=a, g (.inr i)^2 ∂SKRatioClock.Regression.standardArrayLaw (Coordinates ι)) = _
    rw [integral_finsetSum _ (fun i _ =>
      (SKRatioClock.Regression.coordinate_hasLaw (Sum.inr i : Coordinates ι)).hasGaussianLaw.memLp_two.integrable_sq)]
    have hint (i : ι) : (∫ g, g (.inr i)^2 ∂SKRatioClock.Regression.standardArrayLaw (Coordinates ι))=1 := by
      calc
        _ = ∫ x : ℝ, x^2 ∂gaussianReal 0 1 :=
          (SKRatioClock.Regression.coordinate_hasLaw (Sum.inr i : Coordinates ι)).integral_comp (by fun_prop)
        _ = 1 := SKRatioGaussian.gaussian_integral_sq
    simp only [hint,Finset.sum_const, nsmul_eq_mul,mul_one]
  rwa [hm] at h

lemma comparison_pointwise {σ : ι → α} (C K : α → α → ℝ)
    {s : α → ℝ} {δ : ℝ} (hδ : 0≤δ) {u : ι → ℝ} (hu : overlap σ u u=s)
    (g : Coordinates ι → ℝ) :
    (∑ k, comparisonCoeff σ C K s δ u k*g k) ≤
      ∑ a, δ*sqrt (radicalSq σ C K s a)*sqrt (s a)*blockNorm σ a g := by
  simp only [Fintype.sum_sum_type,comparisonCoeff,zero_mul,Finset.sum_const_zero,zero_add]
  have he : (∑ i, δ*sqrt (radicalSq σ C K s (σ i))*u i*g (.inr i)) =
      ∑ a, δ*sqrt (radicalSq σ C K s a)*sum σ (fun i => u i*g (.inr i)) a := by
    convert sum_weighted σ (fun i => u i*g (.inr i)) (fun a => δ*sqrt (radicalSq σ C K s a)) using 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · apply Finset.sum_congr rfl
      intro a _
      ring
  rw [he]
  apply Finset.sum_le_sum
  intro a _
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ.filter (fun i => σ i=a)) u (fun i => g (.inr i))
  have hsq : (∑ i with σ i=a, u i^2)=s a := by
    simpa only [overlap,sum,←pow_two] using congrFun hu a
  rw [hsq] at h
  exact (mul_le_mul_of_nonneg_left h (mul_nonneg hδ (sqrt_nonneg _))).trans_eq (by
    change δ*sqrt _*(sqrt _*blockNorm σ a g)=_
    ring)

variable {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]

theorem residual_sup_expectation_le [Nonempty ι] (σ : ι → α) (C K : α → α → ℝ)
    (hK : ∀ a d, K a d=K d a) {s : α → ℝ} {δ : ℝ} (hδ : 0≤δ)
    {u : I → ι → ℝ} (huc : Continuous u) (hu0 : ∀ t, ZeroSum σ (u t))
    (hus : ∀ t, overlap σ (u t) (u t)=s) :
    (∫ g, SKRatioGaussian.gaussianSup (fun _ : I => 0) (fun t => residualCoeff σ C K δ (u t)) g
      ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι)) ≤
      ∑ a, δ*sqrt (radicalSq σ C K s a)*sqrt (s a)*
        sqrt ((Finset.univ.filter (fun i => σ i=a)).card : ℝ) := by
  let X := fun t => residualCoeff σ C K δ (u t)
  let Y := fun t => comparisonCoeff σ C K s δ (u t)
  have hX : Continuous X := (continuous_residualCoeff σ C K δ).comp huc
  have hY : Continuous Y := (continuous_comparisonCoeff σ C K s δ).comp huc
  have hcomp := SKRatioGaussian.gaussianSup_comparison (m := fun _ : I => 0)
    continuous_const hY hX (fun t r => coeff_orthogonal σ C K s δ (u t) (u r))
      (fun t r => coeff_increment_le C K hK δ (hu0 t) (hu0 r) (hus t) (hus r))
  apply hcomp.trans
  have hbound : ∀ g, SKRatioGaussian.gaussianSup (fun _ : I => 0) Y g ≤
      ∑ a, δ*sqrt (radicalSq σ C K s a)*sqrt (s a)*blockNorm σ a g := by
    intro g
    apply SKRatioGaussian.gaussianSup_le continuous_const hY
    intro t
    simpa only [SKRatioGaussian.gaussianAffine,zero_add] using comparison_pointwise C K hδ (hus t) g
  have hib : Integrable (fun g => ∑ a, δ*sqrt (radicalSq σ C K s a)*sqrt (s a)*blockNorm σ a g)
      (SKRatioGaussian.gaussianCoordinates (Coordinates ι)) := integrable_finsetSum _ (fun a _ =>
        ((blockNorm_memLp σ a).integrable (by norm_num)).const_mul _)
  apply (integral_mono (SKRatioGaussian.integrable_gaussianSup continuous_const hY) hib hbound).trans
  rw [integral_finsetSum _ (fun a _ => ((blockNorm_memLp σ a).integrable (by norm_num)).const_mul _)]
  simp only [integral_const_mul]
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left (blockNorm_mean_le σ a) (by positivity)

end SKRatio.Bins

end

end OAI
