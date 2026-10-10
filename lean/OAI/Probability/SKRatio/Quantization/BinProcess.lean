import Mathlib
import OAI.Probability.SKRatio.Matrices.GaussianAffineGaussianSup
import OAI.Probability.SKRatio.Matrices.GaussianProductUpperTailLipschitz
import OAI.Probability.SKRatio.Quantization.BinGaussian

namespace OAI

noncomputable section
open scoped BigOperators Matrix NNReal
open MeasureTheory ProbabilityTheory Filter Real
namespace SKRatio.Bins
variable {ι α : Type*} [Fintype ι] [Nonempty ι] [Fintype α] [DecidableEq α]
attribute [local instance] Classical.propDecidable

def average (p : ι → ℝ) : ℝ := (∑ i, p i)/(Fintype.card ι:ℝ)
def centered (p : ι → ℝ) : ι → ℝ := fun i => p i-average p

omit [Nonempty ι] in
lemma average_add (p q : ι → ℝ) : average (fun i => p i+q i)=average p+average q := by
  simp only [average,Finset.sum_add_distrib,add_div]
omit [Nonempty ι] in
lemma average_mul (p : ι → ℝ) (c : ℝ) : average (fun i => c*p i)=c*average p := by
  simp only [average,←Finset.mul_sum,mul_div_assoc]
lemma average_const (c : ℝ) : average (fun _ : ι => c)=c := by
  have hn : (Fintype.card ι:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  simp [average,mul_div_cancel_left₀ _ hn]
omit [Nonempty ι] in
lemma average_zeroSum {σ : ι → α} {u : ι → ℝ} (hu : ZeroSum σ u) : average u=0 := by
  have h := zero_sum_weighted hu (fun _ => 1)
  simpa only [mul_one, average, zero_div] using congrArg (fun z : ℝ => z/(Fintype.card ι:ℝ)) h

lemma centered_sq (p : ι → ℝ) : (∑ i, centered p i^2)=(∑ i, p i^2)-
    (Fintype.card ι:ℝ)*average p^2 := by
  have hn : (Fintype.card ι:ℝ)≠0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hsum : (∑ i, p i)=(Fintype.card ι:ℝ)*average p := by
    dsimp [average]
    field_simp
  simp only [centered,sub_sq,Finset.sum_add_distrib,Finset.sum_sub_distrib,
    ←Finset.sum_mul,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  rw [hsum]
  ring
lemma centered_sq_le (p : ι → ℝ) : (∑ i, centered p i^2)≤∑ i, p i^2 := by
  rw [centered_sq]
  exact sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

def fullCoeff (v p : ι → ℝ) (δ : ℝ) : Coordinates ι → ℝ
  | .inl (i,j) => δ/sqrt 2*(centered p i*centered (fun k => v k*p k) j+
      centered p j*centered (fun k => v k*p k) i)
  | .inr _ => 0

omit [Nonempty ι] in
lemma continuous_centered : Continuous (centered (ι := ι)) := by
  apply continuous_pi
  intro i
  exact (continuous_apply i).sub ((continuous_finsetSum _ (fun j _ => continuous_apply j)).div_const _)

omit [Nonempty ι] in
lemma continuous_fullCoeff (v : ι → ℝ) (δ : ℝ) : Continuous (fun p => fullCoeff v p δ) := by
  apply continuous_pi
  intro k
  cases k with
  | inr i => exact continuous_const
  | inl ij =>
    change Continuous (fun p => δ/sqrt 2*(centered p ij.1*centered (fun k => v k*p k) ij.2+
      centered p ij.2*centered (fun k => v k*p k) ij.1))
    have hm : Continuous (fun p : ι → ℝ => fun k => v k*p k) := by fun_prop
    exact (((continuous_apply ij.1).comp continuous_centered |>.mul
      ((continuous_apply ij.2).comp (continuous_centered.comp hm))).add
      (((continuous_apply ij.2).comp continuous_centered).mul
      ((continuous_apply ij.1).comp (continuous_centered.comp hm)))).const_mul _

def crossCoeff (σ : ι → α) (v b : α → ℝ) (a d : α) : ℝ :=
  (v a+v d)*b d-average (fun i => (v a+v (σ i))*b (σ i))

omit [Nonempty ι] [Fintype α] [DecidableEq α] in
lemma crossCoeff_eq (σ : ι → α) (v b : α → ℝ) (a : α) (j : ι) :
    crossCoeff σ v b a (σ j)=centered (fun i => v (σ i)*b (σ i)) j+
      v a*centered (fun i => b (σ i)) j := by
  have he : (fun i => (v a+v (σ i))*b (σ i))=
      (fun i => v a*b (σ i)+v (σ i)*b (σ i)) := by ext i; ring
  rw [crossCoeff,he,average_add,average_mul]
  dsimp only [centered]
  ring

omit [Nonempty ι] in
lemma centered_add_zeroSum {σ : ι → α} (b : α → ℝ) {u : ι → ℝ} (hu : ZeroSum σ u) :
    centered (fun i => b (σ i)+u i)=fun i => centered (fun k => b (σ k)) i+u i := by
  ext i
  simp only [centered,average_add,average_zeroSum hu,add_zero]
  ring

omit [Nonempty ι] [Fintype α] in
lemma zeroSum_mul {σ : ι → α} (v : α → ℝ) {u : ι → ℝ} (hu : ZeroSum σ u) :
    ZeroSum σ (fun i => v (σ i)*u i) := by
  intro a
  have he : sum σ (fun i => v (σ i)*u i) a = v a*sum σ u a := by
    unfold sum
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    change v (σ i)*u i=v a*u i
    rw [(Finset.mem_filter.mp hi).2]
  rw [he,hu a,mul_zero]

omit [Nonempty ι] in
lemma fullCoeff_decomposition {σ : ι → α} (v b : α → ℝ) (δ : ℝ) {u : ι → ℝ}
    (hu : ZeroSum σ u) :
    fullCoeff (fun i => v (σ i)) (fun i => b (σ i)+u i) δ =
      fun k => fullCoeff (fun i => v (σ i)) (fun i => b (σ i)) δ k+
        residualCoeff σ (crossCoeff σ v b) (fun a d => v a+v d) δ u k := by
  have he : (fun i => v (σ i)*(b (σ i)+u i))=
      fun i => v (σ i)*b (σ i)+v (σ i)*u i := by ext i; ring
  have hcen := centered_add_zeroSum (fun a => v a*b a) (zeroSum_mul v hu)
  ext k
  cases k with
  | inr i => simp [fullCoeff,residualCoeff]
  | inl ij =>
    rcases ij with ⟨i,j⟩
    simp only [fullCoeff,residualCoeff,centered_add_zeroSum b hu,he,hcen,residualMatrix,
      Matrix.add_apply,Matrix.transpose_apply,linearMatrix,quadraticMatrix,crossCoeff_eq]
    ring

lemma fullCoeff_sq_le {v p : ι → ℝ} (hv : ∀ i, |v i|≤1) (δ : ℝ) :
    (∑ k, fullCoeff v p δ k^2) ≤ 2*δ^2*(∑ i, p i^2)^2 := by
  let x := centered p
  let y := centered (fun i => v i*p i)
  have hx : (∑ i, x i^2)≤∑ i, p i^2 := centered_sq_le p
  have hy : (∑ i, y i^2)≤∑ i, p i^2 := (centered_sq_le _).trans (by
    apply Finset.sum_le_sum
    intro i _
    have hvi : v i^2≤1 := (sq_le_one_iff_abs_le_one (v i)).mpr (hv i)
    simpa only [mul_pow,one_mul] using mul_le_mul_of_nonneg_right hvi (sq_nonneg (p i)))
  have hprod : (∑ i, x i^2)*(∑ j, y j^2)≤(∑ i, p i^2)^2 := by
    rw [pow_two]
    exact mul_le_mul hx hy (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
  have hsq : (∑ i, ∑ j, (x i*y j+x j*y i)^2)≤4*((∑ i, x i^2)*(∑ j, y j^2)) := by
    calc
      _ ≤ ∑ i, ∑ j, 2*((x i*y j)^2+(x j*y i)^2) := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        nlinarith only [sq_nonneg (x i*y j-x j*y i)]
      _ = _ := by
        simp only [mul_add,mul_pow,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
        ring
  simp only [Fintype.sum_sum_type,fullCoeff,zero_pow (by norm_num : (2:ℕ)≠0),
    Finset.sum_const_zero,add_zero,Fintype.sum_prod_type,mul_pow,div_pow,
    sq_sqrt (by norm_num : (0:ℝ)≤2),←Finset.mul_sum]
  change δ^2/2*(∑ i, ∑ j, (x i*y j+x j*y i)^2)≤_
  have h := mul_le_mul_of_nonneg_left (hsq.trans (mul_le_mul_of_nonneg_left hprod (by norm_num)))
    (show 0≤δ^2/2 by positivity)
  convert h using 1
  first | rfl | ring

lemma fullCoeff_norm_le {v p : ι → ℝ} (hv : ∀ i, |v i|≤1) {δ : ℝ} (hδ : 0≤δ)
    (hp : ∑ i, p i^2=1) : ‖WithLp.toLp 2 (fullCoeff v p δ)‖≤ sqrt 2*δ := by
  have h := fullCoeff_sq_le (p := p) hv δ
  rw [hp] at h
  have he : ‖WithLp.toLp 2 (fullCoeff v p δ)‖^2=∑ k, fullCoeff v p δ k^2 := by
    simp only [EuclideanSpace.norm_sq_eq,Real.norm_eq_abs,sq_abs]
  have hs := sq_sqrt (show (0:ℝ)≤2 by norm_num)
  have hpos : 0≤ sqrt 2*δ := mul_nonneg (sqrt_nonneg _) hδ
  apply (sq_le_sq₀ (norm_nonneg _) hpos).mp
  rw [mul_pow,hs,he]
  simpa only [one_pow,mul_one] using h

section Translation
variable {κ I : Type*} [Fintype κ] [TopologicalSpace I] [CompactSpace I] [Nonempty I]

lemma gaussianSup_add_common {a : I → κ → ℝ} (ha : Continuous a) (c : κ → ℝ)
    (g : κ → ℝ) :
    SKRatioGaussian.gaussianSup (fun _ : I => 0) (fun t k => c k+a t k) g =
      (∑ k, c k*g k)+SKRatioGaussian.gaussianSup (fun _ : I => 0) a g := by
  have hac : Continuous (fun t k => c k+a t k) := continuous_const.add ha
  have he (t : I) : SKRatioGaussian.gaussianAffine (fun _ : I => 0) (fun t k => c k+a t k) g t =
      (∑ k, c k*g k)+SKRatioGaussian.gaussianAffine (fun _ : I => 0) a g t := by
    simp only [SKRatioGaussian.gaussianAffine,add_mul,Finset.sum_add_distrib,zero_add]
  apply le_antisymm
  · apply SKRatioGaussian.gaussianSup_le continuous_const hac
    intro t
    rw [he]
    exact add_le_add le_rfl (SKRatioGaussian.gaussianAffine_le_gaussianSup continuous_const ha g t)
  · obtain ⟨t, ht, _⟩ := SKRatioGaussian.gaussianSup_attained continuous_const ha g
    rw [ht,←he]
    exact SKRatioGaussian.gaussianAffine_le_gaussianSup continuous_const hac g t

lemma integral_gaussianSup_add_common {a : I → κ → ℝ} (ha : Continuous a) (c : κ → ℝ) :
    (∫ g, SKRatioGaussian.gaussianSup (fun _ : I => 0) (fun t k => c k+a t k) g
      ∂SKRatioGaussian.gaussianCoordinates κ) =
      ∫ g, SKRatioGaussian.gaussianSup (fun _ : I => 0) a g ∂SKRatioGaussian.gaussianCoordinates κ := by
  have hi (k : κ) : Integrable (fun g : κ → ℝ => c k*g k) (SKRatioGaussian.gaussianCoordinates κ) :=
    ((SKRatioClock.Regression.coordinate_hasLaw k).hasGaussianLaw.integrable).const_mul _
  simp_rw [gaussianSup_add_common ha c]
  rw [integral_add (integrable_finsetSum _ (fun k _ => hi k))
    (SKRatioGaussian.integrable_gaussianSup continuous_const ha),
    integral_finsetSum _ (fun k _ => hi k)]
  have hm (k : κ) : (∫ g : κ → ℝ, c k*g k ∂SKRatioGaussian.gaussianCoordinates κ)=0 := by
    rw [integral_const_mul]
    change c k*(∫ g : κ → ℝ, g k ∂SKRatioClock.Regression.standardArrayLaw κ)=0
    rw [SKRatioClock.Regression.coordinate_mean,mul_zero]
  simp only [hm,Finset.sum_const_zero,zero_add]
end Translation

variable {I : Type*} [TopologicalSpace I] [CompactSpace I] [Nonempty I]

theorem full_sup_expectation_le (σ : ι → α) (v b : α → ℝ)
    {s : α → ℝ} {δ : ℝ} (hδ : 0≤δ) {u : I → ι → ℝ}
    (huc : Continuous u) (hu0 : ∀ t, ZeroSum σ (u t))
    (hus : ∀ t, overlap σ (u t) (u t)=s) :
    (∫ g, SKRatioGaussian.gaussianSup (fun _ : I => 0)
      (fun t => fullCoeff (fun i => v (σ i)) (fun i => b (σ i)+u t i) δ) g
      ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι)) ≤
      ∑ a, δ*sqrt (radicalSq σ (crossCoeff σ v b) (fun a d => v a+v d) s a)*
        sqrt (s a)*sqrt ((Finset.univ.filter (fun i => σ i=a)).card : ℝ) := by
  have hd (t : I) := fullCoeff_decomposition v b δ (hu0 t)
  simp_rw [hd]
  have hi := integral_gaussianSup_add_common
    ((continuous_residualCoeff σ (crossCoeff σ v b) (fun a d => v a+v d) δ).comp huc)
    (fullCoeff (fun i => v (σ i)) (fun i => b (σ i)) δ)
  exact hi.trans_le (residual_sup_expectation_le σ _ _ (fun a d => add_comm _ _) hδ huc hu0 hus)

theorem full_sup_lipschitz (v : ι → ℝ) (hv : ∀ i, |v i|≤1)
    {δ : ℝ} (hδ : 0≤δ) {p : I → ι → ℝ} (hpc : Continuous p)
    (hp : ∀ t, ∑ i, p t i^2=1) :
    LipschitzWith ⟨sqrt 2*δ,by positivity⟩
      (fun g : EuclideanSpace ℝ (Coordinates ι) =>
        SKRatioGaussian.gaussianSup (fun _ : I => 0) (fun t => fullCoeff v (p t) δ) g.ofLp) := by
  apply SKRatioGaussian.gaussianSup_lipschitz continuous_const ((continuous_fullCoeff v δ).comp hpc)
  intro t
  exact fullCoeff_norm_le hv hδ (hp t)

theorem full_sup_tail (σ : ι → α) (v b : α → ℝ) (hv : ∀ a, |v a|≤1)
    {s : α → ℝ} {δ : ℝ} (hδ : 0<δ) {u : I → ι → ℝ}
    (huc : Continuous u) (hu0 : ∀ t, ZeroSum σ (u t))
    (hus : ∀ t, overlap σ (u t) (u t)=s)
    (hp : ∀ t, ∑ i, (b (σ i)+u t i)^2=1) {a : ℝ} (ha : 0≤a) :
    (SKRatioGaussian.gaussianCoordinates (Coordinates ι)).real {g |
      (∑ d, δ*sqrt (radicalSq σ (crossCoeff σ v b) (fun a d => v a+v d) s d)*
        sqrt (s d)*sqrt ((Finset.univ.filter (fun i => σ i=d)).card : ℝ))+a ≤
      SKRatioGaussian.gaussianSup (fun _ : I => 0)
        (fun t => fullCoeff (fun i => v (σ i)) (fun i => b (σ i)+u t i) δ) g} ≤
      exp (-a^2/(π^2*δ^2)) := by
  let p : I → ι → ℝ := fun t i => b (σ i)+u t i
  have hpc : Continuous p := continuous_const.add huc
  let f := SKRatioGaussian.gaussianSup (fun _ : I => 0)
    (fun t => fullCoeff (fun i => v (σ i)) (p t) δ)
  have hL : (0:ℝ≥0) < ⟨sqrt 2*δ,by positivity⟩ := by
    change (0:ℝ)<sqrt 2*δ
    positivity
  have hc := SKRatioGaussian.gaussianProduct_upper_tail_lipschitz
    (full_sup_lipschitz _ (fun i => hv (σ i)) hδ.le hpc hp) hL ha
  have he := full_sup_expectation_le σ v b hδ.le huc hu0 hus
  have hsub : {g | (∑ d, δ*sqrt (radicalSq σ (crossCoeff σ v b) (fun a d => v a+v d) s d)*
        sqrt (s d)*sqrt ((Finset.univ.filter (fun i => σ i=d)).card : ℝ))+a ≤ f g} ⊆
      {g | a ≤ f g-∫ y, f y ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι)} := by
    intro g hg
    change _+a≤f g at hg
    change (∫ y, f y ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι))≤_ at he
    change a≤f g-(∫ y, f y ∂SKRatioGaussian.gaussianCoordinates (Coordinates ι))
    linarith only [hg,he]
  have hcont : Continuous f := SKRatioGaussian.continuous_gaussianSup continuous_const
    ((continuous_fullCoeff _ _).comp hpc)
  apply (measureReal_mono hsub).trans
  convert hc using 1 <;> try rfl
  apply congrArg Real.exp
  change -a^2/(π^2*δ^2) = -2*a^2/(π^2*(sqrt 2*δ)^2)
  rw [mul_pow,sq_sqrt (by norm_num : (0:ℝ)≤2)]
  ring

end SKRatio.Bins

end

end OAI
