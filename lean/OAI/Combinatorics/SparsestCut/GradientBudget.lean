import OAI.Combinatorics.SparsestCut.ConcreteCells

namespace OAI

universe u1 u2 u3 u4 u5 u6 u7 u8 u9

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.GradientBudget
variable {E : Type u1} {S : Type u2} {I : Type u3} {A : Type u4} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype S] [Fintype I] [Fintype A] [DecidableEq S]

lemma directional_control (u : I → E) (β : I → ℝ) (a e : E) {δ : ℝ}
    (hδ : 0 ≤ δ) (ha : a+e=∑ i, β i • u i)
    (hu : ∀ i, |inner ℝ (u i) a| ≤ δ*‖a‖) :
    ‖a‖ ≤ δ*∑ i, |β i|+‖e‖ := by
  by_cases hz : a=0
  · simp only [hz,norm_zero]; positivity
  have hn : 0 < ‖a‖ := norm_pos_iff.mpr hz
  have hs : |inner ℝ (∑ i, β i • u i) a| ≤ δ*‖a‖*∑ i, |β i| := by
    rw [sum_inner]
    calc
      _ ≤ ∑ i, |inner ℝ (β i • u i) a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, |β i| * (δ*‖a‖) := by
        apply Finset.sum_le_sum; intro i _
        rw [real_inner_smul_left,abs_mul]
        exact mul_le_mul_of_nonneg_left (hu i) (abs_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; ring
  have hip : ‖a‖^2 ≤ |inner ℝ (∑ i, β i • u i) a|+‖e‖*‖a‖ := by
    rw [← ha,inner_add_left]
    have h := abs_real_inner_le_norm e a
    rw [real_inner_self_eq_norm_sq]
    have hab := le_abs_self (‖a‖^2+inner ℝ e a)
    have hab' := neg_le_abs (inner ℝ e a)
    nlinarith
  have hmul : ‖a‖*‖a‖ ≤ (δ*∑ i, |β i|+‖e‖)*‖a‖ := by nlinarith
  nlinarith

omit [DecidableEq S] in
lemma good_chart_average (u : S → I → E) (β : S → I → ℝ) (a : E) (e : S → E)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ s, a+e s=∑ i, β s i • u s i)
    (good : Finset S) (hgood : (Fintype.card S : ℝ)/2 ≤ good.card)
    (hu : ∀ s ∈ good, ∀ i, |inner ℝ (u s i) a| ≤ δ*‖a‖) :
    (Fintype.card S : ℝ)*‖a‖ ≤ 2*∑ s, (δ*∑ i, |β s i|+‖e s‖) := by
  have hg : (good.card:ℝ)*‖a‖ ≤ ∑ s ∈ good, (δ*∑ i, |β s i|+‖e s‖) := by
    calc
      _ = ∑ _s ∈ good, ‖a‖ := by simp
      _ ≤ _ := Finset.sum_le_sum (fun s hs => directional_control (u s) (β s) a (e s) hδ (ha s) (hu s hs))
  have hsub : (∑ s ∈ good, (δ*∑ i, |β s i|+‖e s‖)) ≤ ∑ s, (δ*∑ i, |β s i|+‖e s‖) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro s _ _; positivity
  have hmult := mul_le_mul_of_nonneg_right hgood (norm_nonneg a)
  linarith

omit [DecidableEq S] in
lemma total_gradient (u : S → I → E) (β : S → I → A → ℝ) (a : A → E) (e : S → A → E)
    {δ B R : ℝ} (hδ : 0 ≤ δ)
    (ha : ∀ s α, a α+e s α=∑ i, β s i α • u s i)
    (hg : ∀ α, ∃ good : Finset S, (Fintype.card S : ℝ)/2 ≤ good.card ∧
      ∀ s ∈ good, ∀ i, |inner ℝ (u s i) (a α)| ≤ δ*‖a α‖)
    (hβ : ∀ s, ∑ i, ∑ α, |β s i α| ≤ B)
    (he : ∀ s, ∑ α, ‖e s α‖ ≤ R) (hS : 0 < Fintype.card S) :
    ∑ α, ‖a α‖ ≤ 2*(δ*B+R) := by
  have hcomp (α : A) : (Fintype.card S : ℝ)*‖a α‖ ≤
      2*∑ s, (δ*∑ i, |β s i α|+‖e s α‖) := by
    obtain ⟨good,hgood,hu⟩ := hg α
    exact good_chart_average u (fun s i => β s i α) (a α) (fun s => e s α) hδ
      (fun s => ha s α) good hgood hu
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun α _ => hcomp α)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm] at hs
  have hb (s : S) : (∑ α, (δ*∑ i, |β s i α|+‖e s α‖)) ≤ δ*B+R := by
    rw [Finset.sum_add_distrib,← Finset.mul_sum,Finset.sum_comm]
    exact add_le_add (mul_le_mul_of_nonneg_left (hβ s) hδ) (he s)
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun s _ => hb s)
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hsum
  have hcard : (0:ℝ) < Fintype.card S := by exact_mod_cast hS
  nlinarith

end UniformSparsestCut.GradientBudget

namespace UniformSparsestCut.ConvolutionBounds
open MeasureTheory Set
open scoped BigOperators
variable {G : Type u5} {A : Type u6} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [MeasurableSpace G] [BorelSpace G] [Fintype A]
  {μ : Measure G} [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant]

def smooth (κ f : G → ℝ) (μ : Measure G) : G → ℝ :=
  convolution κ f (ContinuousLinearMap.mul ℝ ℝ) μ

omit [NormedSpace ℝ G] [BorelSpace G] [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant] in
lemma smooth_eq (κ f : G → ℝ) (x : G) :
    smooth κ f μ x = ∫ z, κ z*f (x-z) ∂μ := rfl

lemma smooth_deriv {κ f : G → ℝ} (hk : HasCompactSupport κ)
    (hc : ContDiff ℝ 1 κ) (hf : LocallyIntegrable f μ) (x h : G) :
    fderiv ℝ (smooth κ f μ) x h = ∫ z, (fderiv ℝ κ z h)*f (x-z) ∂μ := by
  unfold smooth
  rw [(hk.hasFDerivAt_convolution_left (ContinuousLinearMap.mul ℝ ℝ) hc hf x).fderiv]
  have hi := (hk.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.mul ℝ ℝ).precompL G) (hc.continuous_fderiv (by norm_num)) hf x
  exact ContinuousLinearMap.integral_apply hi h

omit [SFinite μ] in
lemma smooth_deriv_integrable {κ f : G → ℝ} (hk : HasCompactSupport κ)
    (hc : ContDiff ℝ 1 κ) (hf : LocallyIntegrable f μ) (x h : G) :
    Integrable (fun z => (fderiv ℝ κ z h)*f (x-z)) μ := by
  have hi := (hk.fderiv ℝ).convolutionExists_left
    ((ContinuousLinearMap.mul ℝ ℝ).precompL G) (hc.continuous_fderiv (by norm_num)) hf x
  exact hi.apply_continuousLinearMap h

omit [NormedAddCommGroup G] [NormedSpace ℝ G] [BorelSpace G] [SFinite μ] [μ.IsAddLeftInvariant] [μ.IsNegInvariant] in

lemma integral_l1_bound (f : A → G → ℝ) (hf : ∀ a, Integrable (f a) μ)
    {B : G → ℝ} (hB : Integrable B μ) (hb : ∀ᵐ z ∂μ, ∑ a, |f a z| ≤ B z) :
    (∑ a, |∫ z, f a z ∂μ|) ≤ ∫ z, B z ∂μ := by
  calc
    _ ≤ ∑ a, ∫ z, |f a z| ∂μ := Finset.sum_le_sum (fun a _ => by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (f a))
    _ = ∫ z, ∑ a, |f a z| ∂μ := (integral_finsetSum _ (fun a _ => (hf a).abs)).symm
    _ ≤ _ := integral_mono_ae (integrable_finsetSum _ (fun a _ => (hf a).abs)) hB hb

lemma mismatch {κ : G → ℝ} (hk : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    (f g : A → G → ℝ) (hf : ∀ a, LocallyIntegrable (f a) μ)
    (hg : ∀ a, LocallyIntegrable (g a) μ) (x h : G) {B : ℝ}
    (hki : Integrable (fun z => |fderiv ℝ κ z h|) μ)
    (hb : ∀ᵐ z ∂μ, fderiv ℝ κ z h ≠ 0 → ∑ a, |f a (x-z)-g a (x-z)| ≤ B) :
    (∑ a, |fderiv ℝ (smooth κ (f a) μ) x h-fderiv ℝ (smooth κ (g a) μ) x h|) ≤
      B*(∫ z, |fderiv ℝ κ z h| ∂μ) := by
  simp_rw [smooth_deriv hk hc (hf _),smooth_deriv hk hc (hg _)]
  have hi (a : A) : Integrable (fun z => fderiv ℝ κ z h*(f a (x-z)-g a (x-z))) μ := by
    convert! (smooth_deriv_integrable hk hc (hf a) x h).sub
      (smooth_deriv_integrable hk hc (hg a) x h) using 1
    ext z
    simp only [Pi.sub_apply,mul_sub]
  have he (a : A) : (∫ z, fderiv ℝ κ z h*f a (x-z) ∂μ)-
      (∫ z, fderiv ℝ κ z h*g a (x-z) ∂μ) =
      ∫ z, fderiv ℝ κ z h*(f a (x-z)-g a (x-z)) ∂μ := by
    simp only [mul_sub]
    exact (integral_sub (smooth_deriv_integrable hk hc (hf a) x h)
      (smooth_deriv_integrable hk hc (hg a) x h)).symm
  simp_rw [he]
  rw [← integral_const_mul]
  apply integral_l1_bound _ hi (hki.const_mul B)
  filter_upwards [hb] with z hz
  by_cases hn : fderiv ℝ κ z h=0
  · simp [hn]
  · simp_rw [abs_mul,← Finset.mul_sum]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hz hn) (abs_nonneg (fderiv ℝ κ z h))

omit [NormedSpace ℝ G] [SFinite μ] in

lemma error {κ : G → ℝ} (hk : HasCompactSupport κ) (hc : Continuous κ)
    (hki : Integrable κ μ) (hkn : ∀ z, 0 ≤ κ z) (hk1 : ∫ z, κ z ∂μ=1)
    (f : A → G → ℝ) (hf : ∀ a, LocallyIntegrable (f a) μ) (x : G) {B : ℝ}
    (hb : ∀ᵐ z ∂μ, κ z ≠ 0 → ∑ a, |f a (x-z)-f a x| ≤ B) :
    (∑ a, |smooth κ (f a) μ x-f a x|) ≤ B := by
  have hi0 (a : A) : Integrable (fun z => κ z*f a (x-z)) μ :=
    hk.convolutionExists_left (ContinuousLinearMap.mul ℝ ℝ) hc (hf a) x
  have hi (a : A) : Integrable (fun z => κ z*(f a (x-z)-f a x)) μ := by
    convert! (hi0 a).sub (hki.mul_const (f a x)) using 1
    ext z
    simp only [Pi.sub_apply,mul_sub]
  have he (a : A) : smooth κ (f a) μ x-f a x = ∫ z, κ z*(f a (x-z)-f a x) ∂μ := by
    rw [smooth_eq]
    simp only [mul_sub]
    rw [integral_sub (hi0 a)
      (hki.mul_const (f a x)),integral_mul_const,hk1,one_mul]
  simp_rw [he]
  have hres := integral_l1_bound (μ := μ) _ hi (hki.const_mul B) (by
    filter_upwards [hb] with z hz
    by_cases hn : κ z=0
    · simp [hn]
    · simp_rw [abs_mul,abs_of_nonneg (hkn z),← Finset.mul_sum]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hz hn) (hkn z))
  simpa only [integral_const_mul,hk1,mul_one] using hres

end UniformSparsestCut.ConvolutionBounds

namespace UniformSparsestCut.GradientCalculus
open MeasureTheory Set
open scoped BigOperators RealInnerProductSpace
noncomputable section
variable {m : ℕ} {A : Type u7} {S : Type u8} {I : Type u9} [Fintype A] [Fintype S] [Fintype I] [DecidableEq S]
local notation "E" => EuclideanSpace ℝ (Fin m)

def vector (D : StrongDual ℝ E) : E := (InnerProductSpace.toDual ℝ E).symm D
@[simp] lemma vector_norm (D : StrongDual ℝ E) : ‖vector D‖=‖D‖ :=
  (InnerProductSpace.toDual ℝ E).symm.norm_map D
@[simp] lemma vector_inner (D : StrongDual ℝ E) (x : E) : inner ℝ (vector D) x=D x :=
  InnerProductSpace.toDual_symm_apply
lemma vector_coordinate (D : StrongDual ℝ E) (j : Fin m) :
    vector D j=D (EuclideanSpace.single j 1) := by
  have h := vector_inner D (EuclideanSpace.single j 1)
  simpa [PiLp.inner_apply,PiLp.single_apply] using h
lemma norm_le_partials (D : StrongDual ℝ E) : ‖D‖≤∑ j, |D (EuclideanSpace.single j 1)| := by
  rw [← vector_norm]
  have he : vector D=∑ j, EuclideanSpace.single j (vector D j) := by
    ext i
    simp
  calc
    _ = ‖∑ j, EuclideanSpace.single j (vector D j)‖ := congrArg norm he
    _ ≤ ∑ j, ‖EuclideanSpace.single j (vector D j)‖ := norm_sum_le _ _
    _ = _ := by simp only [PiLp.norm_single,Real.norm_eq_abs,vector_coordinate]
lemma vector_representation (D : StrongDual ℝ E) (u : I → E) (β : I → ℝ)
    (hd : D=∑ i, β i • InnerProductSpace.toDual ℝ E (u i)) :
    vector D=∑ i, β i • u i := by
  apply (InnerProductSpace.toDual ℝ E).injective
  simp only [vector,LinearIsometryEquiv.apply_symm_apply,map_sum,map_smul,hd]

lemma gradient_mismatch {κ : E → ℝ} (hk : HasCompactSupport κ) (hc : ContDiff ℝ 1 κ)
    (f g : A → E → ℝ) (hf : ∀ a, LocallyIntegrable (f a))
    (hg : ∀ a, LocallyIntegrable (g a)) (x : E) {B L : ℝ}
    (hki : ∀ j : Fin m, Integrable (fun z => |fderiv ℝ κ z (EuclideanSpace.single j 1)|))
    (hL : ∀ j : Fin m, ∫ z, |fderiv ℝ κ z (EuclideanSpace.single j 1)| = L)
    (hb : ∀ᵐ z, (∃ j : Fin m, fderiv ℝ κ z (EuclideanSpace.single j 1)≠0) →
      ∑ a, |f a (x-z)-g a (x-z)|≤B) :
    (∑ a, ‖fderiv ℝ (ConvolutionBounds.smooth κ (f a) volume) x-
      fderiv ℝ (ConvolutionBounds.smooth κ (g a) volume) x‖)≤(m:ℝ)*B*L := by
  calc
    _ ≤ ∑ a, ∑ j : Fin m, |fderiv ℝ (ConvolutionBounds.smooth κ (f a) volume) x (EuclideanSpace.single j 1)-
        fderiv ℝ (ConvolutionBounds.smooth κ (g a) volume) x (EuclideanSpace.single j 1)| := by
      apply Finset.sum_le_sum; intro a _
      exact norm_le_partials _
    _ = ∑ j : Fin m, ∑ a, |fderiv ℝ (ConvolutionBounds.smooth κ (f a) volume) x (EuclideanSpace.single j 1)-
        fderiv ℝ (ConvolutionBounds.smooth κ (g a) volume) x (EuclideanSpace.single j 1)| := Finset.sum_comm
    _ ≤ ∑ _j : Fin m, B*L := by
      apply Finset.sum_le_sum; intro j _
      rw [← hL j]
      apply ConvolutionBounds.mismatch hk hc f g hf hg x _ (hki j)
      filter_upwards [hb] with z hz hj using hz ⟨j,hj⟩
    _ = _ := by simp; ring

omit [DecidableEq S] in
lemma gradient_budget (u : S → I → E) (β : S → I → A → ℝ)
    (D : S → A → StrongDual ℝ E) (base : A → StrongDual ℝ E)
    {δ B R : ℝ} (hδ : 0≤δ)
    (hd : ∀ s a, D s a=∑ i, β s i a • InnerProductSpace.toDual ℝ E (u s i))
    (hgood : ∀ a, ∃ good : Finset S, (Fintype.card S:ℝ)/2≤good.card ∧
      ∀ s∈good, ∀ i, |base a (u s i)|≤δ*‖base a‖)
    (hβ : ∀ s, ∑ i, ∑ a, |β s i a|≤B)
    (he : ∀ s, ∑ a, ‖D s a-base a‖≤R) (hS : 0<Fintype.card S) :
    ∑ a, ‖base a‖≤2*(δ*B+R) := by
  have hvec (s : S) (a : A) : vector (base a)+vector (D s a-base a)=∑ i, β s i a • u s i := by
    change (InnerProductSpace.toDual ℝ E).symm (base a)+(InnerProductSpace.toDual ℝ E).symm (D s a-base a)=_
    rw [← map_add,add_sub_cancel]
    exact vector_representation _ _ _ (hd s a)
  have hg (a : A) : ∃ good : Finset S, (Fintype.card S:ℝ)/2≤good.card ∧
      ∀ s∈good, ∀ i, |inner ℝ (u s i) (vector (base a))|≤δ*‖vector (base a)‖ := by
    obtain ⟨good,hc,hg⟩ := hgood a
    refine ⟨good,hc,?_⟩
    intro s hs i
    rw [real_inner_comm,vector_inner,vector_norm]
    exact hg s hs i
  simpa only [vector_norm] using GradientBudget.total_gradient u β (fun a => vector (base a))
    (fun s a => vector (D s a-base a)) hδ hvec hg hβ
    (by intro s; simpa only [vector_norm] using he s) hS
end
end UniformSparsestCut.GradientCalculus

end

end OAI
