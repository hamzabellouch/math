import OAI.Analysis.NumericalRange.CircleIntegrals

namespace OAI

noncomputable section

universe u_35 u_36 u_37 u_38 u_39

open Set Filter Metric Complex
open scoped Topology ComplexConjugate
open MeasureTheory Set Complex
open scoped Topology Real
open MeasureTheory Set Metric Complex Filter
open scoped Topology

open MeasureTheory Set Filter
open scoped ENNReal NNReal InnerProductSpace
namespace CompleteCrouzeix

section

section Jensen
variable {X : Type u_35} {E : Type u_36} [MeasurableSpace X] {μ : Measure X}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma weighted_norm_integral_sq_le {k : X → ℝ} {f : X → E}
    (hk : Integrable k μ) (hk0 : ∀ x, 0 ≤ k x) (hk1 : ∫ x, k x ∂μ = 1)
    (hf : Integrable (fun x => k x • f x) μ)
    (hf2 : Integrable (fun x => k x * ‖f x‖^2) μ) :
    ‖∫ x, k x • f x ∂μ‖^2 ≤ ∫ x, k x * ‖f x‖^2 ∂μ := by
  let v := ∫ x, k x • f x ∂μ
  have hl : Integrable (fun x => 2 * inner ℝ v (k x • f x) - k x * ‖v‖^2) μ :=
    ((hf.const_inner v).const_mul 2).sub (hk.mul_const _)
  have hle : ∫ x, (2 * inner ℝ v (k x • f x) - k x * ‖v‖^2) ∂μ ≤
      ∫ x, k x * ‖f x‖^2 ∂μ := by
    apply integral_mono hl hf2
    intro x
    dsimp only
    rw [real_inner_smul_right]
    have hs := norm_sub_sq_real v (f x)
    have h := mul_nonneg (hk0 x) (sq_nonneg ‖v-f x‖)
    rw [hs] at h
    nlinarith
  rw [integral_sub ((hf.const_inner v).const_mul 2) (hk.mul_const _),
    integral_const_mul, integral_mul_const, integral_inner hf, hk1,
    real_inner_self_eq_norm_sq] at hle
  dsimp [v] at *
  linarith
end Jensen

variable {X : Type u_37} [MeasurableSpace X] (μ : Measure X)

structure MarkovKernel where
  kernel : X → X → ℝ
  measurable : Measurable (Function.uncurry kernel)
  nonneg : ∀ x y, 0 ≤ kernel x y
  bound : ∃ C : ℝ, ∀ x y, ‖kernel x y‖ ≤ C
  row : ∀ x, ∫ y, kernel x y ∂μ = 1
  column : ∀ y, ∫ x, kernel x y ∂μ = 1

namespace MarkovKernel
variable {μ} (K : MarkovKernel μ) [instIsFiniteMeasureΜ : IsFiniteMeasure μ]
  {E : Type u_38} [NormedAddCommGroup E] [instInnerProductSpaceℂE : InnerProductSpace ℂ E] [instCompleteSpaceE : CompleteSpace E]

lemma row_measurable
    {X : Type u_37} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (K : CompleteCrouzeix.MarkovKernel μ) [MeasureTheory.IsFiniteMeasure μ] (x : X) :
    Measurable (K.kernel x) :=
  K.measurable.comp measurable_prodMk_left

lemma row_integrable (x : X) : Integrable (K.kernel x) μ := by
  obtain ⟨C,hC⟩ := K.bound
  exact Integrable.of_bound (K.row_measurable x).aestronglyMeasurable C
    (Filter.Eventually.of_forall (hC x))

lemma integrable_row_smul
    {X : Type u_37} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (K : CompleteCrouzeix.MarkovKernel μ) [MeasureTheory.IsFiniteMeasure μ] {E : Type u_38}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : Lp E 2 μ) (x : X) :
    Integrable (fun y => K.kernel x y • u y) μ := by
  obtain ⟨C,hC⟩ := K.bound
  exact ((Lp.memLp u).integrable (by norm_num)).bdd_smul (𝕜 := ℝ) (φ := K.kernel x) C
    (K.row_measurable x).aestronglyMeasurable (Filter.Eventually.of_forall (hC x))

lemma integrable_sq_norm
    {X : Type u_37} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasure μ] {E : Type u_38} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (u : Lp E 2 μ) : Integrable (fun y => ‖u y‖^2) μ :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable u)).mp (Lp.memLp u)

lemma integrable_row_sq (u : Lp E 2 μ) (x : X) :
    Integrable (fun y => K.kernel x y * ‖u y‖^2) μ := by
  obtain ⟨C,hC⟩ := K.bound
  exact (integrable_sq_norm u).bdd_mul (K.row_measurable x).aestronglyMeasurable
    (Filter.Eventually.of_forall (hC x))

lemma integrable_prod_smul
    {X : Type u_37} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (K : CompleteCrouzeix.MarkovKernel μ) [MeasureTheory.IsFiniteMeasure μ] {E : Type u_38}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : Lp E 2 μ) :
    Integrable (fun p : X × X => K.kernel p.1 p.2 • u p.2) (μ.prod μ) := by
  obtain ⟨C,hC⟩ := K.bound
  exact (((Lp.memLp u).integrable (by norm_num)).comp_snd μ).bdd_smul (𝕜 := ℝ) (φ := Function.uncurry K.kernel) C
    K.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun p => hC p.1 p.2)

lemma integrable_prod_sq (u : Lp E 2 μ) :
    Integrable (fun p : X × X => K.kernel p.1 p.2 * ‖u p.2‖^2) (μ.prod μ) := by
  obtain ⟨C,hC⟩ := K.bound
  exact ((integrable_sq_norm u).comp_snd μ).bdd_mul
    K.measurable.aestronglyMeasurable (Filter.Eventually.of_forall fun p => hC p.1 p.2)

def applyFun (u : Lp E 2 μ) (x : X) : E := ∫ y, K.kernel x y • u y ∂μ

lemma applyFun_aestronglyMeasurable (u : Lp E 2 μ) :
    AEStronglyMeasurable (K.applyFun u) μ :=
  (K.integrable_prod_smul u).aestronglyMeasurable.integral_prod_right'

lemma applyFun_sq_le (u : Lp E 2 μ) (x : X) :
    ‖K.applyFun u x‖^2 ≤ ∫ y, K.kernel x y * ‖u y‖^2 ∂μ := by
  let := InnerProductSpace.rclikeToReal ℂ E
  exact weighted_norm_integral_sq_le (K.row_integrable x) (K.nonneg x) (K.row x)
    (K.integrable_row_smul u x) (K.integrable_row_sq u x)

lemma applyFun_memLp (u : Lp E 2 μ) : MemLp (K.applyFun u) 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm (K.applyFun_aestronglyMeasurable u)).mpr
  apply (K.integrable_prod_sq u).integral_prod_left.mono'
    ((K.applyFun_aestronglyMeasurable u).norm.pow 2)
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact K.applyFun_sq_le u x

def applyLp (u : Lp E 2 μ) : Lp E 2 μ :=
  (K.applyFun_memLp u).toLp (K.applyFun u)

lemma applyLp_ae (u : Lp E 2 μ) : ⇑(K.applyLp u) =ᵐ[μ] K.applyFun u :=
  (K.applyFun_memLp u).coeFn_toLp

lemma l2_norm_sq
    {X : Type u_37} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    [MeasureTheory.IsFiniteMeasure μ] {E : Type u_38} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [CompleteSpace E] (u : Lp E 2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  let := InnerProductSpace.rclikeToReal ℂ E
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

lemma applyLp_norm_sq_le (u : Lp E 2 μ) : ‖K.applyLp u‖^2 ≤ ‖u‖^2 := by
  rw [l2_norm_sq, l2_norm_sq]
  have he : ∫ x, ‖K.applyLp u x‖^2 ∂μ = ∫ x, ‖K.applyFun u x‖^2 ∂μ := by
    apply integral_congr_ae
    filter_upwards [K.applyLp_ae u] with x hx using congrArg (fun z : E => ‖z‖^2) hx
  rw [he]
  calc _ ≤ ∫ x, ∫ y, K.kernel x y * ‖u y‖^2 ∂μ ∂μ := by
         apply integral_mono
         · exact (memLp_two_iff_integrable_sq_norm
             (K.applyFun_aestronglyMeasurable u)).mp (K.applyFun_memLp u)
         · exact (K.integrable_prod_sq u).integral_prod_left
         · exact K.applyFun_sq_le u
       _ = ∫ y, ‖u y‖^2 ∂μ := by
         rw [integral_integral_swap (K.integrable_prod_sq u)]
         congr 1
         funext y
         rw [integral_mul_const, K.column y, one_mul]

lemma applyLp_norm_le (u : Lp E 2 μ) : ‖K.applyLp u‖ ≤ ‖u‖ := by
  have h := K.applyLp_norm_sq_le u
  nlinarith [norm_nonneg (K.applyLp u), norm_nonneg u]

lemma applyFun_add (u v : Lp E 2 μ) (x : X) :
    K.applyFun (u+v) x = K.applyFun u x + K.applyFun v x := by
  unfold applyFun
  calc _ = ∫ y, K.kernel x y • (u y+v y) ∂μ := by
         apply integral_congr_ae
         filter_upwards [Lp.coeFn_add u v] with y hy
         rw [hy]; rfl
       _ = _ := by
         simp_rw [smul_add]
         exact integral_add (K.integrable_row_smul u x) (K.integrable_row_smul v x)

lemma applyFun_smul
    {X : Type u_37} [MeasurableSpace X] {μ : MeasureTheory.Measure X}
    (K : CompleteCrouzeix.MarkovKernel μ) [MeasureTheory.IsFiniteMeasure μ] {E : Type u_38}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (c : ℂ) (u : Lp E 2 μ)
    (x : X) :
    K.applyFun (c • u) x = c • K.applyFun u x := by
  unfold applyFun
  calc _ = ∫ y, c • (K.kernel x y • u y) ∂μ := by
         apply integral_congr_ae
         filter_upwards [Lp.coeFn_smul c u] with y hy
         rw [hy]
         exact smul_comm _ _ _
       _ = _ := integral_smul c _

lemma applyLp_add (u v : Lp E 2 μ) : K.applyLp (u+v) = K.applyLp u+K.applyLp v := by
  apply Lp.ext
  filter_upwards [K.applyLp_ae (u+v), K.applyLp_ae u, K.applyLp_ae v,
    Lp.coeFn_add (K.applyLp u) (K.applyLp v)] with x huv hu hv ha
  rw [huv,ha]
  change K.applyFun (u+v) x = K.applyLp u x+K.applyLp v x
  rw [hu,hv,K.applyFun_add]

lemma applyLp_smul (c : ℂ) (u : Lp E 2 μ) : K.applyLp (c • u) = c • K.applyLp u := by
  apply Lp.ext
  filter_upwards [K.applyLp_ae (c • u), K.applyLp_ae u,
    Lp.coeFn_smul c (K.applyLp u)] with x hcu hu hc
  rw [hcu,hc]
  change K.applyFun (c • u) x = c • K.applyLp u x
  rw [hu,K.applyFun_smul]

def toCLM : Lp E 2 μ →L[ℂ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := K.applyLp
      map_add' := K.applyLp_add
      map_smul' := K.applyLp_smul }
    1 (fun u => by simpa using K.applyLp_norm_le u)

@[simp] lemma toCLM_apply (u : Lp E 2 μ) : K.toCLM u = K.applyLp u := rfl

lemma toCLM_norm_le : ‖(K.toCLM : Lp E 2 μ →L[ℂ] Lp E 2 μ)‖ ≤ 1 := by
  change ‖LinearMap.mkContinuous _ 1 _‖ ≤ 1
  exact LinearMap.mkContinuous_norm_le _ (by norm_num) _

lemma applyFun_integral (u : Lp E 2 μ) :
    ∫ x, K.applyFun u x ∂μ = ∫ y, u y ∂μ := by
  unfold applyFun
  rw [integral_integral_swap (K.integrable_prod_smul u)]
  congr 1
  funext y
  rw [integral_smul_const, K.column y, one_smul]

lemma toCLM_integral (u : Lp E 2 μ) :
    ∫ x, K.toCLM u x ∂μ = ∫ y, u y ∂μ := by
  rw [show (∫ x, K.toCLM u x ∂μ) = ∫ x, K.applyFun u x ∂μ from
    integral_congr_ae (K.applyLp_ae u)]
  exact K.applyFun_integral u

lemma applyFun_const (c : E) (x : X) :
    K.applyFun (Lp.const 2 μ c) x = c := by
  unfold applyFun
  calc _ = ∫ y, K.kernel x y • c ∂μ := by
         apply integral_congr_ae
         filter_upwards [Lp.coeFn_const (p := 2) (μ := μ) c] with y hy
         rw [hy]; rfl
       _ = c := by rw [integral_smul_const, K.row x, one_smul]

lemma toCLM_const (c : E) : K.toCLM (Lp.const 2 μ c) = Lp.const 2 μ c := by
  apply Lp.ext
  filter_upwards [K.applyLp_ae (Lp.const 2 μ c), Lp.coeFn_const (p := 2) (μ := μ) c]
    with x hx hc
  exact hx.trans ((K.applyFun_const c x).trans hc.symm)

lemma toCLM_compLpL_real {F : Type u_39} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (L : E →L[ℝ] F) (u : Lp E 2 μ) :
    K.toCLM (L.compLpL 2 μ u) = L.compLpL 2 μ (K.toCLM u) := by
  apply Lp.ext
  filter_upwards [K.applyLp_ae (L.compLpL 2 μ u),
    L.coeFn_compLpL (K.toCLM u), K.applyLp_ae u] with x hx hL hu
  change K.applyLp (L.compLpL 2 μ u) x = _
  rw [hx,hL]
  change K.applyFun (L.compLpL 2 μ u) x = L (K.applyLp u x)
  rw [hu]
  unfold applyFun
  rw [← L.integral_comp_comm (K.integrable_row_smul u x)]
  apply integral_congr_ae
  filter_upwards [L.coeFn_compLpL u] with y hy
  rw [hy, map_smul]

end MarkovKernel
end
open MeasureTheory Set Metric Complex ComplexConjugate
open scoped Topology Real
local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

structure AnalyticBidiskKernel where
  B : ℂ → ℂ → ℂ
  continuous : ContinuousOn (Function.uncurry B)
    (closedBall 0 1 ×ˢ closedBall 0 1)
  left : ∀ y ∈ closedBall 0 1, AnalyticOnNhd ℂ (fun x => B x y) (closedBall 0 1)
  right : ∀ x ∈ closedBall 0 1, AnalyticOnNhd ℂ (B x) (closedBall 0 1)
  zero_left : ∀ y, B 0 y = 0
  zero_right : ∀ x, B x 0 = 0
  positive : ∀ w t : Circle, 0 ≤ 1 + 2 * (B (w : ℂ)⁻¹ (t : ℂ)⁻¹).re

namespace AnalyticBidiskKernel
variable (K : AnalyticBidiskKernel)

def circleB (w t : UnitAddCircle) : ℂ := K.B (w.toCircle : ℂ)⁻¹ (t.toCircle : ℂ)⁻¹

def kernel (w t : UnitAddCircle) : ℝ := 1 + 2 * (K.circleB w t).re

lemma norm_inv_circle (t : UnitAddCircle) : ‖(t.toCircle : ℂ)⁻¹‖ = 1 := by
  simp [Circle.norm_coe]

lemma inv_circle_mem (t : UnitAddCircle) : (t.toCircle : ℂ)⁻¹ ∈ closedBall 0 1 := by
  simp [mem_closedBall, dist_zero_right]

lemma continuous_circleB : Continuous (Function.uncurry K.circleB) := by
  have hi : Continuous (fun t : UnitAddCircle => (t.toCircle : ℂ)⁻¹) :=
    continuous_subtype_val.comp AddCircle.continuous_toCircle.inv
  apply K.continuous.comp_continuous ((hi.comp continuous_fst).prodMk (hi.comp continuous_snd))
  intro p
  exact ⟨inv_circle_mem p.1, inv_circle_mem p.2⟩

lemma continuous_kernel : Continuous (Function.uncurry K.kernel) :=
  continuous_const.add (continuous_const.mul (Complex.continuous_re.comp K.continuous_circleB))

lemma circleB_row_integral (w : UnitAddCircle) :
    (∫ t, K.circleB w t ∂AddCircle.haarAddCircle) = 0 := by
  unfold circleB
  rw [integral_reciprocal_analytic (K.right _ (inv_circle_mem w)), K.zero_right]

lemma circleB_column_integral (t : UnitAddCircle) :
    (∫ w, K.circleB w t ∂AddCircle.haarAddCircle) = 0 := by
  unfold circleB
  rw [integral_reciprocal_analytic (K.left _ (inv_circle_mem t)), K.zero_left]

lemma kernel_row_integral (w : UnitAddCircle) :
    (∫ t, K.kernel w t ∂AddCircle.haarAddCircle) = 1 := by
  have hc : Continuous (K.circleB w) :=
    K.continuous_circleB.comp (continuous_const.prodMk continuous_id)
  have hi := hc.integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  change (∫ t, (1 + 2 * (K.circleB w t).re) ∂AddCircle.haarAddCircle) = 1
  have hir : Integrable (fun t => (K.circleB w t).re) AddCircle.haarAddCircle := hi.re
  have he : (∫ t, (K.circleB w t).re ∂AddCircle.haarAddCircle) =
      (∫ t, K.circleB w t ∂AddCircle.haarAddCircle).re := integral_re hi
  rw [integral_add (integrable_const (1 : ℝ))
    (hir.const_mul 2), integral_const_mul, he, K.circleB_row_integral]
  simp

lemma kernel_column_integral (t : UnitAddCircle) :
    (∫ w, K.kernel w t ∂AddCircle.haarAddCircle) = 1 := by
  have hc : Continuous (fun w => K.circleB w t) :=
    K.continuous_circleB.comp (continuous_id.prodMk continuous_const)
  have hi := hc.integrable_of_hasCompactSupport
    (μ := AddCircle.haarAddCircle) (HasCompactSupport.of_compactSpace _)
  change (∫ w, (1 + 2 * (K.circleB w t).re) ∂AddCircle.haarAddCircle) = 1
  have hir : Integrable (fun w => (K.circleB w t).re) AddCircle.haarAddCircle := hi.re
  have he : (∫ w, (K.circleB w t).re ∂AddCircle.haarAddCircle) =
      (∫ w, K.circleB w t ∂AddCircle.haarAddCircle).re := integral_re hi
  rw [integral_add (integrable_const (1 : ℝ))
    (hir.const_mul 2), integral_const_mul, he, K.circleB_column_integral]
  simp

def toMarkovKernel : MarkovKernel (@AddCircle.haarAddCircle 1 inferInstance) where
  kernel := K.kernel
  measurable := K.continuous_kernel.measurable
  nonneg w t := K.positive w.toCircle t.toCircle
  bound := by
    obtain ⟨C,hC⟩ := isCompact_univ.exists_bound_of_continuousOn K.continuous_kernel.continuousOn
    exact ⟨C, fun w t => hC (w,t) (mem_univ _)⟩
  row := K.kernel_row_integral
  column := K.kernel_column_integral

lemma circleB_right_nonpos_fourier (w : UnitAddCircle) (n : ℤ) (hn : n ≤ 0) :
    (∫ t, K.circleB w t * fourier n t ∂AddCircle.haarAddCircle) = 0 := by
  cases n with
  | ofNat k =>
    have hk : k = 0 := Int.natCast_nonpos_iff.mp hn
    subst k
    simpa using K.circleB_row_integral w
  | negSucc k =>
    change (∫ t, K.circleB w t * fourier (-(↑(k+1) : ℤ)) t ∂AddCircle.haarAddCircle) = 0
    simp only [fourier_neg_natCast_toCircle]
    simpa only [circleB, mul_comm] using
      integral_reciprocal_analytic_mul_inv_pow (K.right _ (inv_circle_mem w))
        (Nat.succ_ne_zero k)

lemma circleB_left_nonpos_fourier (t : UnitAddCircle) (n : ℤ) (hn : n ≤ 0) :
    (∫ w, K.circleB w t * fourier n w ∂AddCircle.haarAddCircle) = 0 := by
  cases n with
  | ofNat k =>
    have hk : k = 0 := Int.natCast_nonpos_iff.mp hn
    subst k
    simpa using K.circleB_column_integral t
  | negSucc k =>
    change (∫ w, K.circleB w t * fourier (-(↑(k+1) : ℤ)) w ∂AddCircle.haarAddCircle) = 0
    simp only [fourier_neg_natCast_toCircle]
    simpa only [circleB, mul_comm] using
      integral_reciprocal_analytic_mul_inv_pow (K.left _ (inv_circle_mem t))
        (Nat.succ_ne_zero k)

lemma conj_circleB_right_nonneg_fourier (w : UnitAddCircle) (n : ℤ) (hn : 0 ≤ n) :
    (∫ t, conj (K.circleB w t) * fourier n t ∂AddCircle.haarAddCircle) = 0 := by
  have h := congrArg conj (K.circleB_right_nonpos_fourier w (-n) (by omega))
  rw [← integral_conj] at h
  simpa only [map_mul, ← fourier_neg, neg_neg, map_zero] using h

lemma conj_circleB_left_nonneg_fourier (t : UnitAddCircle) (n : ℤ) (hn : 0 ≤ n) :
    (∫ w, conj (K.circleB w t) * fourier n w ∂AddCircle.haarAddCircle) = 0 := by
  have h := congrArg conj (K.circleB_left_nonpos_fourier t (-n) (by omega))
  rw [← integral_conj] at h
  simpa only [map_mul, ← fourier_neg, neg_neg, map_zero] using h

end AnalyticBidiskKernel
end CompleteCrouzeix

end

end OAI
