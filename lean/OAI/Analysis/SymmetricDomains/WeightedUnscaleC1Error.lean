import Mathlib
import OAI.Analysis.SymmetricDomains.WeightedTaylorUniformlyCompact

namespace OAI

noncomputable section

open Set Metric Complex
open scoped Topology
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
open scoped Topology ContDiff
open Filter
open scoped BigOperators Topology ContDiff
open Set Filter MeasureTheory
open scoped Topology
open Set Filter
open Set Metric
open scoped Topology
open Set Filter Metric
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter
open scoped Topology
open Set Filter Metric
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061
open Set Filter Metric
open scoped Topology NNReal
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def weightedUnscale (t : ℝ) (x : E × F) : E × F :=
  ((Real.sqrt t)⁻¹ • x.1,t⁻¹ • x.2)

lemma weightedUnscale_scale {t : ℝ} (ht : 0 < t) (x : E × F) :
    weightedUnscale t (weightedScale t x) = x := by
  ext <;> simp [weightedUnscale,weightedScale,ht.ne',(Real.sqrt_pos.mpr ht).ne']

lemma weightedScale_unscale {t : ℝ} (ht : 0 < t) (x : E × F) :
    weightedScale t (weightedUnscale t x) = x := by
  ext <;> simp [weightedUnscale,weightedScale,ht.ne',(Real.sqrt_pos.mpr ht).ne']

lemma weightedUnscale_sub (t : ℝ) (x y : E × F) :
    weightedUnscale t (x-y) = weightedUnscale t x-weightedUnscale t y := by
  ext <;> simp [weightedUnscale,smul_sub]

lemma weightedUnscale_norm {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (x : E × F) :
    ‖weightedUnscale t x‖ ≤ t⁻¹*‖x‖ := by
  have hs : t ≤ Real.sqrt t := by
    have hs0 := Real.sqrt_nonneg t
    have hs1 : Real.sqrt t ≤ 1 := by exact (Real.sqrt_le_one).mpr ht1
    nlinarith [Real.sq_sqrt ht.le]
  have hi : (Real.sqrt t)⁻¹ ≤ t⁻¹ := inv_anti₀ ht hs
  rw [weightedUnscale,Prod.norm_def,max_le_iff]
  constructor
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _))]
    exact (mul_le_mul_of_nonneg_right hi (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (norm_fst_le x) (inv_nonneg.mpr ht.le))
  · rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.mpr ht.le)]
    exact mul_le_mul_of_nonneg_left (norm_snd_le x) (inv_nonneg.mpr ht.le)

lemma weightedScale_uniform_zero {K : Set (E × F)} (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun t x => weightedScale t x) (fun _ => 0)
      (𝓝[>] (0 : ℝ)) K := by
  obtain ⟨M,hM,hMK⟩ := hK.exists_pos_norm_le
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hs : Tendsto (fun t : ℝ => Real.sqrt t*M) (𝓝[>] 0) (𝓝 0) := by
    simpa only [zero_mul] using sqrt_tendsto_pos.mono_right nhdsWithin_le_nhds |>.mul_const M
  filter_upwards [self_mem_nhdsWithin,(tendsto_order.mp hs).2 ε hε,
    tendsto_id.mono_left nhdsWithin_le_nhds |>.eventually (Iio_mem_nhds (show (0:ℝ) < 1 from zero_lt_one))] with t ht he ht1
  intro x hx
  have hδ : weightedScale t x = parabolicScale (Real.sqrt t) x := by
    simp only [weightedScale,parabolicScale,Real.sq_sqrt ht.le]
  rw [dist_zero_left,hδ]
  exact ((parabolicScale_norm (Real.sqrt_nonneg _) ((Real.sqrt_le_one).mpr ht1.le) x).trans
    (mul_le_mul_of_nonneg_left (hMK x hx) (Real.sqrt_nonneg _))).trans_lt he

lemma weightedScale_continuous_uniform {Y : Type*} [UniformSpace Y]
    {f : E × F → Y} (hf : ContinuousAt f 0) {K : Set (E × F)}
    (hK : Bornology.IsBounded K) :
    TendstoUniformlyOn (fun t x => f (weightedScale t x)) (fun _ => f 0)
      (𝓝[>] (0 : ℝ)) K := by
  apply tendsto_prod_principal_iff.mp
  exact hf.tendsto.comp (tendsto_prod_principal_iff.mpr (weightedScale_uniform_zero hK))

lemma weightedScale_eventually_mem {K : Set (E × F)} (hK : Bornology.IsBounded K)
    {U : Set (E × F)} (hU : U ∈ 𝓝 (0 : E × F)) :
    ∀ᶠ t : ℝ in 𝓝[>] 0, ∀ x ∈ K, weightedScale t x ∈ U := by
  have hh := (tendsto_prod_principal_iff.mpr (weightedScale_uniform_zero hK)).eventually hU
  rw [Filter.eventually_prod_principal_iff] at hh
  exact hh

theorem weightedUnscale_C1_error {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {χ : Y → E × F} {y₀ : Y} (hχ : ContDiffAt ℝ 1 χ y₀)
    {t : ℕ → ℝ} (ht : Tendsto t atTop (𝓝 0)) (htp : ∀ j, 0 < t j)
    {q q' : ℕ → Y} (hq : Tendsto q atTop (𝓝 y₀)) (hq' : Tendsto q' atTop (𝓝 y₀))
    (herr : Tendsto (fun j => (t j)⁻¹*dist (q' j) (q j)) atTop (𝓝 0)) :
    Tendsto (fun j => weightedUnscale (t j) (χ (q' j))-
      weightedUnscale (t j) (χ (q j))) atTop (𝓝 0) := by
  obtain ⟨C,V,hV,hC⟩ := hχ.exists_lipschitzOnWith
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _)
    (show ∀ᶠ j in atTop, ‖weightedUnscale (t j) (χ (q' j))-
      weightedUnscale (t j) (χ (q j))‖ ≤ (C:ℝ)*((t j)⁻¹*dist (q' j) (q j)) from ?_)
    (by simpa only [mul_zero] using herr.const_mul (C:ℝ))
  filter_upwards [hq.eventually hV,hq'.eventually hV,(tendsto_order.mp ht).2 1 zero_lt_one]
    with j hqv hqv' ht1
  rw [← weightedUnscale_sub]
  calc ‖weightedUnscale (t j) (χ (q' j)-χ (q j))‖
      ≤ (t j)⁻¹*‖χ (q' j)-χ (q j)‖ := weightedUnscale_norm (htp j) ht1.le _
    _ ≤ (t j)⁻¹*((C:ℝ)*dist (q' j) (q j)) :=
      mul_le_mul_of_nonneg_left (by simpa only [dist_eq_norm] using hC.dist_le_mul _ hqv' _ hqv)
        (inv_nonneg.mpr (htp j).le)
    _ = (C:ℝ)*((t j)⁻¹*dist (q' j) (q j)) := by ring

end Release061

end

end OAI
