import Mathlib
import OAI.Analysis.SymmetricDomains.WeightedUnscaleC1Error
import OAI.Analysis.SymmetricDomains.IndependentSupportCoercivity

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

section
open Set Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem weightedUnscale_bound {M t : ℝ} (hM : 0 ≤ M) (ht : 0 < t)
    {x : E × F} (hx : ‖x‖^2 ≤ M*t) (hw : ‖x.2‖ ≤ M*t) :
    ‖weightedUnscale t x‖ ≤ max (Real.sqrt M) M := by
  have hs : ‖x.1‖ ≤ Real.sqrt M*Real.sqrt t := by
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [mul_pow,Real.sq_sqrt hM,Real.sq_sqrt ht.le]
    exact ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (norm_fst_le x)).trans hx
  rw [weightedUnscale,Prod.norm_def,max_le_iff]
  constructor
  · have hsr := Real.sqrt_pos.mpr ht
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hsr),mul_comm,←div_eq_mul_inv]
    exact ((div_le_iff₀ hsr).mpr hs).trans (le_max_left _ _)
  · rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr ht),mul_comm,←div_eq_mul_inv]
    exact ((div_le_iff₀ ht).mpr hw).trans (le_max_right _ _)

theorem independent_support_scaled_bound
    [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E] {k : ℕ}
    (β : Fin (k+1) → Fin (k+1) → ℝ) (hβ : LinearIndependent ℝ β)
    (h : Fin (k+1) → E × (Fin (k+1) → ℂ) → ℂ)
    (hh : ∀ i, AnalyticAt ℂ (h i) 0) (hh0 : ∀ i, h i 0 = 1)
    (hder : ∀ i x, fderiv ℂ (fun y => Complex.log (h i y)) 0 x =
      Complex.I*∑ j, (β i j : ℂ)*x.2 j)
    (D : Set (E × (Fin (k+1) → ℂ))) {c : ℝ} (hc : 0 < c)
    (hpeak : ∀ x ∈ D, ‖h 0 x‖ ≤ Real.exp (-c*‖x‖^2)) :
    ∃ C > 0, ∃ V ∈ 𝓝 (0 : E × (Fin (k+1) → ℂ)),
      ∀ A ≥ 0, ∀ t > 0, ∀ x ∈ V, x ∈ D →
        ‖fun i => 1-h i x‖ ≤ A*t →
        ‖weightedUnscale t x‖ ≤ max (Real.sqrt (C*A)) (C*A) := by
  obtain ⟨C,hC,V,hV,hb⟩ := independent_support_coercivity β hβ h hh hh0 hder D hc hpeak
  refine ⟨C,hC,V,hV,?_⟩
  intro A hA t ht x hx hxD hd
  have H := hb x hx hxD
  have hd' : C*‖fun i => 1-h i x‖ ≤ (C*A)*t := by
    calc _ ≤ C*(A*t) := mul_le_mul_of_nonneg_left hd hC.le
         _ = _ := by ring
  exact weightedUnscale_bound (mul_nonneg hC.le hA) ht (H.1.trans hd') (H.2.trans hd')

end

open Set Filter Asymptotics
open scoped Topology

theorem gaussian_peak_localizes {E : Type*} [NormedAddCommGroup E]
    (h : E → ℂ) (D : Set E) (p : E)
    (hp : ∀ q ∈ D, ‖h q‖ ≤ Real.exp (-(‖q-p‖^2)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ q ∈ D, ‖1-h q‖ < δ → ‖q-p‖ < ε := by
  refine ⟨1-Real.exp (-(ε^2)),?_,?_⟩
  · have he : Real.exp (-(ε^2)) < 1 :=
      Real.exp_lt_one_iff.mpr (neg_neg_of_pos (sq_pos_of_pos hε))
    linarith
  · intro q hq hd
    by_contra hn
    have he : ε^2 ≤ ‖q-p‖^2 := (sq_le_sq₀ hε.le (norm_nonneg _)).mpr (le_of_not_gt hn)
    have hn' : ‖h q‖ ≤ Real.exp (-(ε^2)) :=
      (hp q hq).trans (Real.exp_le_exp.mpr (neg_le_neg he))
    have htri : (1 : ℝ) ≤ ‖1-h q‖+‖h q‖ := by
      simpa only [norm_one] using norm_le_norm_sub_add (1 : ℂ) (h q)
    linarith

theorem gaussian_peak_eventually_mem {E I A : Type*} [NormedAddCommGroup E]
    {l : Filter I} (h : E → ℂ) (D : Set E) (p : E)
    (hp : ∀ q ∈ D, ‖h q‖ ≤ Real.exp (-(‖q-p‖^2)))
    (x : I → A → E) (K : Set A) (t : I → ℝ) (ht : Tendsto t l (𝓝 0))
    {C : ℝ} (hx : ∀ᶠ i in l, ∀ a ∈ K, x i a ∈ D ∧ ‖1-h (x i a)‖ ≤ C*t i)
    {V : Set E} (hV : V ∈ 𝓝 p) :
    ∀ᶠ i in l, ∀ a ∈ K, x i a ∈ V := by
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp hV
  obtain ⟨δ,hδ,hd⟩ := gaussian_peak_localizes h D p hp hε
  have ht' : Tendsto (fun i => C*t i) l (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul ht
  have he := ht' (gt_mem_nhds hδ)
  filter_upwards [hx,he] with i hi hit a ha
  apply hball
  rw [Metric.mem_ball,dist_eq_norm]
  exact hd _ (hi a ha).1 ((hi a ha).2.trans_lt hit)

theorem inverse_chart_gaussian {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    {Φ : E → F} {Ψ : F → E} {p : F}
    (hΦ : ContinuousAt Φ 0) (hΦ0 : Φ 0 = p)
    (hΨ : DifferentiableAt ℂ Ψ p) (hΨ0 : Ψ p = 0)
    (hinv : ∀ᶠ x in 𝓝 (0 : E), Ψ (Φ x) = x)
    (h : F → ℂ) (D : Set F)
    (hpeak : ∀ q ∈ D, ‖h q‖ ≤ Real.exp (-(‖q-p‖^2))) :
    ∃ c > 0, ∀ᶠ x in 𝓝 (0 : E), Φ x ∈ D →
      ‖h (Φ x)‖ ≤ Real.exp (-c*‖x‖^2) := by
  obtain ⟨C,hC,hbound⟩ := hΨ.isBigO_sub.exists_pos
  have he : ∀ᶠ x in 𝓝 (0 : E), ‖Ψ (Φ x)‖ ≤ C*‖Φ x-p‖ := by
    have h := ((hΦ0 ▸ hΦ.tendsto) hbound.bound)
    change ∀ᶠ x in 𝓝 (0 : E), ‖Ψ (Φ x)-Ψ p‖ ≤ C*‖Φ x-p‖ at h
    simpa only [hΨ0,sub_zero] using h
  refine ⟨1/C^2,by positivity,?_⟩
  filter_upwards [he,hinv] with x hx hi hxD
  rw [hi] at hx
  have hs : ‖x‖^2 ≤ C^2*‖Φ x-p‖^2 := by
    simpa only [mul_pow] using (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hx
  have hs' : (1/C^2)*‖x‖^2 ≤ ‖Φ x-p‖^2 := by
    rw [one_div,mul_comm,←div_eq_mul_inv]
    exact (div_le_iff₀ (sq_pos_of_pos hC)).mpr (by nlinarith [hs])
  exact (hpeak _ hxD).trans (Real.exp_le_exp.mpr (by nlinarith [hs']))

end Release061

end

end OAI
