import Mathlib
import OAI.Analysis.SymmetricDomains.WeightedTaylorUniformlyCompact
import OAI.Analysis.SymmetricDomains.FiniteUnion

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
open scoped BigOperators NNReal ENNReal Topology
open Set Filter
namespace Release061

section
open Set Filter Metric Topology
open scoped Classical

theorem support_normal_ray_bound
    {E F H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    [NormedAddCommGroup H] [NormedSpace ℂ H] {k : ℕ}
    (Φ : E × F → H) {p : H} (hΦ : AnalyticAt ℂ Φ 0) (hΦ0 : Φ 0=p)
    (h : Fin k → H → ℂ) (hh : ∀ i, AnalyticAt ℂ (h i) p)
    (hh0 : ∀ i, h i p=1) (w : F) :
    ∃ A > 0, ∃ τ > 0, ∀ t : ℝ, 0 < t → t < τ →
      ‖fun i => 1-h i (Φ (weightedScale t (0,w)))‖ ≤ A*t := by
  let f : E × F → (Fin k → ℂ) := fun z i => h i (Φ z)
  have hf : DifferentiableAt ℂ f 0 := (analyticAt_pi_iff.mpr
    fun i => ((hΦ0.symm ▸ hh i).comp hΦ)).differentiableAt
  obtain ⟨C,hC,hbound⟩ := hf.isBigO_sub.exists_pos
  have hr : ContinuousAt (fun t : ℝ => ((0 : E),t • w)) 0 :=
    continuousAt_const.prodMk (continuousAt_id.smul continuousAt_const)
  have he : ∀ᶠ t : ℝ in 𝓝 0,
      ‖f (0,t • w)-f 0‖ ≤ C*‖((0 : E),t • w)‖ := by
    have hr' : Tendsto (fun t : ℝ => ((0 : E),t • w)) (𝓝 0) (𝓝 0) := by
      simpa only [zero_smul,Prod.mk_zero_zero] using hr.tendsto
    have he' := hr' hbound.bound
    change ∀ᶠ t : ℝ in 𝓝 0, ‖f (0,t • w)-f 0‖ ≤ C*‖((0 : E),t • w)-0‖ at he'
    simpa only [sub_zero] using he'
  obtain ⟨τ,hτ,hball⟩ := Metric.mem_nhds_iff.mp he
  refine ⟨C*(‖w‖+1),mul_pos hC (by positivity),τ,hτ,?_⟩
  intro t ht htτ
  have htb : t ∈ ball (0 : ℝ) τ := by
    simpa only [mem_ball,dist_zero_right, Real.norm_eq_abs,abs_of_pos ht] using htτ
  have heq : weightedScale t ((0 : E),w) = (0,t • w) := by simp [weightedScale]
  have hzero : f 0 = fun _ => 1 := by funext i; exact (congrArg (h i) hΦ0).trans (hh0 i)
  have hn : ‖fun i => 1-h i (Φ (weightedScale t (0,w)))‖ = ‖f (0,t • w)-f 0‖ := by
    rw [heq,hzero,← norm_neg]
    congr 1
    funext i
    simp only [Pi.neg_apply,Pi.sub_apply,f,neg_sub]
  rw [hn]
  calc
    _ ≤ C*‖((0 : E),t • w)‖ := hball htb
    _ = C*(t*‖w‖) := by
      rw [Prod.norm_def,norm_zero,max_eq_right (norm_nonneg _),norm_smul,
        Real.norm_eq_abs,abs_of_pos ht]
    _ ≤ C*(‖w‖+1)*t := by nlinarith [hC,ht]

end

open Set Filter Topology
open scoped Classical

theorem IsSmooth.compact_support_rates {n k : ℕ} {U : Set (Affine n)}
    [Nonempty U] [PreconnectedSpace U] (hU : IsSmooth U)
    {K : Set U} (hK : IsCompact K)
    (h : Fin k → Affine n → ℂ) (hh : ∀ i, Differentiable ℂ (h i))
    (hb : ∀ i z, z ∈ U → ‖h i z‖ ≤ 1)
    (f : ℕ → U → U)
    (hf : ∀ j, HolomorphicOnSubset U (fun y => (f j y).val))
    (a : ℕ → U) (ha : ∀ j, a j ∈ K)
    (t : ℕ → ℝ) (ht : ∀ j, 0 < t j) {A : ℝ} (hA : 0 < A)
    (hbase : ∀ᶠ j in atTop, ‖fun i => 1-h i (f j (a j)).val‖ ≤ A*t j)
    {E : Set (Affine n)} (hE : IsCompact E) (hEU : E ⊆ U) :
    ∃ C > 0, ∀ᶠ j in atTop, ∀ y : U, y.val ∈ E →
      ‖fun i => 1-h i (f j y).val‖ ≤ C*t j := by
  let E' : Set U := Subtype.val ⁻¹' E
  have hE' : IsCompact E' := by
    apply Topology.IsEmbedding.subtypeVal.isCompact_iff.mpr
    have he : Subtype.val '' E'=E := by
      ext y
      constructor
      · rintro ⟨z,hz,rfl⟩; exact hz
      · intro hy; exact ⟨⟨y,hEU hy⟩,hy,rfl⟩
    rw [he]
    exact hE
  obtain ⟨B,hB,hbound⟩ := hU.compact_peak_ratio hK hE'
  refine ⟨B*A,mul_pos hB hA,?_⟩
  filter_upwards [hbase] with j hj y hy
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_pos hB hA).le (ht j).le)).mpr
  intro i
  calc
    _ ≤ B*‖1-h i (f j (a j)).val‖ := hbound (h i) (hh i) (hb i) (f j) (hf j)
      (a j) (ha j) y hy
    _ ≤ B*‖fun i => 1-h i (f j (a j)).val‖ :=
      mul_le_mul_of_nonneg_left (norm_le_pi_norm (fun i => (1 : ℂ)-h i (f j (a j)).val) i) hB.le
    _ ≤ B*(A*t j) := mul_le_mul_of_nonneg_left hj hB.le
    _ = (B*A)*t j := by ring

end Release061

end

end OAI
