import Mathlib
import OAI.Analysis.SymmetricDomains.BishopTransverseNoncollapse

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
namespace Release061.Wiener
open scoped Topology
open Set Filter Metric

theorem bishopData_noncollapse {k : ℕ} [NeZero k]
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ} {ε : ℝ}
    (D : LocalBishopData k f ε) {Ω : Set (Fin k → ℂ)}
    (hΩ : IsOpen Ω) (hCP : DiscContinuityWithin k Ω ε)
    {u₀ : ℝ} (hu₀ : 0 < u₀)
    (hG : ContinuousOn (graphPoint f) (closedBall 0 ε ×ˢ Icc 0 u₀))
    (hgraph : ∀ x ∈ closedBall 0 ε, ∀ u ∈ Ioo 0 u₀, graphPoint f (x,u) ∈ Ω) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
      ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω := by
  let L := max 1 ‖D.lam‖
  have hL : 1 ≤ L := le_max_left _ _
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨a,ha,htr⟩ := Metric.mem_nhds_iff.mp D.transverse
  let α := min (min D.radius a) (u₀/(4*L))/2
  have hα : 0 < α := half_pos (lt_min (lt_min D.radius_pos ha) (div_pos hu₀ (by positivity)))
  have hαmin : α < min (min D.radius a) (u₀/(4*L)) := by dsimp [α] at hα ⊢; linarith
  have hαr : α < D.radius := (hαmin.trans_le (min_le_left _ _)).trans_le (min_le_left _ _)
  have hαa : α < a := (hαmin.trans_le (min_le_left _ _)).trans_le (min_le_right _ _)
  have hαu : α*(4*L) < u₀ :=
    (lt_div_iff₀ (by positivity)).mp (hαmin.trans_le (min_le_right _ _))
  let d := min (D.radius/2) (u₀/4)
  have hd : 0 < d := lt_min (half_pos D.radius_pos) (by positivity)
  have hdr : d < D.radius := (min_le_left _ _).trans_lt (by linarith [D.radius_pos])
  have hdu : d ≤ u₀/4 := min_le_right _ _
  have hu : α*L+d < u₀ := by nlinarith
  apply bishop_transverse_noncollapse D hΩ hCP hα hαr hd hdr hL hu
  · apply hG.mono
    intro q hq
    exact ⟨hq.1,⟨hα.le.trans hq.2.1,by
      have hαL : α ≤ α*L := by nlinarith
      linarith [hq.2.2]⟩⟩
  · exact hgraph
  · intro θ
    exact (le_abs_self _).trans ((realEvaluation_bound θ D.lam).trans (le_max_right _ _))
  · exact htr (by simpa only [mem_ball,Real.dist_eq,sub_zero,abs_of_pos hα] using hαa)

lemma graphPoint_contDiffAt {k : ℕ} {f : (Fin (k+1) → ℝ) → Fin k → ℝ}
    (hf : AnalyticAt ℝ f 0) :
    ContDiffAt ℝ 1 (graphPoint f) (0 : (Fin k → ℝ) × ℝ) := by
  have hP : ContDiffAt ℝ 1 (fun q : (Fin k → ℝ) × ℝ => (Fin.cons q.2 q.1 : Fin (k+1) → ℝ)) 0 := by
    apply contDiffAt_pi.mpr
    intro i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp only [Fin.cons_zero,Fin.cons_succ] <;> fun_prop
  have hzero : (Fin.cons (0 : ℝ) (0 : Fin k → ℝ) : Fin (k+1) → ℝ) = 0 := by ext i; refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  have hf' : ContDiffAt ℝ 1 (fun q : (Fin k → ℝ) × ℝ => f (Fin.cons q.2 q.1)) 0 := by
    have hfa : ContDiffAt ℝ 1 f (Fin.cons (0 : ℝ) (0 : Fin k → ℝ)) := by rw [hzero]; exact hf.contDiffAt
    exact hfa.comp (f := fun q : (Fin k → ℝ) × ℝ => (Fin.cons q.2 q.1 : Fin (k+1) → ℝ)) (0 : (Fin k → ℝ) × ℝ) hP
  apply contDiffAt_pi.mpr
  intro i
  exact (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (by fun_prop)).add
    (contDiffAt_const.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp 0 (contDiffAt_pi.mp hf' i)))

lemma discContinuityWithin_mono {k : ℕ} {Ω : Set (Fin k → ℂ)} {ε r : ℝ}
    (h : DiscContinuityWithin k Ω ε) (hr : r ≤ ε) : DiscContinuityWithin k Ω r := by
  intro A hA hAh hsmall hbd hstart
  exact h A hA hAh (fun s z => (hsmall s z).trans_le hr) hbd hstart

theorem interior_balls_from_analytic_graphs {k : ℕ} {Ω : Set (Fin k → ℂ)}
    (hΩ : IsOpen Ω) {ε : ℝ} (hε : 0 < ε) (hCP : DiscContinuityWithin k Ω ε)
    {f : (Fin (k+1) → ℝ) → Fin k → ℝ} (hf : AnalyticAt ℝ f 0)
    (hf0 : ∀ᶠ x in 𝓝 (0 : Fin k → ℝ), f (Fin.cons 0 x) = 0)
    (hgraph : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), 0 < q.2 → graphPoint f q ∈ Ω) :
    ∃ c C t₀ : ℝ, 0 < c ∧ 0 < C ∧ 0 < t₀ ∧ ∀ t, 0 < t → t < t₀ →
      ∃ a : Fin k → ℂ, ‖a‖ ≤ C*t ∧ ball a (c*t) ⊆ Ω := by
  have hG := graphPoint_contDiffAt hf
  obtain ⟨V,hV,hGV⟩ := hG.contDiffOn (m := 1) (by norm_num) (by norm_num)
  have hall : ∀ᶠ q in 𝓝 (0 : (Fin k → ℝ) × ℝ), q ∈ V ∧
      (0 < q.2 → graphPoint f q ∈ Ω) := Filter.Eventually.and hV hgraph
  obtain ⟨r,hr,hrs⟩ := Metric.mem_nhds_iff.mp hall
  let e := min (ε/2) (r/2)
  have he : 0 < e := lt_min (half_pos hε) (half_pos hr)
  have heε : e ≤ ε := (min_le_left _ _).trans (by linarith)
  have her : e < r := (min_le_right _ _).trans_lt (by linarith)
  have hproduct : closedBall (0 : Fin k → ℝ) e ×ˢ Icc 0 (r/2) ⊆ ball 0 r := by
    rintro ⟨x,u⟩ ⟨hx,hu⟩
    rw [mem_ball,dist_zero_right,Prod.norm_def,max_lt_iff,Real.norm_eq_abs,abs_of_nonneg hu.1]
    exact ⟨(mem_closedBall_zero_iff.mp hx).trans_lt her,hu.2.trans_lt (by linarith)⟩
  have hgraphs : ∀ x ∈ closedBall 0 e, ∀ u ∈ Ioo 0 (r/2), graphPoint f (x,u) ∈ Ω := by
    intro x hx u hu
    exact (hrs (hproduct ⟨hx,⟨hu.1.le,hu.2.le⟩⟩)).2 hu.1
  by_cases hk : k = 0
  · subst k
    have h0 : (0 : Fin 0 → ℂ) ∈ Ω := by
      have hi := hgraphs 0 (mem_closedBall_self he.le) (r/4) ⟨by positivity,by linarith⟩
      simpa only [Subsingleton.elim (graphPoint f ((0 : Fin 0 → ℝ),r/4)) 0] using hi
    refine ⟨1,1,1,by norm_num,by norm_num,by norm_num,?_⟩
    intro t ht _
    refine ⟨(0 : Fin 0 → ℂ),by simpa only [norm_zero,one_mul] using ht.le,?_⟩
    intro z _
    simpa only [Subsingleton.elim z 0] using h0
  · let : NeZero k := ⟨hk⟩
    obtain ⟨D⟩ := localBishopData_exists hf hf0 he
    exact bishopData_noncollapse D hΩ (discContinuityWithin_mono hCP heε) (half_pos hr)
      (hGV.continuousOn.mono fun q hq => (hrs (hproduct hq)).1) hgraphs

end Release061.Wiener

end

end OAI
