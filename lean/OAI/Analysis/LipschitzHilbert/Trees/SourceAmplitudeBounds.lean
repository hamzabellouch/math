import OAI.Analysis.LipschitzHilbert.Trees.SourceAmplitudeExhaustion

namespace OAI

/-! On each fixed exhaustion the original source amplitude is bounded
for every complex phase. Nonnegative real phases give the sharper
phase-independent bound needed on the simplex tube. -/

noncomputable section
open MeasureTheory Set
open scoped BigOperators
namespace LipschitzHilbert.AngularGrid
variable {τ σ X κ : Type*} [Fintype κ]

theorem sourcePacketAmplitude_norm_on_exhaustion (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ) (K : ℕ) (gap : ℕ → ℝ)
    (packets : Finset σ) (assigned : σ → τ) (stop : σ → ℕ)
    (value : X → σ → EuclideanSpace ℂ κ) (a : ℝ) (level : ℕ) (cell : ℤ)
    (phase : ℕ → ℂ) (n : ℕ) (x : X)
    (hx : x ∈ sourceExhaustion (g.sourceAmplitudeRadius tops slope precision cutoff weight K gap
      packets assigned stop value a level cell) n) :
    ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
      (value x) phase a x level cell‖ ≤
      ∑ s ∈ g.packetSet packets (fun s => slope (assigned s)) stop level cell,
        Real.exp ((∑ j ∈ Finset.Ico level (stop s), ‖phase j‖)*(n:ℝ))*(n:ℝ) := by
  have heq := g.sourcePacketAmplitude_affine_exp tops slope precision cutoff weight K gap packets
    assigned stop (value x) phase (fun _ => 0) a x level cell (0:ℂ)
  simp only [zero_mul,add_zero] at heq
  rw [heq]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  rw [norm_smul]
  have hbase : ‖g.sourcePacketBase tops slope precision cutoff weight assigned stop (value x) a x s‖ ≤ (n:ℝ) :=
    (g.sourceAmplitudeRadius_base_le tops slope precision cutoff weight K gap packets assigned stop
      value a level cell s hs x).trans hx
  have hlog : ‖g.sourcePathLog tops slope precision cutoff weight K gap phase level (stop s)
      (slope (assigned s)) x‖ ≤ (∑ j ∈ Finset.Ico level (stop s), ‖phase j‖)*(n:ℝ) := by
    apply (g.pathLogCombination_norm_le _ _ phase level (stop s) (slope (assigned s))).trans
    exact mul_le_mul_of_nonneg_left
      ((g.sourceAmplitudeRadius_log_le tops slope precision cutoff weight K gap packets assigned stop
        value a level cell s hs x).trans hx) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  have hexp : ‖Complex.exp (g.sourcePathLog tops slope precision cutoff weight K gap phase level
      (stop s) (slope (assigned s)) x)‖ ≤
      Real.exp ((∑ j ∈ Finset.Ico level (stop s), ‖phase j‖)*(n:ℝ)) := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans hlog)
  exact mul_le_mul hexp hbase (norm_nonneg _) (Real.exp_pos _).le

theorem sourcePacketAmplitude_norm_le_radius (g : AngularGrid) (tops : Finset τ)
    (slope precision : τ → ℝ) (cutoff : ℝ) (weight : τ → X → ℝ)
    (hp : ∀ t ∈ tops, 0 ≤ precision t) (hw : ∀ t x, 0 < weight t x)
    {K : ℕ} (hK : 0 < K) (gap : ℕ → ℝ) (packets : Finset σ) (assigned : σ → τ)
    (stop : σ → ℕ) (value : X → σ → EuclideanSpace ℂ κ) (a : ℝ) (level : ℕ) (cell : ℤ)
    (hassigned : ∀ s ∈ packets, assigned s ∈ tops)
    (heligible : ∀ s ∈ packets, g.eligible cutoff (precision (assigned s)) (stop s))
    (phase : ℕ → ℂ) (hphase : ∀ j, 0 ≤ (phase j).re) (x : X) :
    ‖g.sourcePacketAmplitude tops slope precision cutoff weight K gap packets assigned stop
      (value x) phase a x level cell‖ ≤
      g.sourceAmplitudeRadius tops slope precision cutoff weight K gap packets assigned stop value a level cell x := by
  unfold sourcePacketAmplitude packetAmplitude sourceAmplitudeRadius
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro s hs
  have hsp : s ∈ packets := (Finset.mem_filter.mp hs).1
  have ht := hassigned s hsp
  have hprod : ‖g.packetPathProduct (g.sourceTransition tops slope precision cutoff weight K gap phase x)
      level (stop s) (slope (assigned s))‖ ≤ 1 := by
    rw [packetPathProduct,norm_prod]
    apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
    intro j hj
    have hjstop : j+1 ≤ stop s := by have := (Finset.mem_Ico.mp hj).2; omega
    exact g.sourceTransition_norm_le_one tops slope precision cutoff weight hp hw hK gap phase x j
      (assigned s) ht (g.eligible_of_le (hp _ ht) hjstop (heligible s hsp)) (hphase j)
  rw [norm_smul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hprod).trans
    (le_add_of_nonneg_right (g.pathLogSize_nonneg _ _ _ _ _))

end LipschitzHilbert.AngularGrid

end

end OAI
