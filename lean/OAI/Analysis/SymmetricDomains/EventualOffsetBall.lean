import Mathlib
import OAI.Analysis.SymmetricDomains.BoundaryInjective

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
namespace Release061
open Set Filter Metric
open scoped Topology

def offsetScaled {S E : Type*} [SMul ℝ E] (A : S → Set E) (s : S) (t : ℝ) : Set E :=
  {v | t • v ∈ A s}

def offsetDistance {S E : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) (v : E) : ℝ :=
  min 1 (infDist v (offsetScaled A s t)ᶜ)

lemma offsetDistance_nonneg {S E : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) (v : E) : 0 ≤ offsetDistance A s t v :=
  le_min zero_le_one infDist_nonneg

lemma offsetDistance_le_one {S E : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) (v : E) : offsetDistance A s t v ≤ 1 := min_le_left _ _

lemma offsetDistance_lipschitz {S E : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) : LipschitzWith 1 (offsetDistance A s t) := by
  unfold offsetDistance
  convert (LipschitzWith.const (α := E) (1 : ℝ)).min
    (lipschitz_infDist_pt (offsetScaled A s t)ᶜ) using 1; norm_num

lemma offset_excluded_nonempty {S E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) (h0 : (0 : E) ∉ A s) :
    (offsetScaled A s t)ᶜ.Nonempty := ⟨0,by simpa [offsetScaled] using h0⟩

lemma offsetDistance_zero {S E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : S → Set E) (s : S) (t : ℝ) (h0 : (0 : E) ∉ A s) : offsetDistance A s t 0 = 0 := by
  rw [offsetDistance,infDist_zero_of_mem (show (0 : E) ∈ (offsetScaled A s t)ᶜ by
    simpa [offsetScaled] using h0)]
  norm_num

lemma ball_subset_offsetScaled {S E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : S → Set E} {s : S} {t c : ℝ} {v : E} (ht : 0 < t)
    (hball : ball v (c*t) ⊆ A s) : ball (t⁻¹ • v) c ⊆ offsetScaled A s t := by
  intro x hx
  change t • x ∈ A s
  apply hball
  have he : dist (t • x) v = t * dist x (t⁻¹ • v) := by
    nth_rw 1 [← smul_inv_smul₀ ht.ne' v]
    rw [dist_smul₀,Real.norm_eq_abs,abs_of_pos ht]
  rw [mem_ball,he,mul_comm c t]
  exact mul_lt_mul_of_pos_left hx ht

lemma radius_le_infDist_compl {E : Type*} [PseudoMetricSpace E]
    {A : Set E} {v : E} {c : ℝ} (hne : Aᶜ.Nonempty) (hball : ball v c ⊆ A) :
    c ≤ infDist v Aᶜ := by
  apply (le_infDist hne).mpr
  intro y hy
  by_contra h
  exact hy (hball (by simpa only [mem_ball,dist_comm] using lt_of_not_ge h))

theorem excluded_offset_noncollapse {S E : Type*} [TopologicalSpace S]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (A : S → Set E) (F : Set E) {s₀ : S} {s : ℕ → S} {t : ℕ → ℝ} {v : ℕ → E}
    (hs : Tendsto s atTop (𝓝 s₀)) (ht : Tendsto t atTop (𝓝 0))
    (htpos : ∀ j, 0 < t j) (h0 : ∀ j, (0 : E) ∉ A (s j))
    {c C : ℝ} (hc : 0 < c) (hbound : ∀ j, ‖v j‖ ≤ C*t j)
    (hball : ∀ j, ball (v j) (c*t j) ⊆ A (s j))
    (hexcluded : ∀ (s' : ℕ → S) (t' : ℕ → ℝ) (v' : ℕ → E) (w : E),
      Tendsto s' atTop (𝓝 s₀) → Tendsto t' atTop (𝓝 0) →
      (∀ j, 0 < t' j) → Tendsto v' atTop (𝓝 w) → w ∈ F →
      Tendsto (fun j => infDist (v' j) (offsetScaled A (s' j) (t' j))ᶜ) atTop (𝓝 0)) :
    F ≠ univ := by
  let w : ℕ → E := fun j => (t j)⁻¹ • v j
  have hw (j : ℕ) : w j ∈ closedBall (0 : E) C := by
    rw [mem_closedBall,dist_zero_right]
    dsimp [w]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr (htpos j))]
    calc (t j)⁻¹ * ‖v j‖ ≤ (t j)⁻¹*(C*t j) :=
          mul_le_mul_of_nonneg_left (hbound j) (inv_nonneg.mpr (htpos j).le)
      _ = C := by field_simp [(htpos j).ne']
  obtain ⟨a,_,φ,hφ,hwa⟩ := (isCompact_closedBall (0 : E) C).tendsto_subseq hw
  intro hF
  have hlim := hexcluded (s ∘ φ) (t ∘ φ) (w ∘ φ) a (hs.comp hφ.tendsto_atTop)
    (ht.comp hφ.tendsto_atTop) (fun j => htpos (φ j)) hwa (by rw [hF]; trivial)
  have hb : ∀ j, c ≤ infDist (w (φ j)) (offsetScaled A (s (φ j)) (t (φ j)))ᶜ := by
    intro j
    exact radius_le_infDist_compl (offset_excluded_nonempty A _ _ (h0 (φ j)))
      (ball_subset_offsetScaled (htpos (φ j)) (hball (φ j)))
  have hc0 : c ≤ (0 : ℝ) := ge_of_tendsto hlim (Eventually.of_forall hb)
  exact not_le_of_gt hc hc0

lemma complex_ball_offset_ball {k : ℕ} {Ω : Set (Fin k → ℂ)} {a : Fin k → ℂ}
    {r : ℝ} (φ : (Fin k → ℝ) → Fin k → ℝ)
    (hball : ball a r ⊆ Ω) :
    ball ((fun i => (a i).im) - φ (fun i => (a i).re)) r ⊆
      {v : Fin k → ℝ | (fun i => ((a i).re : ℂ)+Complex.I*((φ (fun i => (a i).re) i+v i) : ℂ)) ∈ Ω} := by
  intro v hv
  apply hball
  rw [mem_ball,dist_eq_norm] at hv ⊢
  have he : (fun i => ((a i).re : ℂ)+Complex.I*((φ (fun i => (a i).re) i+v i) : ℂ)) - a =
      fun i => Complex.I*((v-((fun i => (a i).im)-φ (fun i => (a i).re))) i : ℂ) := by
    funext i
    apply Complex.ext <;> simp; ring
  rw [he]
  simpa only [Pi.norm_def,nnnorm_mul,Complex.nnnorm_I,Complex.nnnorm_real,one_mul] using hv

lemma tendsto_of_truncated_zero {I : Type*} {l : Filter I} {f : I → ℝ}
    (h : Tendsto (fun i => min 1 (f i)) l (𝓝 0)) : Tendsto f l (𝓝 0) := by
  have he : ∀ᶠ i in l, f i < 1 := by
    filter_upwards [(tendsto_order.mp h).2 1 zero_lt_one] with i hi
    rcases min_lt_iff.mp hi with hi | hi
    · exact (lt_irrefl _ hi).elim
    · exact hi
  exact h.congr' (he.mono fun i hi => min_eq_right hi.le)

lemma moving_offsetDistance_limit {S E I : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : I → S) (t : I → ℝ) {l : Filter I} {v : I → E} {w : E} {a : ℝ}
    (h : Tendsto (fun j => offsetDistance A (s j) (t j) w) l (𝓝 a))
    (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun j => offsetDistance A (s j) (t j) (v j)) l (𝓝 a) := by
  apply h.congr_dist
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun j => by simpa only [NNReal.coe_one,one_mul] using
      (offsetDistance_lipschitz A (s j) (t j)).dist_le_mul w (v j))
  simpa only [dist_self] using (tendsto_const_nhds (x := w) (f := l)).dist hv

lemma excluded_limit_from_offsetDistance {S E I : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : I → S) (t : I → ℝ) {l : Filter I} {v : I → E} {w : E}
    (h : Tendsto (fun j => offsetDistance A (s j) (t j) w) l (𝓝 0))
    (hv : Tendsto v l (𝓝 w)) :
    Tendsto (fun j => infDist (v j) (offsetScaled A (s j) (t j))ᶜ) l (𝓝 0) :=
  tendsto_of_truncated_zero (moving_offsetDistance_limit A s t h hv)

lemma eventual_offset_ball {S E I : Type*} [MetricSpace E] [SMul ℝ E]
    (A : S → Set E) (s : I → S) (t : I → ℝ) {l : Filter I} {w : E} {a : ℝ}
    (ha : 0 < a) (h : Tendsto (fun j => offsetDistance A (s j) (t j) w) l (𝓝 a)) :
    ∀ᶠ j in l, ball w (a/2) ⊆ offsetScaled A (s j) (t j) := by
  filter_upwards [(tendsto_order.mp h).1 (a/2) (by linarith)] with j hj
  exact (ball_subset_ball ((lt_of_lt_of_le hj (min_le_right _ _)).le)).trans
    ball_infDist_compl_subset

end Release061

end

end OAI
