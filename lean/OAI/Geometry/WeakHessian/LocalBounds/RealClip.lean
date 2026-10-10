import Mathlib

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile0
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

noncomputable section
open Set Filter Topology Bornology
open scoped InnerProductSpace

attribute [local instance] Classical.propDecidable
open Set
open scoped NNReal
open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

namespace WeakHessianFunctional
open Set Filter MeasureTheory
open scoped Topology ENNReal

variable {X : Type*} [MeasurableSpace X] {m : Measure X}

def realClip (n : ℕ) (r : ℝ) : ℝ := max (-(n:ℝ)) (min r n)
lemma realClip_lipschitz (n : ℕ) : LipschitzWith 1 (realClip n) :=
  (LipschitzWith.id.min_const (n:ℝ)).const_max (-(n:ℝ))
lemma realClip_zero (n : ℕ) : realClip n 0 = 0 := by simp [realClip]
lemma realClip_abs_le (n : ℕ) (r : ℝ) : |realClip n r| ≤ (n:ℝ) := by
  exact abs_le.mpr ⟨le_max_left _ _,max_le (by linarith [Nat.cast_nonneg (α := ℝ) n]) (min_le_right _ _)⟩
lemma realClip_norm_le (n : ℕ) (r : ℝ) : ‖realClip n r‖ ≤ ‖r‖ := by
  simpa only [realClip_zero, sub_zero, NNReal.coe_one, one_mul] using
    (realClip_lipschitz n).norm_sub_le r 0
lemma realClip_tendsto (r : ℝ) : Tendsto (fun n => realClip n r) atTop (𝓝 r) := by
  have he : ∀ᶠ n : ℕ in atTop, |r| ≤ (n:ℝ) :=
    (tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop |r|))
  apply tendsto_const_nhds.congr'
  filter_upwards [he] with n hn
  simp only [realClip, min_eq_left (abs_le.mp hn).2, max_eq_right (abs_le.mp hn).1]

lemma realClip_tendsto_Lp (f : Lp ℝ 2 m) :
    Tendsto (fun n => (realClip_lipschitz n).compLp (realClip_zero n) f) atTop (𝓝 f) := by
  let g : ℕ → X → ℝ := fun n x => realClip n (f x)
  have hg (n : ℕ) : MemLp (g n) 2 m :=
    (realClip_lipschitz n).comp_memLp (realClip_zero n) (Lp.memLp f)
  have hi : UnifIntegrable g 2 m := by
    rw [unifIntegrable_iff']
    intro ε hε
    obtain ⟨δ,hδ,hδf⟩ := (Lp.memLp f).eLpNorm_indicator_le (by norm_num) (by norm_num) hε
    refine ⟨δ,hδ,fun n s hs hms => ?_⟩
    rw [← eLpNorm_indicator_eq_eLpNorm_restrict hs]
    apply le_trans (eLpNorm_mono ((hg n).aestronglyMeasurable.indicator hs) (fun x => ?_)) (hδf s hs hms)
    by_cases hx : x ∈ s
    · simpa only [indicator_of_mem hx,g] using realClip_norm_le n (f x)
    · simp only [indicator_of_notMem hx,le_refl]
  have ht : UnifTight g 2 m := by
    intro ε hε
    obtain ⟨s,hs,hms,hfs⟩ := (Lp.memLp f).exists_eLpNorm_indicator_compl_lt (by norm_num) hε.ne'
    refine ⟨s,hms.ne,fun n => ?_⟩
    apply le_trans (eLpNorm_mono ((hg n).aestronglyMeasurable.indicator hs.compl) (fun x => ?_)) hfs.le
    by_cases hx : x ∈ sᶜ
    · simpa only [indicator_of_mem hx,g] using realClip_norm_le n (f x)
    · simp only [indicator_of_notMem hx,le_refl]
  have hconv := tendsto_Lp_of_tendsto_ae (by norm_num : (1:ℝ≥0∞) ≤ 2)
    (by norm_num : (2:ℝ≥0∞) ≠ ∞) (fun n => (hg n).aestronglyMeasurable) (Lp.memLp f) hi ht
      (Eventually.of_forall fun x => realClip_tendsto (f x))
  rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm']
  convert hconv using 1
  ext n
  apply eLpNorm_congr_ae
  filter_upwards [(realClip_lipschitz n).coeFn_compLp (realClip_zero n) f] with x hx
  exact congrArg (fun z => z-f x) hx

end WeakHessianFunctional

end
end InlinedFile0

end OAI
