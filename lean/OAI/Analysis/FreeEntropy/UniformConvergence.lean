import OAI.Analysis.FreeEntropy.MicrostatesHeat

namespace OAI

universe u1 u2

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace FiniteEntropySeparation
 theorem uniform_of_all_selections {α : ℕ → Type u1} (S : (k:ℕ) → Set (α k)) (hS : ∀k,(S k).Nonempty)
    (F : (k:ℕ) → α k → ℝ) (hF : ∀a:(k:ℕ) → α k,(∀k,a k ∈ S k) → Tendsto (fun k => F k (a k)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0<ε) : ∀ᶠ k in atTop,∀a ∈ S k,|F k a|<ε := by
  classical
  choose a ha using hS
  let b (k : ℕ) : α k := if h : ∃x ∈ S k,ε≤|F k x| then h.choose else a k
  have hb (k : ℕ) : b k ∈ S k := by
    dsimp only [b]
    split_ifs with h
    · exact h.choose_spec.1
    · exact ha k
  have ht := (hF b hb).abs.eventually (gt_mem_nhds (by simpa using hε))
  filter_upwards [ht] with k hk x hx
  by_contra he
  have h : ∃x ∈ S k,ε≤|F k x| := ⟨x,hx,le_of_not_gt he⟩
  have hh : ε≤|F k (b k)| := by simpa only [b,dite_eq_left h] using h.choose_spec.2
  exact (not_lt_of_ge hh) hk
 theorem integral_tendsto_zero_of_uniform {α : ℕ → Type u2} [∀k,MeasurableSpace (α k)]
    (μ : (k:ℕ) → Measure (α k)) [∀k,IsProbabilityMeasure (μ k)]
    (S : (k:ℕ) → Set (α k)) (hS : ∀k,∀ᵐ a ∂μ k,a ∈ S k)
    (F : (k:ℕ) → α k → ℝ) (hm : ∀k,AEStronglyMeasurable (F k) (μ k))
    (hu : ∀ε:ℝ,0<ε → ∀ᶠ k in atTop,∀a ∈ S k,|F k a|<ε) :
    Tendsto (fun k => ∫ a,F k a ∂μ k) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hu (ε/2) (by positivity)] with k hk
  have hb : ∀ᵐ a ∂μ k,‖F k a‖≤ε/2 := by
    filter_upwards [hS k] with a ha
    exact (hk a ha).le
  have hi : Integrable (F k) (μ k) := (integrable_const (ε/2)).mono' (hm k) hb
  have hn : ‖∫ a,F k a ∂μ k‖≤ε/2 := by
    apply (norm_integral_le_integral_norm _).trans
    exact (integral_mono_ae hi.norm (integrable_const _) hb).trans_eq (by simp)
  simpa only [dist_zero_right] using hn.trans_lt (by linarith : ε/2<ε)
end FiniteEntropySeparation

end

end OAI
