import Mathlib

namespace OAI

noncomputable section

namespace Problem336.ContinuousPathLimit

open Filter MeasureTheory
open scoped Topology

variable {T Ω : Type*} [TopologicalSpace T] [CompactSpace T]

def pathLimit (F : ℕ → C(T, ℝ)) : C(T, ℝ) := by
  classical
  exact if ∃ f, Tendsto F atTop (𝓝 f) then limUnder atTop F else 0

omit [CompactSpace T] in

theorem pathLimit_eq_of_tendsto {F : ℕ → C(T, ℝ)} {f : C(T, ℝ)}
    (h : Tendsto F atTop (𝓝 f)) : pathLimit F = f := by
  rw [pathLimit, ite_eq_left ⟨f, h⟩]
  exact h.limUnder_eq

theorem tendsto_pathLimit_of_summable {F : ℕ → C(T, ℝ)} (d : ℕ → ℝ)
    (hF : ∀ n, dist (F n) (F (n + 1)) ≤ d n) (hd : Summable d) :
    Tendsto F atTop (𝓝 (pathLimit F)) := by
  obtain ⟨f, hf⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_dist_le_of_summable d hF hd)
  rwa [pathLimit_eq_of_tendsto hf]

theorem tendsto_pathLimit_of_eventually_summable {F : ℕ → C(T, ℝ)} (d : ℕ → ℝ)
    (hF : ∀ᶠ n in atTop, dist (F n) (F (n + 1)) ≤ d n) (hd : Summable d) :
    Tendsto F atTop (𝓝 (pathLimit F)) := by
  let d' n := max (dist (F n) (F (n + 1))) (d n)
  have heq : d =ᶠ[cofinite] d' := by
    rw [Nat.cofinite_eq_atTop]
    exact hF.mono (fun n hn => (max_eq_right hn).symm)
  exact tendsto_pathLimit_of_summable d' (fun n => le_max_left _ _)
    (hd.congr_cofinite heq)

theorem dist_pathLimit_le_tsum {F : ℕ → C(T, ℝ)} (d : ℕ → ℝ)
    (hF : ∀ n, dist (F n) (F (n + 1)) ≤ d n) (hd : Summable d) (n : ℕ) :
    dist (F n) (pathLimit F) ≤ ∑' m, d (n + m) :=
  dist_le_tsum_of_dist_le_of_tendsto d hF hd
    (tendsto_pathLimit_of_summable d hF hd) n

theorem tendsto_eval_pathLimit {F : ℕ → C(T, ℝ)} (d : ℕ → ℝ)
    (hF : ∀ n, dist (F n) (F (n + 1)) ≤ d n) (hd : Summable d) (t : T) :
    Tendsto (fun n => F n t) atTop (𝓝 (pathLimit F t)) :=
  (continuous_eval_const t).continuousAt.tendsto.comp
    (tendsto_pathLimit_of_summable d hF hd)

theorem pathLimit_eval_eq_of_eventually {F : ℕ → C(T, ℝ)} (d : ℕ → ℝ)
    (hF : ∀ n, dist (F n) (F (n + 1)) ≤ d n) (hd : Summable d)
    (t : T) (a : ℝ) (ha : ∀ᶠ n in atTop, F n t = a) : pathLimit F t = a :=
  tendsto_nhds_unique (tendsto_eval_pathLimit d hF hd t)
    (tendsto_const_nhds.congr' (ha.mono (fun _ hn => hn.symm)))

section Measurability

variable [MeasurableSpace Ω]

theorem stronglyMeasurable_pathLimit (F : ℕ → Ω → C(T, ℝ))
    (hF : ∀ n, StronglyMeasurable (F n)) :
    StronglyMeasurable (fun ω => pathLimit (fun n => F n ω)) := by
  classical
  have hc : MeasurableSet {ω | ∃ f, Tendsto (fun n => F n ω) atTop (𝓝 f)} :=
    StronglyMeasurable.measurableSet_exists_tendsto (l := atTop) hF
  unfold pathLimit
  exact StronglyMeasurable.ite hc
    (StronglyMeasurable.limUnder (l := atTop) hF) stronglyMeasurable_const

variable [MeasurableSpace C(T, ℝ)] [BorelSpace C(T, ℝ)]

theorem measurable_pathLimit [SecondCountableTopology C(T, ℝ)]
    (F : ℕ → Ω → C(T, ℝ)) (hF : ∀ n, Measurable (F n)) :
    Measurable (fun ω => pathLimit (fun n => F n ω)) :=
  (stronglyMeasurable_pathLimit F (fun n => (hF n).stronglyMeasurable)).measurable

end Measurability

open ProbabilityTheory

variable [MeasurableSpace Ω] {P : Measure Ω}

theorem ae_tendsto_pathLimit_of_eventually_summable
    (F : ℕ → Ω → C(T, ℝ)) (d : ℕ → ℝ) (hd : Summable d)
    (hF : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, dist (F n ω) (F (n + 1) ω) ≤ d n) :
    ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop
      (𝓝 (pathLimit (fun n => F n ω))) := by
  filter_upwards [hF] with ω hω
  exact tendsto_pathLimit_of_eventually_summable d hω hd

omit [CompactSpace T] in

theorem hasLaw_eval_pathLimit {ι : Type*} (times : ι → T)
    (F : ℕ → Ω → C(T, ℝ)) (a : Ω → ι → ℝ) (μ : Measure (ι → ℝ))
    (hconv : ∀ᵐ ω ∂P, ∃ f, Tendsto (fun n => F n ω) atTop (𝓝 f))
    (hstab : ∀ᵐ ω ∂P, ∀ i, ∀ᶠ n in atTop, F n ω (times i) = a ω i)
    (ha : HasLaw a μ P) :
    HasLaw (fun ω i => pathLimit (fun n => F n ω) (times i)) μ P := by
  apply ha.congr
  filter_upwards [hconv, hstab] with ω hω hs
  obtain ⟨f, hf⟩ := hω
  funext i
  rw [pathLimit_eq_of_tendsto hf]
  exact tendsto_nhds_unique
    ((continuous_eval_const (times i)).continuousAt.tendsto.comp hf)
    (tendsto_const_nhds.congr' ((hs i).mono (fun _ hn => hn.symm)))

end Problem336.ContinuousPathLimit

end

end OAI
