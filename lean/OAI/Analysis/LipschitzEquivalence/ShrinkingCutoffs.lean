import OAI.Analysis.LipschitzEquivalence.LocalLipschitz

namespace OAI

universe uM

noncomputable section
open scoped BigOperators InnerProductSpace Topology ENNReal
open scoped Topology ENNReal NNReal
open scoped Classical ENNReal NNReal InnerProductSpace Topology
open Filter Set
open scoped NNReal Topology
open Filter Set

namespace LipschitzCounterexample.LocalizedLinearization
open Filter Set Topology
open scoped NNReal ENNReal
variable {M : Type uM} [MetricSpace M] [Zero M]

theorem shrinking_radius_uniform (z : M) {μ : ℕ → FreeSpace.Space M}
    (hw : WeakSequences.WeakNull μ) (f : ℕ → ℝ≥0 → M → ℝ) {C : ℝ≥0}
    (hf : ∀ i (r : ℝ≥0), 0 < r → LipschitzWith C (f i r))
    (hfz : ∀ i (r : ℝ≥0), 0 < r → f i r z = 0)
    (hfs : ∀ i (r : ℝ≥0), 0 < r → ∀ x, (r : ℝ) ≤ dist x z → f i r x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ≥0, ∀ hr : 0 < r, (r : ℝ) < δ →
      ∀ᶠ i in atTop, |test (normalized (f i r) (hf i r hr)) (μ i)| < ε := by
  classical
  by_contra hn
  push Not at hn
  have hchoice (n : ℕ) := hn (1 / ((n : ℝ)+1)) (by positivity)
  choose r hr hrad hnot using hchoice
  have hbad (n k : ℕ) : ∃ i > k,
      ε ≤ |test (normalized (f i (r n)) (hf i (r n) (hr n))) (μ i)| := by
    have hh : ∃ᶠ i in atTop,
        ε ≤ |test (normalized (f i (r n)) (hf i (r n) (hr n))) (μ i)| := by
      simpa only [not_lt] using hnot n
    exact Filter.frequently_atTop'.mp hh k
  let next (n p : ℕ) : ℕ := Classical.choose (hbad n p)
  let seq : ℕ → ℕ := fun n => Nat.rec 0 (fun n p => next n p) n
  have hseq (n : ℕ) : seq n < seq (n+1) ∧
      ε ≤ |test (normalized (f (seq (n+1)) (r n)) (hf _ _ (hr n))) (μ (seq (n+1)))| :=
    Classical.choose_spec (hbad n (seq n))
  have hmono : StrictMono seq := strictMono_nat_of_lt_succ (fun n => (hseq n).1)
  let a : ℕ → ℕ := fun n => seq (n+1)
  have ha : StrictMono a := fun _ _ hn => hmono (Nat.add_lt_add_right hn 1)
  have hrlim : Tendsto (fun n => (r n : ℝ)) atTop (𝓝 0) :=
    squeeze_zero (fun n => (r n).coe_nonneg) (fun n => (hrad n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim := shrinking_tests z (hw.subseq ha) r hr hrlim
    (fun n => f (a n) (r n)) (fun n => hf _ _ (hr n))
    (fun n => hfz _ _ (hr n)) (fun n x hx => hfs _ _ (hr n) x hx)
  have habs := hlim.abs
  simp only [abs_zero] at habs
  have hevent := habs.eventually (eventually_lt_nhds hε)
  obtain ⟨n,hn⟩ := hevent.exists
  exact (not_lt_of_ge (hseq n).2) hn

theorem cutoff_pairings_small (z : M) {μ : ℕ → FreeSpace.Space M}
    (hw : WeakSequences.WeakNull μ) (d : ℕ → M → ℝ) {L : ℝ≥0}
    (hd : ∀ i, LipschitzWith L (d i)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ≥0, ∀ hr : 0 < r, (r : ℝ) < δ →
      ∀ᶠ i in atTop,
        |test (normalized (fun x => (d i x-d i z)*cutoff z r x)
          (cutoff_product_lipschitz z hr (fun x => d i x-d i z)
            (lipschitz_sub_const (d i) (hd i) (d i z)) (sub_self _))) (μ i)| < ε := by
  refine shrinking_radius_uniform z hw (fun i r x => (d i x-d i z)*cutoff z r x)
    (fun i r hr => cutoff_product_lipschitz z hr _
      (lipschitz_sub_const _ (hd i) _) (sub_self _)) ?_ ?_ hε
  · intro i r hr
    simp
  · intro i r hr x hx
    rw [cutoff_zero z hr hx,mul_zero]

end LipschitzCounterexample.LocalizedLinearization

end

end OAI
