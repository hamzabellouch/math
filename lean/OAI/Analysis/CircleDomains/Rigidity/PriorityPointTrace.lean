import OAI.Analysis.CircleDomains.Selection.PriorityStability
import OAI.Analysis.CircleDomains.Selection.PriorityTermination

namespace OAI

/-! Continuity at a point end: early cutoffs are retained exactly, while
all later active scalar values approach the original point trace. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity

 def priorityTruncatedValues (c : ℕ → ℝ) (a : ℝ) (N : ℕ) (n : ℕ) : ℝ :=
  if n < N then c n else a

 theorem priorityTruncatedValues_bound {c : ℕ → ℝ} {B : ℝ} (hc : ∀ n, ‖c n‖ ≤ B)
    (a : ℝ) (N n : ℕ) : ‖priorityTruncatedValues c a N n‖ ≤ max B ‖a‖ := by
  by_cases hn : n < N
  · simp only [priorityTruncatedValues, ite_eq_left hn]
    exact (hc n).trans (le_max_left _ _)
  · simp only [priorityTruncatedValues, ite_eq_right hn]
    exact le_max_right _ _

 theorem priorityInfiniteValue_constant_tail {χ c : ℕ → ℝ}
    (hχ : ∀ n, χ n ∈ Icc (0 : ℝ) 1) {B : ℝ} (hc : ∀ n, ‖c n‖ ≤ B) (a : ℝ) (N : ℕ) :
    priorityInfiniteValue χ (priorityTruncatedValues c a N) a =
      a + ∑ n ∈ Finset.range N, priorityWeight χ n*(c n-a) := by
  let d := priorityTruncatedValues c a N
  have hds := priorityWeighted_summable hχ (priorityTruncatedValues_bound hc a N)
  have has := (priorityWeight_summable hχ).mul_right a
  have hdiff : (∑' n, priorityWeight χ n*(d n-a)) =
      (∑' n, priorityWeight χ n*d n)-(∑' n, priorityWeight χ n)*a := by
    simp_rw [mul_sub]
    rw [hds.tsum_sub has, (priorityWeight_summable hχ).tsum_mul_right]
  have hfinite : (∑' n, priorityWeight χ n*(d n-a)) =
      ∑ n ∈ Finset.range N, priorityWeight χ n*(c n-a) := by
    calc
      _ = ∑ n ∈ Finset.range N, priorityWeight χ n*(d n-a) := by
        apply tsum_eq_sum
        intro n hn
        simp only [d, priorityTruncatedValues, ite_eq_right (by simpa only [Finset.mem_range] using hn),
          sub_self, mul_zero]
      _ = _ := Finset.sum_congr rfl (fun n hn => by
        simp only [d, priorityTruncatedValues, ite_eq_left (Finset.mem_range.mp hn)])
  change (1-∑' n, priorityWeight χ n)*a+(∑' n, priorityWeight χ n*d n) = _
  rw [← hfinite, hdiff]
  ring

 theorem priorityInfiniteValue_continuousAt_point_trace
    {X : Type*} [TopologicalSpace X] {p : X}
    (χ : ℕ → X → ℝ) (c : ℕ → ℝ) (x : X → ℝ)
    (hχc : ∀ n, ContinuousAt (χ n) p)
    (hχ : ∀ q n, χ n q ∈ Icc (0 : ℝ) 1)
    {B : ℝ} (hc : ∀ n, ‖c n‖ ≤ B) (hx : ContinuousAt x p)
    (htail : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ᶠ q in 𝓝 p,
      ∀ n, N ≤ n → χ n q ≠ 0 → ‖c n-x p‖ ≤ ε) :
    ContinuousAt (fun q => priorityInfiniteValue (fun n => χ n q) c (x q)) p := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  let δ := ε/4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨N, hN⟩ := htail δ hδ
  let d := priorityTruncatedValues c (x p) N
  let Q := fun q => priorityInfiniteValue (fun n => χ n q) d (x p)
  have hQ : ContinuousAt Q p := by
    have hh : ContinuousAt (fun q => x p+
        ∑ n ∈ Finset.range N, priorityWeight (fun i => χ i q) n*(c n-x p)) p :=
      continuousAt_const.add (tendsto_finsetSum _ (fun n _ =>
        (priorityWeight_continuousAt hχc n).mul continuousAt_const))
    apply hh.congr_of_eventuallyEq
    exact Eventually.of_forall fun q => priorityInfiniteValue_constant_tail (hχ q) hc (x p) N
  have hnearX : ∀ᶠ q in 𝓝 p, ‖x q-x p‖ < δ := by
    simpa only [dist_eq_norm] using (Metric.tendsto_nhds.mp hx) δ hδ
  have hnearQ : ∀ᶠ q in 𝓝 p, dist (Q q) (Q p) < δ :=
    (Metric.tendsto_nhds.mp hQ) δ hδ
  have hcompare (q : X) (hq : ∀ n, N ≤ n → χ n q ≠ 0 → ‖c n-x p‖ ≤ δ)
      (hxq : ‖x q-x p‖ ≤ δ) :
      dist (priorityInfiniteValue (fun n => χ n q) c (x q)) (Q q) ≤ δ := by
    apply priorityInfiniteValue_stability (hχ q) hc (priorityTruncatedValues_bound hc (x p) N) hxq
    intro n
    by_cases hz : χ n q = 0
    · exact Or.inl hz
    · apply Or.inr
      by_cases hn : n < N
      · simp only [priorityTruncatedValues, ite_eq_left hn, sub_self, norm_zero]
        exact hδ.le
      · simpa only [d, priorityTruncatedValues, ite_eq_right hn] using hq n (Nat.le_of_not_gt hn) hz
  have hp : dist (priorityInfiniteValue (fun n => χ n p) c (x p)) (Q p) ≤ δ :=
    hcompare p (mem_of_mem_nhds hN) (by simpa only [sub_self, norm_zero] using hδ.le)
  filter_upwards [hN, hnearX, hnearQ] with q hq hxq hQq
  have hqq := hcompare q hq hxq.le
  calc
    _ ≤ dist (priorityInfiniteValue (fun n => χ n q) c (x q)) (Q q)+
        dist (Q q) (Q p)+dist (Q p) (priorityInfiniteValue (fun n => χ n p) c (x p)) :=
      dist_triangle4 _ _ _ _
    _ < ε := by rw [dist_comm (Q p)] ; dsimp [δ] at hqq hQq hp; linarith

end CircleDomainRigidity

end

end OAI
