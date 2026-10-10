import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.InterpolationUniform
import OAI.Probability.CriticalPercolation.Criticality.ExhaustionEvents
import OAI.Probability.CriticalPercolation.Criticality.RestrictedInterpolation

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open scoped Classical Topology

namespace CriticalPercolation

lemma exists_le_of_eventually_exists_le {I : Type*} [Finite I]
    {f : I → ℕ → ℝ} {a : I → ℝ} {r : ℕ → ℝ} {b : ℝ}
    (hf : ∀ i, Tendsto (f i) atTop (𝓝 (a i))) (hr : Tendsto r atTop (𝓝 b))
    (h : ∀ᶠ n in atTop, ∃ i, r n ≤ f i n) : ∃ i, b ≤ a i := by
  by_contra! hh
  have ht : ∀ᶠ n in atTop, ∀ i, f i n < r n :=
    Filter.eventually_all.mpr (fun i => (hf i).eventually_lt hr (hh i))
  obtain ⟨n,hn,hn'⟩ := (h.and ht).exists
  obtain ⟨i,hi⟩ := hn
  exact (not_le.mpr (hn' i)) hi

namespace BondGraph
variable {V E : Type*} [Countable E] (G : BondGraph V E)

theorem infinite_interpolation_measure
    (d : ℕ) (x : ℕ → V) (hd : 2≤d) (p : unitInterval)
    (hp : (p : ℝ) ∈ Set.Ioo 0 1) {c ε : ℝ} (hc : 0<c) (hε : 0<ε)
    (hεp : ε≤p) (hεq : ε≤1-(p:ℝ))
    (hconn : ∀ j k, j<k → k≤d → k-j<d →
      c ≤ (G.law p).real {ω | (G.openGraph ω).Reachable (x j) (x k)})
    (s : ℕ) (hδ : 0 < (G.law p).real (G.twoClusterEvent (x 0) (x d) s)) :
    ∃ j<d, 0 < (G.law p).real (G.twoClusterEvent (x j) (x (j+1)) s) ∧
      -Real.log ((G.law p).real (G.twoClusterEvent (x j) (x (j+1)) s)) ≤
        interpolationConstant (c/2) ε *
          (Real.log (1/(G.law p).real (G.twoClusterEvent (x 0) (x d) s))+Nat.clog 2 d+1) := by
  let K := (Set.to_countable (Set.univ : Set E)).finiteExhaustion
  let δ (n : ℕ) := (G.law p).real {ω | K n ∩ ω ∈ G.twoClusterEvent (x 0) (x d) s}
  let δlim := (G.law p).real (G.twoClusterEvent (x 0) (x d) s)
  have hδt : Tendsto δ atTop (𝓝 δlim) := G.tendsto_real_twoCluster_restrict p _ _ _ K
  have hδpos : ∀ᶠ n in atTop, 0 < δ n := hδt.eventually (eventually_gt_nhds hδ)
  have hcc : c/2 < c := by linarith
  have hce : ∀ᶠ n in atTop, ∀ j k : Fin (d+1), j.val<k.val → k.val-j.val<d →
      c/2 ≤ (G.law p).real {ω | (G.openGraph (K n ∩ ω)).Reachable (x j.val) (x k.val)} := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro k
    by_cases hjk : j.val<k.val ∧ k.val-j.val<d
    · have hl := lt_of_lt_of_le hcc (hconn j k hjk.1 (by omega) hjk.2)
      filter_upwards [(G.tendsto_real_reachable_restrict p (x j) (x k) K).eventually (eventually_gt_nhds hl)]
        with n hn
      exact fun _ _ => hn.le
    · exact Filter.Eventually.of_forall (fun _ _ _ => (hjk ⟨by assumption,by assumption⟩).elim)
  let C := interpolationConstant (c/2) ε
  let r (n : ℕ) := Real.exp (-C*(Real.log (1/δ n)+Nat.clog 2 d+1))
  let b := Real.exp (-C*(Real.log (1/δlim)+Nat.clog 2 d+1))
  have hr : Tendsto r atTop (𝓝 b) := by
    have h1 : Tendsto (fun n => 1/δ n) atTop (𝓝 (1/δlim)) := tendsto_const_nhds.div hδt (ne_of_gt hδ)
    have h2 := h1.log (one_div_ne_zero (ne_of_gt hδ))
    have hh : Tendsto (fun n => -C*(Real.log (1/δ n)+Nat.clog 2 d+1)) atTop
        (𝓝 (-C*(Real.log (1/δlim)+Nat.clog 2 d+1))) :=
      tendsto_const_nhds.mul ((h2.add_const _).add_const _)
    exact (Real.continuous_exp.tendsto _).comp hh
  have he : ∀ᶠ n in atTop, ∃ j : Fin d,
      r n ≤ (G.law p).real {ω | K n ∩ ω ∈ G.twoClusterEvent (x j.val) (x (j.val+1)) s} := by
    filter_upwards [hδpos,hce] with n hnδ hnc
    obtain ⟨j,hjd,hjp,hjl⟩ := G.restricted_interpolation_measure (K n) (K.finite n) d x hd p hp
      (by linarith : 0<c/2) hε hεp hεq (fun j k hjk hkd hdiff =>
        hnc ⟨j,by omega⟩ ⟨k,by omega⟩ hjk hdiff) s hnδ
    refine ⟨⟨j,hjd⟩,?_⟩
    apply (Real.le_log_iff_exp_le hjp).mp
    change -Real.log _ ≤ C * (Real.log (1/δ n)+Nat.clog 2 d+1) at hjl
    linarith
  obtain ⟨j,hj⟩ := exists_le_of_eventually_exists_le
    (fun j : Fin d => G.tendsto_real_twoCluster_restrict p (x j) (x (j.val+1)) s K) hr he
  have hjp := lt_of_lt_of_le (Real.exp_pos _) hj
  refine ⟨j,j.isLt,hjp,?_⟩
  have hl := (Real.le_log_iff_exp_le hjp).mpr hj
  change -C*(Real.log (1/δlim)+Nat.clog 2 d+1) ≤ _ at hl
  change -Real.log _ ≤ C * (Real.log (1/δlim)+Nat.clog 2 d+1)
  linarith

end BondGraph
end CriticalPercolation
end
end
end

end OAI
