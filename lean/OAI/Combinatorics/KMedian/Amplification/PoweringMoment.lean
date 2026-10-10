import Mathlib
import OAI.Combinatorics.KMedian.Amplification.PoweringMean
import OAI.Combinatorics.KMedian.Expanders.PathCount

namespace OAI

section Inline_PCPPoweringMoment

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

namespace PortCSP
variable {V D A : Type} [Fintype V] [Nonempty V] [Fintype D] [Nonempty D]
  [Fintype A] [Inhabited A] [DecidableEq A]
variable {G : PortGraph V D} (C : PortCSP G A) {cap : ℕ}

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma diagHit_nonneg (a : V → Advice D A cap) (x : V → A) (i j n : ℕ) (p : G.Walk n) :
    0 ≤ C.diagHit a x i j n p := by
  unfold diagHit
  split_ifs
  · exact C.rootHit_nonneg a x i j _
  · rfl

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma diagHit_le_ith (a : V → Advice D A cap) (x : V → A) (i j n : ℕ) (p : G.Walk n) :
    C.diagHit a x i j n p ≤ p.ithHit (bad := C.Bad x) i := by
  unfold diagHit
  split_ifs with h
  · have hi : i < n := by omega
    have hr := C.rootHit_le a x i j (PortGraph.Walk.centerEquiv i j (p.cast h))
    simpa only [cutHit,PortGraph.Walk.center_vertex,PortGraph.Walk.center_port,
      PortGraph.Walk.cast_vertex,PortGraph.Walk.cast_port,PortGraph.Walk.ithHit,dite_eq_left hi] using hr
  · exact p.ithHit_nonneg i

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma rowHit_le (a : V → Advice D A cap) (x : V → A) (i L n : ℕ) (p : G.Walk n) :
    (∑ j ∈ range (L+1), C.diagHit a x i j n p) ≤ p.ithHit (bad := C.Bad x) i := by
  classical
  calc
    _ ≤ ∑ j ∈ range (L+1), if j=n-i-1 then p.ithHit (bad := C.Bad x) i else 0 := by
      apply sum_le_sum
      intro j _
      by_cases hj : j=n-i-1
      · rw [ite_eq_left hj]
        exact C.diagHit_le_ith a x i j n p
      · rw [ite_eq_right hj]
        have hn : n ≠ i+(j+1) := by omega
        simp [diagHit,hn]
    _ ≤ _ := by
      simp only [sum_ite_eq']
      split_ifs
      · exact le_rfl
      · exact p.ithHit_nonneg i

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma witness_bounds (a : V → Advice D A cap) (x : V → A) (L n : ℕ) (p : G.Walk n) :
    0 ≤ C.witness a x L n p ∧ C.witness a x L n p ≤ p.hitCount (bad := C.Bad x) := by
  constructor
  · exact sum_nonneg (fun i _ => sum_nonneg (fun j _ => C.diagHit_nonneg a x i j n p))
  · calc
      _ ≤ ∑ i ∈ range (L+1), p.ithHit (bad := C.Bad x) i :=
        sum_le_sum (fun i _ => C.rowHit_le a x i L n p)
      _ ≤ _ := p.partial_hits_le (L+1)

omit [Fintype V] [Nonempty V] [Fintype D] [Nonempty D] [Fintype A] in
lemma stoppedWitness_bounds (a : V → Advice D A cap) (x : V → A) (t L : ℕ)
    (z : (Fin cap → Fin (t+1)) × G.Walk cap) :
    0 ≤ C.stoppedWitness a x t L z ∧ C.stoppedWitness a x t L z ≤ z.2.hitCount (bad := C.Bad x) := by
  have h := C.witness_bounds a x L (Stopped.length t cap z.1)
    (z.2.segment 0 (Stopped.length t cap z.1) (by have := Stopped.length_le t cap z.1; omega))
  exact ⟨h.1,h.2.trans (z.2.prefix_hitCount_le _ (Stopped.length_le t cap z.1))⟩

omit [Fintype A] in
theorem witness_energy_le (hG : G.Contracts (1/2)) (a : V → Advice D A cap)
    (x : V → A) (t L : ℕ) :
    energy (C.stoppedWitness a x t L) ≤
      5*cap*testRate (C.Bad x) + (cap:ℝ)^2*(testRate (C.Bad x))^2 := by
  unfold energy
  rw [expect_prod]
  calc
    _ ≤ 𝔼 c : Fin cap → Fin (t+1), 𝔼 p : G.Walk cap, (p.hitCount (bad := C.Bad x))^2 := by
      apply expect_le_expect
      intro c _
      apply expect_le_expect
      intro p _
      have h := C.stoppedWitness_bounds a x t L (c,p)
      exact pow_le_pow_left₀ h.1 h.2 2
    _ = 𝔼 p : G.Walk cap, (p.hitCount (bad := C.Bad x))^2 := Fintype.expect_const _
    _ ≤ _ := PortGraph.Walk.hitCount_second_moment (C.bad_symmetric x) hG

theorem witness_support_bound (hG : G.Contracts (1/2)) (a : V → Advice D A cap)
    (t L : ℕ) (hcap : 2*L+1 < cap) :
    ((t:ℝ) * testRate (C.Bad (G.plurality a t L)) *
      (PortGraph.totalMass t L / Fintype.card A)^2)^2 ≤
    testRate (fun z => C.stoppedWitness a (G.plurality a t L) t L z ≠ 0) *
      (5*cap*testRate (C.Bad (G.plurality a t L)) +
        (cap:ℝ)^2*(testRate (C.Bad (G.plurality a t L)))^2) := by
  have hm := C.witness_mean_ge a t L hcap
  have he := C.witness_energy_le hG a (G.plurality a t L) t L
  have hc := mean_sq_le_support_energy (C.stoppedWitness a (G.plurality a t L) t L)
  have hn : 0 ≤ (t:ℝ) * testRate (C.Bad (G.plurality a t L)) *
      (PortGraph.totalMass t L / Fintype.card A)^2 :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (testRate_nonneg _)) (sq_nonneg _)
  exact (pow_le_pow_left₀ hn hm 2).trans (hc.trans
    (mul_le_mul_of_nonneg_left he (testRate_nonneg _)))

end PortCSP
end MetricKMedian.PCP

end Inline_PCPPoweringMoment

end OAI
