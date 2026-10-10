import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.MonotoneIndicatorUpper
import OAI.Probability.CriticalPercolation.GraphGeometry.UniformGeometry
import OAI.Probability.CriticalPercolation.Criticality.TwoPointSelf

namespace OAI

section
section CurrentModule12
noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma subcritical_local_rate_bound (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (p : unitInterval) (hp : p < G.criticalProbability) (o : V)
    (γ : ℝ) (N : ℕ)
    (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ))
    (n : ℕ) (hn : 1 ≤ n) (a : ℝ) (ha : 0 ≤ a)
    (hlocal : ∀ x y : V, y ∈ G.vertexBall x n → a ≤ twoPoint G p x y) :
    a * Real.exp (γ*n) ≤ 1 := by
  let : Nonempty V := ⟨o⟩
  obtain ⟨C,hC⟩ := subcritical_susceptibility G hl hq p hp
  have hbound (k : ℕ) (hk : N ≤ k) : (a * Real.exp (γ*n))^k ≤ C := by
    have hkn : N ≤ k*n := hk.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left k hn)
    let B := G.vertexBall o (k*n)
    have hB := G.vertexBall_finite hl o (k*n)
    have hsum : (B.ncard : ℝ)*a^k ≤ C := by
      calc
        _ = ∑ _v ∈ hB.toFinset, a^k := by simp only [B,Finset.sum_const,nsmul_eq_mul,Set.ncard_eq_toFinset_card _ hB]
        _ ≤ ∑ v ∈ hB.toFinset, twoPoint G p o v := by
          apply Finset.sum_le_sum
          intro v hv
          exact local_bound_propagation G p n a ha hlocal k o v (hB.mem_toFinset.mp hv)
        _ ≤ C := hC _ o
    have hvol : Real.exp (γ*(k*n : ℕ)) ≤ (B.ncard : ℝ) := by
      calc
        _ ≤ Real.exp (Real.log (B.ncard : ℝ)) := Real.exp_le_exp.mpr (hgrowth (k*n) hkn o)
        _ = _ := Real.exp_log (Nat.cast_pos.mpr (G.vertexBall_ncard_pos hl o (k*n)))
    calc
      _ = Real.exp (γ*(k*n : ℕ))*a^k := by
        rw [mul_pow,← Real.exp_nat_mul,Nat.cast_mul,mul_comm (a^k)]
        congr 2
        ring
      _ ≤ (B.ncard : ℝ)*a^k := mul_le_mul_of_nonneg_right hvol (pow_nonneg ha k)
      _ ≤ C := hsum
  by_contra hnot
  have hrate : 1 < a * Real.exp (γ*n) := lt_of_not_ge hnot
  have ht := (tendsto_pow_atTop_atTop_of_one_lt hrate).eventually (eventually_gt_atTop C)
  obtain ⟨k,hk,hkC⟩ := ((eventually_ge_atTop N).and ht).exists
  exact (not_lt_of_ge (hbound k hk)) hkC

theorem no_uniform_critical_twoPoint (hl : G.LocallyFinite) (hq : G.QuasiTransitive)
    (hpc : 0 < G.criticalProbability) (o : V)
    (γ : ℝ) (hγ : 0 < γ) (N : ℕ)
    (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ)) :
    ¬ ∃ θ : ℝ, 0 < θ ∧ ∀ x y : V, θ ≤ twoPoint G G.criticalProbability x y := by
  rintro ⟨θ,hθ,hall⟩
  let a := θ/2
  have ha : 0 < a := half_pos hθ
  obtain ⟨n,hn⟩ := exists_nat_gt (1/(a*γ))
  have hnexp : 1 < a*γ*(n:ℝ) := by
    have hh := (div_lt_iff₀ (mul_pos ha hγ)).mp hn
    nlinarith
  have hn1 : 1 ≤ n := by
    by_contra hn1
    have hn0 : n=0 := by omega
    simp only [hn0,Nat.cast_zero,mul_zero] at hnexp
    linarith
  have hlarge : 1 < a*Real.exp (γ*n) := by
    have hh := mul_le_mul_of_nonneg_left (Real.add_one_le_exp (γ*n)) ha.le
    nlinarith
  obtain ⟨q,hqp,hqbound⟩ := exists_lower_local_parameter G hl hq
    G.criticalProbability hpc n a (fun x y _ =>
      lt_of_lt_of_le (by dsimp [a]; linarith) (hall x y))
  exact (not_lt_of_ge (subcritical_local_rate_bound G hl hq q hqp o γ N hgrowth n hn1
    a ha.le (fun x y h => (hqbound x y h).le))) hlarge

end CriticalPercolation.Sharpness
end
end CurrentModule12

section CurrentModule13

noncomputable section
open Set MeasureTheory Filter Topology
open scoped Classical BigOperators

namespace CriticalPercolation.Sharpness
variable {V E : Type*} (G : BondGraph V E) [Countable V] [Countable E]

lemma harris_infiniteEvent (p : unitInterval) (x y : V) :
    (G.law p).real (G.infiniteEvent x) * (G.law p).real (G.infiniteEvent y) ≤
      (G.law p).real (G.infiniteEvent x ∩ G.infiniteEvent y) := by
  let K := (Set.to_countable (Set.univ : Set V)).finiteExhaustion
  have hinter : (⋂ n, G.hitEvent x (K n)ᶜ ∩ G.hitEvent y (K n)ᶜ) =
      G.infiniteEvent x ∩ G.infiniteEvent y := by
    rw [Set.iInter_inter_distrib,← G.infiniteEvent_eq_iInter_hit_compl K x,
      ← G.infiniteEvent_eq_iInter_hit_compl K y]
  have hlim := tendsto_measure_iInter_atTop (μ := G.law p)
    (fun n => ((G.measurableSet_hitEvent x (K n)ᶜ).inter
      (G.measurableSet_hitEvent y (K n)ᶜ)).nullMeasurableSet)
    (show Antitone (fun n => G.hitEvent x (K n)ᶜ ∩ G.hitEvent y (K n)ᶜ) from
      fun _ _ h => Set.inter_subset_inter
        (G.hitEvent_mono_target x (Set.compl_subset_compl.mpr (K.mono h)))
        (G.hitEvent_mono_target y (Set.compl_subset_compl.mpr (K.mono h))))
    ⟨0,measure_ne_top _ _⟩
  rw [hinter] at hlim
  apply le_of_tendsto_of_tendsto
    ((G.tendsto_real_hit_compl p K x).mul (G.tendsto_real_hit_compl p K y))
    ((ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hlim)
  apply Eventually.of_forall
  intro n
  simpa only [BernoulliProduct.law_const,BondGraph.law,
    measureReal_def,Function.comp_apply] using
    BernoulliProduct.harris_finiteWitness (fun _ : E => p)
      (G.hitEvent x (K n)ᶜ) (G.hitEvent y (K n)ᶜ)
      (G.hitEvent_isUpperSet _ _) (G.hitEvent_isUpperSet _ _)
      (G.hitEvent_hasFiniteOpenWitness _ _) (G.hitEvent_hasFiniteOpenWitness _ _)

lemma unique_twoPoint_lower (p : unitInterval)
    (hu : ∀ᵐ ω ∂G.law p, ∀ x y, (G.cluster ω x).Infinite →
      (G.cluster ω y).Infinite → (G.openGraph ω).Reachable x y) (x y : V) :
    (G.law p).real (G.infiniteEvent x) * (G.law p).real (G.infiniteEvent y) ≤
      twoPoint G p x y := by
  apply (harris_infiniteEvent G p x y).trans
  unfold twoPoint
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [hu] with ω hω
  intro h
  rw [hit_singleton_eq]
  exact hω x y h.1 h.2

theorem critical_null_of_unique (hc : G.fullGraph.Connected)
    (hl : G.LocallyFinite) (hq : G.QuasiTransitive) (o : V)
    (γ : ℝ) (hγ : 0 < γ) (N : ℕ)
    (hgrowth : ∀ m≥N, ∀ v : V, γ*m ≤ Real.log ((G.vertexBall v m).ncard : ℝ))
    (hu : ∀ᵐ ω ∂G.law G.criticalProbability, ∀ x y, (G.cluster ω x).Infinite →
      (G.cluster ω y).Infinite → (G.openGraph ω).Reachable x y) :
    G.law G.criticalProbability G.percolates = 0 := by
  by_contra hnot
  have hpos : 0 < G.law G.criticalProbability G.percolates := bot_lt_iff_ne_bot.mpr hnot
  obtain ⟨θ,hθ,hall⟩ := G.uniform_rooted_probability hc hl hq G.criticalProbability hpos
  have hpc : 0 < G.criticalProbability := by
    by_contra h
    have he : G.criticalProbability = 0 := le_antisymm (not_lt.mp h) (bot_le)
    rw [he,G.law_zero_percolates] at hpos
    exact (lt_irrefl _ hpos)
  apply no_uniform_critical_twoPoint G hl hq hpc o γ hγ N hgrowth
  refine ⟨θ*θ,mul_pos hθ hθ,?_⟩
  intro x y
  exact (mul_le_mul (hall x) (hall y) hθ.le (measureReal_nonneg)).trans
    (unique_twoPoint_lower G G.criticalProbability hu x y)

end CriticalPercolation.Sharpness
end
end CurrentModule13

end

end OAI
