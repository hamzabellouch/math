import OAI.Combinatorics.SparsestCut.Logarithms

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut
open Filter
noncomputable section

theorem mainGap :
    ∃ c : ℝ, 0 < c ∧
      ∃ n : ℕ → ℕ, ∃ C : (j : ℕ) → Capacity (n j),
        (∀ j, 2 ≤ n j) ∧
        Tendsto n atTop atTop ∧
        (∀ j, 0 < glValue (C j)) ∧
        ∀ᶠ j in atTop,
          c * Real.sqrt (Real.log (n j : ℝ)) / (Real.log (Real.log (n j : ℝ))) ^ 3 ≤
            OPT (C j) / glValue (C j) := by
  classical
  let α : ℝ := KernelApprox.cstar/6
  let β : ℝ := SourceContraction.C+1
  have hα : 0<α := div_pos KernelApprox.cstar_pos (by norm_num)
  have hβ : 0<β := by have hc := SourceContraction.C_pos; dsimp [β]; linarith
  have hcast : Tendsto (fun d : ℕ => (d:ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hevent : ∀ᶠ d : ℕ in atTop, Nonempty (PivotFamily.PFamily d) ∧
      3000≤d ∧ 1≤Real.log d ∧ SourceContraction.H≤(d:ℝ) ∧
      4*SourceWeighted.D≤(d:ℝ) ∧ SourceMetric.C₀+1≤α*(d:ℝ) := by
    filter_upwards [PivotFamily.pivot_directions_exist,eventually_ge_atTop 3000,
      (Real.tendsto_log_atTop.comp hcast).eventually (eventually_ge_atTop 1),
      hcast.eventually (eventually_ge_atTop SourceContraction.H),
      hcast.eventually (eventually_ge_atTop (4*SourceWeighted.D)),
      hcast.eventually (eventually_ge_atTop ((SourceMetric.C₀+1)/α))] with d hf hd hl hH hD ha
    exact ⟨hf,hd,hl,hH,hD,by simpa only [mul_comm] using (div_le_iff₀ hα).mp ha⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hevent
  have hex : ∀ j : ℕ, ∃ (n : ℕ) (C : Capacity n),
      (j+N+1)^(j+N+1)≤n ∧ n≤(j+N+1)^(4030*(j+N+1)) ∧
      2≤n ∧ 1≤OPT C ∧ 0<glValue C ∧ glValue C≤β*RateComparison.weight (j+N+1:ℕ)/(α*(j+N+1:ℕ)) := by
    intro j
    obtain ⟨⟨f⟩,hd,hl,hH,hD,ha⟩ := hN (j+N+1) (by omega)
    exact SourceUniform.instance_exists f hd hl hH hD ha
  choose n C hlo hhi hn hopt hgl hbound using hex
  refine ⟨α/(β*Real.sqrt 4030),by positivity,n,C,hn,?_,hgl,?_⟩
  · apply tendsto_atTop_mono (fun j => ?_) tendsto_id
    have hd1 : 1≤j+N+1 := by omega
    have hp : j+N+1≤(j+N+1)^(j+N+1) := by
      simpa using (Nat.pow_le_pow_right hd1 hd1 : (j+N+1)^1≤(j+N+1)^(j+N+1))
    exact (show j≤j+N+1 by omega).trans (hp.trans (hlo j))
  · exact Filter.Eventually.of_forall (fun j => RateComparison.gap_of_gl
      (by omega : 0<j+N+1) (hN (j+N+1) (by omega)).2.2.1
      (hlo j) (hhi j) hα hβ (hopt j) (hgl j) (hbound j))
end
end UniformSparsestCut

end

end OAI
