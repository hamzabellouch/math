import Mathlib
import OAI.Analysis.Commutator.DecomposableLimit
import OAI.Analysis.Commutator.TightField

namespace OAI

noncomputable section

section

noncomputable section

open MeasureTheory Filter

open scoped Topology InnerProductSpace

namespace Kadison.Decomposable

variable {Ω H : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [IsFiniteMeasure μ] [TopologicalSpace.SeparableSpace H]

lemma fieldAlgebra_isClosed (Q : Ω → VonNeumannAlgebra H) :
    IsClosed (fieldAlgebra μ Q : Set (Lp H 2 μ →L[ℂ] Lp H 2 μ)) := by
  apply isClosed_of_closure_subset
  intro A hA
  have hcomm (s : Set Ω) (hs : MeasurableSet s) : Commute A (indicatorOperator μ s hs) := by
    apply closure_minimal (t:={B : Lp H 2 μ →L[ℂ] Lp H 2 μ |
      B*indicatorOperator μ s hs=indicatorOperator μ s hs*B}) ?_
      (isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)) hA
    intro B hB
    exact fieldMember_commutes_indicator μ Q hB s hs
  obtain ⟨T,hm,hb,he⟩ := exists_field_of_commutes_indicator μ A hcomm
  have hseq (n : ℕ) : ∃ B : Lp H 2 μ →L[ℂ] Lp H 2 μ,
      B∈fieldAlgebra μ Q ∧ ‖B-A‖<1/((n:ℝ)+1) := by
    obtain ⟨B,hB,hd⟩ := Metric.mem_closure_iff.mp hA (1/((n:ℝ)+1)) (by positivity)
    exact ⟨B,hB,by simpa only [dist_eq_norm,norm_sub_rev] using hd⟩
  choose B hB hdist using hseq
  have hBn (n : ℕ) : ‖B n‖≤‖A‖+1 := by
    have heps : 1/((n:ℝ)+1)≤1 := (div_le_one (by positivity)).mpr (by linarith [Nat.cast_nonneg (α:=ℝ) n])
    have hnorm := norm_sub_le (B n-A) (-A)
    have hn : ‖B n‖≤‖B n-A‖+‖A‖ := by simpa using hnorm
    linarith [hdist n]
  have hfields (n : ℕ) := fieldMember_tight μ Q (hB n) (by positivity : 0≤‖A‖+1) (hBn n)
  choose S hS hSb hSe hSm using hfields
  have hlimB : Tendsto B atTop (𝓝 A) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨N,hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [dist_eq_norm]
    apply (hdist n).trans_le
    exact (one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)).trans hN.le
  have hlim (f : Lp H 2 μ) : Tendsto
      (fun n => operator μ (S n) (hS n) (hSb n) f) atTop
      (𝓝 (operator μ T hm hb f)) := by
    have hh : Tendsto (fun n => B n f) atTop (𝓝 (A f)) :=
      (ContinuousLinearMap.apply ℂ (Lp H 2 μ) f).continuous.tendsto A |>.comp hlimB
    simpa only [←hSe,←he] using hh
  exact ⟨T,hm,‖A‖,hb,norm_nonneg A,he,
    mem_ae_of_bounded_strong_limit μ Q T hm hb S hS (by positivity) hSb hSm hlim⟩

end Kadison.Decomposable

end

end
end

end OAI
