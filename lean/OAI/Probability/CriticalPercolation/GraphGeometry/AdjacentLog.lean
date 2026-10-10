import Mathlib
import OAI.Probability.CriticalPercolation.Model
import OAI.Probability.CriticalPercolation.Criticality.MinimalPair
import OAI.Probability.CriticalPercolation.Criticality.WitnessEvents

namespace OAI

section
section
noncomputable section
open Set MeasureTheory ProbabilityTheory
open scoped Classical

namespace CriticalPercolation.BondGraph
variable {V E : Type*} (G : BondGraph V E)

lemma adjacent_log_lower (A ε : ℝ) (hA : 0<A) (hε : 0<ε)
    (p : unitInterval) (hεp : ε≤p) (s : ℕ) (hs : 1 ≤ s) (e : E)
    (hbound : ∀ K : ℕ,
      (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^K)) ≤
        A/((p:ℝ)*(2:ℝ)^K))
    (hpos : 0<(G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s)) :
    Real.log s/2-Real.log (2*A/ε) ≤
      -Real.log ((G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s)) := by
  let K := Nat.log 4 s
  let δ := (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s)
  have hK : 4^K ≤ s := Nat.pow_log_le_self 4 (by omega)
  have hu : (s:ℝ) < (4:ℝ)^(K+1) := by
    exact_mod_cast Nat.lt_pow_succ_log_self (by norm_num : 1<(4:ℕ)) s
  have hp : 0<(p:ℝ) := hε.trans_le hεp
  have hm : δ≤A/(ε*(2:ℝ)^K) := by
    calc _ ≤ (G.law p).real (G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 (4^K)) :=
            measureReal_mono (G.twoClusterEvent_antitone _ _ hK)
         _ ≤ A/((p:ℝ)*(2:ℝ)^K) := hbound K
         _ ≤ _ := div_le_div_of_nonneg_left hA.le (by positivity)
            (mul_le_mul_of_nonneg_right hεp (by positivity))
  have hl := Real.log_le_log hpos hm
  rw [Real.log_div hA.ne' (by positivity),Real.log_mul hε.ne' (by positivity),Real.log_pow] at hl
  have hspos : (0:ℝ)<s := Nat.cast_pos.mpr (by omega)
  have hls := Real.log_lt_log hspos hu
  rw [Real.log_pow,Nat.cast_add,Nat.cast_one] at hls
  have hlog4 : Real.log 4=2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [hlog4] at hls
  have heq : Real.log (2*A/ε)=Real.log 2+Real.log A-Real.log ε := by
    rw [Real.log_div (by positivity) hε.ne',Real.log_mul (by norm_num) hA.ne']
  rw [heq]
  change Real.log δ ≤ _ at hl
  change Real.log s/2-_ ≤ -Real.log δ
  linarith

lemma twoClusterEvent_of_adj {u v : V} (h : G.fullGraph.Adj u v) :
    ∃ e : E, ∀ s, G.twoClusterEvent u v s =
      G.twoClusterEvent (G.ends e).out.1 (G.ends e).out.2 s := by
  obtain ⟨⟨e,_,he⟩,_⟩ := h
  refine ⟨e,fun s => G.twoClusterEvent_sym2 ?_ s⟩
  exact he.symm.trans (G.ends e).out_eq.symm

end CriticalPercolation.BondGraph
end
end
end

end OAI
