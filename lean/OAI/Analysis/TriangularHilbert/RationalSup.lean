import OAI.Analysis.TriangularHilbert.EndpointContinuity

namespace OAI

section
namespace TriangularHilbert
open MeasureTheory Filter Heat
open scoped Topology ENNReal
noncomputable section

abbrev RatEndpoints := {p : ℚ×ℚ // 0 < p.1 ∧ p.1 < p.2}
instance : Inhabited RatEndpoints := ⟨⟨(1,2),by norm_num⟩⟩

def RatEndpoints.toEndpoints (q : RatEndpoints) : Endpoints where
  lower := q.1.1
  upper := q.1.2
  lower_pos := by exact_mod_cast q.2.1
  lower_lt_upper := by exact_mod_cast q.2.2

def cyclicMax (B C : Plane → ℂ) (z : Plane) : ℝ≥0∞ :=
  ⨆ q : RatEndpoints, ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel (q.1.1:ℝ) (q.1.2:ℝ)) z‖

lemma cyclicHard_le_cyclicMax {B C : Plane → ℂ} {z : Plane} (hz : CubicSliceGood B C z)
    {r R : ℝ} (hr : 0 < r) (hR : r < R) :
    ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel r R) z‖ ≤ cyclicMax B C z := by
  obtain ⟨u,_,hu,htu⟩ := Real.exists_seq_rat_strictMono_tendsto r
  obtain ⟨v,_,hv,htv⟩ := Real.exists_seq_rat_strictAnti_tendsto R
  have ht := (continuousAt_cyclicHard hz hr hR).tendsto.comp (htu.prodMk_nhds htv)
  apply le_of_tendsto (ENNReal.continuous_ofReal.continuousAt.tendsto.comp ht.norm)
  filter_upwards [htu (eventually_gt_nhds hr)] with n hn
  have hq : 0 < u n ∧ u n < v n := by
    constructor
    · exact_mod_cast (show (0:ℝ) < (u n:ℝ) from hn)
    · exact_mod_cast ((hu n).trans (hR.trans (hv n)))
  exact le_iSup (fun q : RatEndpoints => ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel (q.1.1:ℝ) (q.1.2:ℝ)) z‖)
    ⟨(u n,v n),hq⟩

lemma cyclicMax_eq_iSup {B C : Plane → ℂ} {z : Plane} (hz : CubicSliceGood B C z) :
    cyclicMax B C z = ⨆ E : Endpoints, ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel E.lower E.upper) z‖ := by
  apply le_antisymm
  · apply iSup_le
    intro q
    exact le_iSup (fun E : Endpoints => ENNReal.ofReal ‖cyclicKernelOutput B C (hardKernel E.lower E.upper) z‖) q.toEndpoints
  · apply iSup_le
    intro E
    exact cyclicHard_le_cyclicMax hz E.lower_pos E.lower_lt_upper

def RatEndpoints.sequence (n : ℕ) : RatEndpoints := (Encodable.decode (α := RatEndpoints) n).getD default
lemma RatEndpoints.sequence_surjective : Function.Surjective RatEndpoints.sequence := by
  intro q
  exact ⟨Encodable.encode q,by simp [RatEndpoints.sequence,Encodable.encodek]⟩
end
end TriangularHilbert
end

end OAI
