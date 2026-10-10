import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L1Space.AEEqFun
import Mathlib.Topology.Instances.ENNReal.Lemmas

namespace OAI

/-! # Completing real L1 sequences with uniformly convergent approximations -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace BoltzmannNonuniqueness.Compactness
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

private theorem real_sub_triangle (f g h : X → ℝ) :
    eLpNorm (f-h) 1 μ ≤ eLpNorm (f-g) 1 μ+eLpNorm (g-h) 1 μ := by
  have he : f-h = (f-g)+(g-h) := by ext x; simp
  rw [he]
  exact eLpNorm_add_le (by norm_num)

theorem l1_limit_of_uniform_approximation {f : ℕ → X → ℝ}
    {u : ℕ → ℕ → X → ℝ} {g : ℕ → X → ℝ} {δ : ℕ → ℝ≥0∞}
    (hf : ∀ n, Integrable (f n) μ) (hδ : Tendsto δ atTop (𝓝 0))
    (he : ∀ j n, eLpNorm (f n-u j n) 1 μ ≤ δ j)
    (hc : ∀ j, Tendsto (fun n => eLpNorm (u j n-g j) 1 μ) atTop (𝓝 0)) :
    ∃ q : X → ℝ, Integrable q μ ∧
      Tendsto (fun n => eLpNorm (f n-q) 1 μ) atTop (𝓝 0) := by
  let F : ℕ → Lp ℝ 1 μ := fun n => (memLp_one_iff_integrable.mpr (hf n)).toLp (f n)
  have hF : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    have hε8 : 0 < ENNReal.ofReal (ε/8) := ENNReal.ofReal_pos.mpr (by positivity)
    obtain ⟨j,hj⟩ := (hδ.eventually (gt_mem_nhds hε8)).exists
    obtain ⟨N,hN⟩ := eventually_atTop.mp ((hc j).eventually (gt_mem_nhds hε8))
    refine ⟨N,fun m hm n hn => ?_⟩
    have hb : eLpNorm (f m-f n) 1 μ ≤ ENNReal.ofReal (ε/2) := by
      calc
        _ ≤ eLpNorm (f m-u j m) 1 μ+eLpNorm (u j m-f n) 1 μ := real_sub_triangle _ _ _
        _ ≤ eLpNorm (f m-u j m) 1 μ+
            (eLpNorm (u j m-g j) 1 μ+eLpNorm (g j-f n) 1 μ) :=
          add_le_add le_rfl (real_sub_triangle _ _ _)
        _ ≤ eLpNorm (f m-u j m) 1 μ+
            (eLpNorm (u j m-g j) 1 μ+
              (eLpNorm (g j-u j n) 1 μ+eLpNorm (u j n-f n) 1 μ)) := by
          gcongr
          exact real_sub_triangle _ _ _
        _ ≤ ENNReal.ofReal (ε/8)+(ENNReal.ofReal (ε/8)+
            (ENNReal.ofReal (ε/8)+ENNReal.ofReal (ε/8))) := by
          rw [eLpNorm_sub_comm (g j) (u j n),eLpNorm_sub_comm (u j n) (f n)]
          exact add_le_add ((he j m).trans hj.le)
            (add_le_add (hN m hm).le (add_le_add (hN n hn).le ((he j n).trans hj.le)))
        _ = _ := by rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]; congr 1; ring
    apply (ENNReal.ofReal_lt_ofReal_iff hε).mp
    rw [← Lp.edist_dist]
    change edist ((memLp_one_iff_integrable.mpr (hf m)).toLp (f m))
      ((memLp_one_iff_integrable.mpr (hf n)).toLp (f n)) < _
    rw [Lp.edist_toLp_toLp]
    exact hb.trans_lt (ENNReal.ofReal_lt_ofReal_iff hε |>.mpr (by linarith))
  obtain ⟨q,hq⟩ := cauchySeq_tendsto_of_complete hF
  refine ⟨q,L1.integrable_coeFn q,?_⟩
  have hlim := hq.edist (tendsto_const_nhds (x := q))
  simp only [edist_self] at hlim
  apply hlim.congr'
  exact Filter.Eventually.of_forall (fun n => by
    dsimp only
    rw [Lp.edist_def]
    apply eLpNorm_congr_ae
    exact ((memLp_one_iff_integrable.mpr (hf n)).coeFn_toLp).sub ae_eq_rfl)

end BoltzmannNonuniqueness.Compactness

end

end OAI
