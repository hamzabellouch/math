import OAI.Analysis.CircleDomains.Sobolev.SummableEnergyCutoffs

namespace OAI

/-! The pointwise sum of the cutoff differential norms is itself in L2,
with the sum of their L2 norms as a bound. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

 theorem l2_tsum_of_summable_norms (g : ℕ → ℂ → ℝ)
    (hg : ∀ n, MemLp (g n) 2 volume)
    (hs : Summable (fun n => (eLpNorm (g n) 2 volume).toReal)) :
    MemLp (fun z => ∑' n, g n z) 2 volume ∧
      (eLpNorm (fun z => ∑' n, g n z) 2 volume).toReal ≤
        ∑' n, (eLpNorm (g n) 2 volume).toReal := by
  let F : ℕ → Lp ℝ 2 volume := fun n => (hg n).toLp (g n)
  have hnorm : Summable (fun n => ‖F n‖) := by
    simpa only [F, Lp.norm_toLp] using hs
  have hfinite : (∑' n, ‖F n‖ₑ) ≠ (⊤ : ℝ≥0∞) := by
    have hh := hs.tsum_ofReal_lt_top
    have he (n : ℕ) : ENNReal.ofReal (eLpNorm (g n) 2 volume).toReal = eLpNorm (g n) 2 volume :=
      ENNReal.ofReal_toReal (hg n).ne_top
    simp_rw [he] at hh
    simpa only [F, Lp.enorm_toLp] using hh.ne
  have hvalues : ∀ᵐ z ∂volume, ∀ n, F n z = g n z :=
    ae_all_iff.mpr (fun n => (hg n).coeFn_toLp)
  have hae : (⇑(∑' n, F n) : ℂ → ℝ) =ᵐ[volume] (fun z => ∑' n, g n z) := by
    filter_upwards [Lp.coeFn_tsum hfinite, hvalues] with z hz hv
    rw [hz]
    exact tsum_congr hv
  refine ⟨(Lp.memLp (∑' n, F n)).ae_eq hae, ?_⟩
  rw [← eLpNorm_congr_ae hae, ← Lp.norm_def]
  simpa only [F, Lp.norm_toLp] using norm_tsum_le_tsum_norm hnorm

end CircleDomainRigidity

end

end OAI
