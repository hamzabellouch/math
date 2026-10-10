import Mathlib
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialBudget
import OAI.Combinatorics.SharpRamsey.Selection.SourceGridShape

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real Filter SourceScales
open scoped Topology NNReal
noncomputable section

lemma Budget.mono_grid {σ P : ℝ} {L : ℝ≥0} {R N M p h : ℕ}
    (hb : Budget σ P L R N p h) (hm : M≤N) : Budget σ P L R M p h := by
  have hm' : (M:ℝ)≤N := by exact_mod_cast hm
  have hP : 0≤P := le_trans (by norm_num) hb.large
  refine { hb with sum := ?_, cert := ?_, shift := ?_ }
  · apply le_trans _ hb.sum
    gcongr
  · apply le_trans _ hb.cert
    unfold MomentBudgetBridge.certificateOverhead
    gcongr
  · apply le_trans _ hb.shift
    unfold MomentBudgetBridge.shiftOverhead
    gcongr

theorem eventually_bounded_budget {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R N : ℕ),Admissible σ η D R → (N:ℝ)≤σ^2 →
      ∃ p h : ℕ,(p:ℝ)≤σ^2 ∧ Budget σ (scaleP σ η D R) (Real.toNNReal (scaleL σ η D)) R N p h := by
  filter_upwards [eventually_enumeration_budgets hη,
    eventually_pencil_scalar_budgets hη 400000,eventually_P_le_linear hη (1/12) (by norm_num),
    eventually_uniform_L hη (eventually_ge_atTop (100000000000000:ℝ)),
    eventually_uniform_R hη 400,PlanarLearning.eventually_schedule hη,eventually_ge_atTop (10002:ℝ)]
    with σ he hp hu hl hr hs hσ D R N had hN
  let L := scaleL σ η D
  let P := scaleP σ η D R
  have hL : 100000000000000≤L := hl D R had
  have hR : (400:ℝ)≤R := hr D R had
  have hL0 : 0≤L := by linarith
  have hLP : L≤P := by change L≤L*R; nlinarith
  have hP0 : 0<P := by linarith
  obtain ⟨p,hp0,hpe,hpl,hpu⟩ := PlanarLearning.even_order (by linarith : 0<σ) hP0
  obtain ⟨hLa,hcert,hshift,hpb,hps,h,hh,hR',hhs,hhr⟩ := he D R p N had hpu hN
  obtain ⟨hdiag,hpow,hsum,htwo,hvar⟩ := hp D R N had hN
  have hlu : (Real.toNNReal L:ℝ)=L := Real.coe_toNNReal _ hL0
  have hPu : P≤σ/12 := by simpa only [div_eq_mul_inv,mul_comm,one_mul] using hu D R had
  have hB : 2*exp (6*P)≤exp σ := by
    have h2 : 2≤exp (σ-6*P) := by have := add_one_le_exp (σ-6*P); linarith
    calc
      _ ≤ exp (σ-6*P)*exp (6*P) := mul_le_mul_of_nonneg_right h2 (exp_pos _).le
      _ = _ := by rw [←exp_add]; congr 1; ring
  change ∃ p h : ℕ,(p:ℝ)≤σ^2 ∧ Budget σ P (Real.toNNReal L) R N p h
  refine ⟨p,h,moment_order_le hσ (by linarith) hpu,?_⟩
  constructor
  · linarith
  · exact hL.trans hLP
  · linarith
  · exact hB
  · rw [hlu]; rfl
  · rw [hlu]; linarith
  · exact hR'
  · exact hp0
  · exact hpe
  · exact hpl
  · simpa only [hlu] using hs D R had
  · exact hdiag
  · simpa only [hlu] using hpow
  · simpa only [hlu] using hsum
  · exact htwo
  · simpa only [hlu] using hvar
  · exact hcert
  · exact hshift
  · exact hpb
  · exact hps
  · exact hh
  · exact hhs
  · exact hhr

end
end SharpLogRamsey.SpatialLearning

end

end OAI
