import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.PlanarScales
import OAI.Combinatorics.SharpRamsey.Spatial.SpatialPencils

namespace OAI

section
namespace SharpLogRamsey.SpatialLearning
open Finset Real Filter SourceScales
open scoped Topology NNReal
noncomputable section

structure Budget (σ P : ℝ) (L : ℝ≥0) (R N p h : ℕ) : Prop where
  sigma : 2≤σ
  large : 100000000000000≤P
  upper : P≤σ
  B : 2*exp (6*P)≤exp σ
  identity : P=(L:ℝ)*R
  Llarge : 10000≤(L:ℝ)
  Rlarge : 400≤R
  p_pos : 0<p
  p_even : Even p
  order : 10000*σ≤(p:ℝ)*P
  sparseSchedules : (R:ℝ)*exp (-(24/25:ℝ)*(L:ℝ))≤1/10
  diag : 400000*2^R≤exp (P/20)
  pow : (2*(L:ℝ)^2)^R≤exp (P/25)
  sum : (400000:ℝ)^2*exp ((L:ℝ)/50)+(N:ℝ)*2^R*exp (P/50)≤exp (P/20)
  two : 2≤exp (P/20)
  variance : 400000*exp ((L:ℝ)/1000)≤exp (P/100)
  cert : MomentBudgetBridge.certificateOverhead p N P≤exp (2*P/25)
  shift : MomentBudgetBridge.shiftOverhead p N≤exp (2*P/25)
  pb : (p:ℝ)^2≤exp (P/10)
  ps : 2*(p:ℝ)+3≤exp (P/10)
  h_pos : 0<h
  h_small : h≤(R/2)/400
  h_root : (p:ℝ)*h*(19/20:ℝ)^(h-1)<1/2

theorem eventually_budget {η : ℝ} (hη : 0<η) :
    ∀ᶠ σ : ℝ in atTop,∀ (D : ℝ) (R N : ℕ),Admissible σ η D R → (N:ℝ)≤σ^2 →
      ∃ p h : ℕ,Budget σ (scaleP σ η D R) (Real.toNNReal (scaleL σ η D)) R N p h := by
  filter_upwards [eventually_enumeration_budgets hη,
    eventually_pencil_scalar_budgets hη 400000,eventually_P_le_linear hη (1/12) (by norm_num),
    eventually_uniform_L hη (eventually_ge_atTop (100000000000000:ℝ)),
    eventually_uniform_R hη 400,PlanarLearning.eventually_schedule hη,eventually_ge_atTop (2:ℝ)]
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
  change ∃ p h : ℕ,Budget σ P (Real.toNNReal L) R N p h
  refine ⟨p,h,?_⟩
  constructor
  · exact hσ
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
