import Mathlib
import OAI.Geometry.WeakHessian.HeatFlow.FormGeneratorSymmetric

namespace OAI

open Set Filter MeasureTheory
open scoped ENNReal NNReal Topology

section InlinedFile157
noncomputable section
namespace WeakHessianFunctional
open Set Filter
open scoped Topology ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {Q : E → ℝ≥0∞} (hQ : ClosedQuadraticEnergy Q)

lemma ClosedQuadraticEnergy.finite_energy_of_generator_pairing
    (hd : hQ.domain.topologicalClosure = ⊤) (f : E) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u A : E,hQ.IsFormGenerator u A →
      |⟪f,A⟫_ℝ| ≤ C*(‖u‖+Real.sqrt (2*(Q u).toReal))) : Q f < ∞ := by
  let t (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  have ht (n : ℕ) : 0 < t n := by dsimp [t]; positivity
  let us (n : ℕ) := (hQ.scale (ht n)).resolvent f
  let As (n : ℕ) := (t n)⁻¹ • (us n-f)
  have hg (n : ℕ) : hQ.IsFormGenerator (us n) (As n) :=
    (hQ.scaled_resolvent_iff (ht n) f (us n)).mp rfl
  have hE (n : ℕ) : 2*(Q (us n)).toReal ≤ -⟪f,As n⟫_ℝ := by
    have he := hQ.formGenerator_energy (hg n)
    have hf : f=us n-t n • As n := by
      dsimp [As]
      rw [smul_smul,mul_inv_cancel₀ (ht n).ne',one_smul,sub_sub_cancel]
    calc
      2*(Q (us n)).toReal = -⟪us n,As n⟫_ℝ := by simpa only [real_inner_comm] using he
      _ ≤ -⟪us n,As n⟫_ℝ+t n*‖As n‖^2 := le_add_of_nonneg_right (mul_nonneg (ht n).le (sq_nonneg _))
      _ = -⟪f,As n⟫_ℝ := by rw [hf,inner_sub_left,real_inner_smul_left,real_inner_self_eq_norm_sq]; ring
  have hbound (n : ℕ) : (Q (us n)).toReal ≤ C*‖f‖+C^2 := by
    have hn : ‖us n‖ ≤ ‖f‖ := by
      simpa only [(hQ.scale (ht n)).resolvent_zero,sub_zero] using (hQ.scale (ht n)).resolvent_nonexpansive f 0
    have hh := (hE n).trans ((neg_le_abs _).trans ((hb _ _ (hg n)).trans
      (mul_le_mul_of_nonneg_left (add_le_add hn le_rfl) hC)))
    have hs := Real.sq_sqrt (show 0 ≤ 2*(Q (us n)).toReal by positivity)
    have hp := sq_nonneg (Real.sqrt (2*(Q (us n)).toReal)-C)
    nlinarith only [hh,hs,hp,sq_nonneg C]
  have hbound' (n : ℕ) : Q (us n) ≤ ENNReal.ofReal (C*‖f‖+C^2) := by
    apply (ENNReal.toReal_le_toReal (hg n).1.ne ENNReal.ofReal_ne_top).mp
    rw [ENNReal.toReal_ofReal (by positivity)]
    exact hbound n
  have hT : Tendsto us atTop (𝓝 f) := hQ.scaled_resolvent_tendsto hd ht tendsto_one_div_add_atTop_nhds_zero_nat f
  have H : Q f ≤ ENNReal.ofReal (C*‖f‖+C^2) :=
    hQ.lowerSemicontinuous.isClosed_epigraph.mem_of_tendsto (hT.prodMk_nhds tendsto_const_nhds)
      (Eventually.of_forall hbound')
  exact H.trans_lt ENNReal.ofReal_lt_top
end WeakHessianFunctional

end
end InlinedFile157

end OAI
