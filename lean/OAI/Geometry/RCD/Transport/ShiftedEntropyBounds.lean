import OAI.Geometry.RCD.Coordinates.HeatRegularizedEntropy

namespace OAI

/-! # Finite-range shifted entropy and its affine upper bound -/

open Set Filter MeasureTheory
open scoped NNReal
noncomputable section
namespace RegularPointCoordinates

theorem shiftedEntropy_le_affine {ε A a : ℝ} (hε : 0<ε) (ha : a∈Icc 0 A) :
    shiftedEntropy ε a ≤
      ε*(Real.log (ε+A)-Real.log ε)+(Real.log (ε+A)-Real.log ε-1)*a := by
  have hp : 0<ε+a := add_pos_of_pos_of_nonneg hε ha.1
  have hl := Real.log_le_log hp (add_le_add le_rfl ha.2)
  have hm := mul_le_mul_of_nonneg_left hl hp.le
  unfold shiftedEntropy
  nlinarith only [hm]

variable {X : Type*} [MeasurableSpace X] (μ : Measure X)

theorem shiftedEntropy_memLp {ε : ℝ} (hε : 0<ε) (A : ℝ≥0)
    (f : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, f x∈Icc 0 (A:ℝ)) :
    MemLp (fun x => shiftedEntropy ε (f x)) 2 μ := by
  obtain ⟨Φ,φ,ψ,C,D,M,N,hΦ,_hφ,_hψ,hΦ0,_hφ0,_hdΦ,_hdφ,_hM,_hN,he⟩ :=
    exists_local_smooth_entropy hε A.coe_nonneg
  have hr : (fun x => Φ (f x)) =ᵐ[μ] fun x => shiftedEntropy ε (f x) := by
    filter_upwards [hf] with x hx
    exact (he _ hx).2.2
  exact (memLp_congr_ae ((hΦ.coeFn_compLp hΦ0 f).trans hr)).mp (Lp.memLp _)

theorem shiftedEntropy_weighted_integrable {ε : ℝ} (hε : 0<ε) (A : ℝ≥0)
    (f w : Lp ℝ 2 μ) (hf : ∀ᵐ x ∂μ, f x∈Icc 0 (A:ℝ)) :
    Integrable (fun x => w x*shiftedEntropy ε (f x)) μ :=
  (Lp.memLp w).integrable_mul (shiftedEntropy_memLp μ hε A f hf)

end RegularPointCoordinates

end

end OAI
