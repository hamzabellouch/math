import OAI.Geometry.RCD.Transport.LocalSmoothEntropy
import OAI.Geometry.RCD.Heat.HeatNonlinearPairingDerivative

namespace OAI

/-! # Exact regularized entropy differentiation for the actual heat paths -/

open Set Filter MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace RegularPointCoordinates

def shiftedEntropy (ε a : ℝ) : ℝ :=
  (ε+a)*(Real.log (ε+a)-Real.log ε)-a

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] (μ : Measure X) [μ.Regular] (hQ : QuadraticCheegerEnergy μ)

theorem heat_shiftedEntropy_hasDerivAt {ε : ℝ} (hε : 0<ε)
    (f w : Lp ℝ 2 μ) (hf0 : 0≤f) (A B : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |f x|≤A) (hw : ∀ᵐ x ∂μ, |w x|≤B)
    {T t : ℝ} (ht : 0<t) (htT : t<T) (L : ℝ≥0)
    (hL : ∀ᵐ x ∂μ, SobolevSpace.minimalSlope μ hQ
      (heatSobolev μ hQ (T-t) (sub_pos.mpr htT) f) x≤L) :
    HasDerivAt (fun s => ∫ x, heatAt μ hQ s w x *
      shiftedEntropy ε (heatAt μ hQ (T-s) f x) ∂μ)
      (∫ x, heatAt μ hQ t w x *
        (localGamma μ hQ (heatSobolev μ hQ (T-t) (sub_pos.mpr htT) f)
          (heatSobolev μ hQ (T-t) (sub_pos.mpr htT) f) x /
          (ε+heatAt μ hQ (T-t) f x)) ∂μ) t := by
  obtain ⟨Φ,φ,ψ,C,D,M,N,hΦ,hφ,hψ,hΦ0,hφ0,hdΦ,hdφ,hM,hN,he⟩ :=
    exists_local_smooth_entropy hε A.coe_nonneg
  have hval (s : ℝ) : ∀ᵐ x ∂μ, heatAt μ hQ (T-s) f x ∈ Icc 0 (A:ℝ) := by
    filter_upwards [(Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ (T-s) f hf0),
      heatAt_abs_le_const μ hQ (T-s) A f hf] with x hx hb
    exact ⟨hx,(le_abs_self _).trans hb⟩
  have hp (s : ℝ) : inner ℝ (heatAt μ hQ s w) (hΦ.compLp hΦ0 (heatAt μ hQ (T-s) f)) =
      ∫ x, heatAt μ hQ s w x * shiftedEntropy ε (heatAt μ hQ (T-s) f x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hΦ.coeFn_compLp hΦ0 (heatAt μ hQ (T-s) f),hval s] with x hx hv
    simp only [Real.inner_apply,Function.comp_apply,hx, (he _ hv).2.2,shiftedEntropy]
  have hh := heat_nonlinear_pairing_hasDerivAt μ hQ hΦ hΦ0 hφ hφ0 hψ hdΦ hdφ
    M N hM hN f w B hw ht htT L hL
  simp_rw [hp] at hh
  have heq : (∫ x, heatAt μ hQ t w x * (ψ (heatAt μ hQ (T-t) f x) *
      localGamma μ hQ (heatSobolev μ hQ (T-t) (sub_pos.mpr htT) f)
        (heatSobolev μ hQ (T-t) (sub_pos.mpr htT) f) x) ∂μ) =
      ∫ x, heatAt μ hQ t w x *
        (localGamma μ hQ (heatSobolev μ hQ (T-t) (sub_pos.mpr htT) f)
          (heatSobolev μ hQ (T-t) (sub_pos.mpr htT) f) x /
          (ε+heatAt μ hQ (T-t) f x)) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hval t] with x hx
    rw [(he _ hx).1,div_eq_mul_inv]
    ring
  rwa [heq] at hh

theorem heat_shiftedEntropy_continuous {ε : ℝ} (hε : 0<ε)
    (f w : Lp ℝ 2 μ) (hf0 : 0≤f) (A : ℝ≥0)
    (hf : ∀ᵐ x ∂μ, |f x|≤A) (T : ℝ) :
    Continuous (fun s => ∫ x, heatAt μ hQ s w x *
      shiftedEntropy ε (heatAt μ hQ (T-s) f x) ∂μ) := by
  obtain ⟨Φ,φ,ψ,C,D,M,N,hΦ,hφ,hψ,hΦ0,hφ0,hdΦ,hdφ,hM,hN,he⟩ :=
    exists_local_smooth_entropy hε A.coe_nonneg
  have hp (s : ℝ) : (∫ x, heatAt μ hQ s w x *
      shiftedEntropy ε (heatAt μ hQ (T-s) f x) ∂μ) =
      inner ℝ (heatAt μ hQ s w) (hΦ.compLp hΦ0 (heatAt μ hQ (T-s) f)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hΦ.coeFn_compLp hΦ0 (heatAt μ hQ (T-s) f),
      (Lp.coeFn_nonneg _).mpr (heatAt_nonneg μ hQ (T-s) f hf0),
      heatAt_abs_le_const μ hQ (T-s) A f hf] with x hx hn hb
    have hv : heatAt μ hQ (T-s) f x ∈ Icc 0 (A:ℝ) := ⟨hn,(le_abs_self _).trans hb⟩
    simp only [Real.inner_apply,Function.comp_apply,hx,(he _ hv).2.2,shiftedEntropy]
  simp_rw [hp]
  exact (heatAt_continuous μ hQ w).inner
    ((hΦ.continuous_compLp hΦ0).comp ((heatAt_continuous μ hQ f).comp (continuous_const.sub continuous_id)))

end RegularPointCoordinates

end

end OAI
