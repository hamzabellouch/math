import OAI.Geometry.RCD.Heat.CompactEndpointKernelBounds
import OAI.Geometry.RCD.Heat.CompactHeatFactors

namespace OAI

/-! # One Gaussian tail for a compact factor throughout a fixed time window -/

open Set Filter MeasureTheory Metric TopologicalSpace
noncomputable section
namespace RegularPointCoordinates.NoncollapsedRCD
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
  [ProperSpace X] {K : ℝ} {n : ℕ} (hX : NoncollapsedRCD K n X)
  (hn : 2 ≤ n) (p : X) [SeparableSpace X]
  [IsLocallyFiniteMeasure (hausdorff n X)] [(hausdorff n X).Regular]

theorem compact_factor_time_tail {S : Set X} [CompactSpace S]
    (ν : Measure S) [IsProbabilityMeasure ν] (F : C(S,ℝ)) (hF : ∀ y, 0 ≤ F y)
    (z : X) {R a b : ℝ} (hR : 1 ≤ R) (hS : ∀ y : S, dist z y ≤ R)
    (ha : 0 < a) (_hab : a ≤ b) (hb : b ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ) (hat : a ≤ t) (_htb : t ≤ b) (x : X),
      2*R ≤ dist x z →
      hX.compactHeatFactor hn p ν F t (ha.trans_le hat) x ≤
        C*Real.exp (-(dist x z)^2/(20*b)) := by
  obtain ⟨A,B,hA,_hB,hupper⟩ := hX.compact_endpoint_kernel_upper hn p z hR
  let C := A*(Real.sqrt a)⁻¹^n*Real.exp B*(∫ y, F y ∂ν)
  have hmass : 0 ≤ ∫ y, F y ∂ν := integral_nonneg hF
  refine ⟨C,by dsimp only [C]; positivity,?_⟩
  intro t hat htb x hx
  have ht := ha.trans_le hat
  have hsa := Real.sqrt_pos.mpr ha
  have hst := Real.sqrt_pos.mpr ht
  have hinv : (Real.sqrt t)⁻¹ ≤ (Real.sqrt a)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le hsa (Real.sqrt_le_sqrt hat)
  have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hst.le) hinv n
  have htime : (dist x z)^2/(20*b) ≤ (dist x z)^2/(20*t) :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      (mul_le_mul_of_nonneg_left htb (by norm_num))
  have hker (y : S) : hX.canonicalHeatKernel hn p t x y ≤
      A*(Real.sqrt a)⁻¹^n*Real.exp B*Real.exp (-(dist x z)^2/(20*b)) := by
    have hy : dist (y:X) z ≤ R := by simpa only [dist_comm] using hS y
    apply (hupper ht (htb.trans hb) x y hy hx).trans
    calc
      _ ≤ A*(Real.sqrt a)⁻¹^n*Real.exp (-(dist x z)^2/(20*b)+B) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hpow hA.le
        · apply Real.exp_le_exp.mpr
          simp only [neg_div] at *
          linarith
        · exact (Real.exp_pos _).le
        · positivity
      _ = _ := by rw [Real.exp_add]; ring
  have hi : Integrable (fun y : S => hX.canonicalHeatKernel hn p t x y*F y) ν :=
    (((hX.canonicalHeatKernel_continuous_right hn p t ht x).comp continuous_subtype_val).mul
      F.continuous).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hFi : Integrable F ν := F.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hh := integral_mono hi (hFi.const_mul
    (A*(Real.sqrt a)⁻¹^n*Real.exp B*Real.exp (-(dist x z)^2/(20*b))))
    (fun y => mul_le_mul_of_nonneg_right (hker y) (hF y))
  rw [integral_const_mul] at hh
  change (∫ y, hX.canonicalHeatKernel hn p t x y*F y ∂ν) ≤ _
  apply hh.trans_eq
  dsimp only [C]
  ring

end RegularPointCoordinates.NoncollapsedRCD

end

end OAI
