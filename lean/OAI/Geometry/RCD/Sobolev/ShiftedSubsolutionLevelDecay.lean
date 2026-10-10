import OAI.Geometry.RCD.Sobolev.SubsolutionLevelStep
import OAI.Geometry.RCD.Sobolev.ShiftedDyadicSubsolutionLevels

namespace OAI

/-! # Decay above a prescribed level for bounded-potential subsolutions -/

open Set Metric Filter MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace RegularPointCoordinates

variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [ProperSpace X]

theorem NoncollapsedRCD.subsolution_shifted_level_energies_tendsto_zero {K : ℝ} {n : ℕ}
    (hX : NoncollapsedRCD K n X) (hn : 2 ≤ n) (Λ H : ℝ) (hΛ : 0 ≤ Λ) (hH : 0≤H) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (x : X) (R : ℝ), 0 < R → -1 ≤ K*R^2 →
      ∀ (u : SobolevSpace (hausdorff n X) hX.quadratic) (a : ℝ), 0 ≤ a → a*R^2 ≤ Λ →
      IsWeakSubsolutionOn (hausdorff n X) hX.quadratic (ball x R) u a →
      (∫ y in ball x R, (max (SobolevSpace.toLp (hausdorff n X) hX.quadratic u y-H) 0)^2
        ∂hausdorff n X) ≤ δ*(hausdorff n X).real (ball x R) →
      Tendsto (fun i : ℕ => ∫ y in closedBall x (R/2+R/(4*2^i)),
        (max (SobolevSpace.toLp (hausdorff n X) hX.quadratic u y-((H+1)-(2^i:ℝ)⁻¹)) 0)^2
          ∂hausdorff n X) atTop (𝓝 0) := by
  obtain ⟨p,C,hp,hC,hstep⟩ := hX.subsolution_level_step hn
  have hp0 : 0 < p := by linarith
  let α := 1-2/p
  have hα : 0 < α := by
    have hh : 2/p < 1 := (div_lt_one hp0).mpr hp
    dsimp only [α]
    linarith
  let C₀ := C*(641+16*Λ*(H+1))*(16:ℝ)^α
  let b := (4:ℝ)^(1+α)
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  have hb : 0 < b := by dsimp only [b]; positivity
  obtain ⟨δ,hδ,hdecay⟩ := exists_superlinear_decay_threshold hC₀ hb hα
  refine ⟨δ,hδ,?_⟩
  intro x R hR hcurv u a ha haR hu hsmall
  let μ := hausdorff n X
  let V := μ.real (ball x R)
  let U := SobolevSpace.toLp μ hX.quadratic u
  let J (i : ℕ) := ∫ y in closedBall x (R/2+R/(4*2^i)),
    (max (U y-((H+1)-(2^i:ℝ)⁻¹)) 0)^2 ∂μ
  let Y (i : ℕ) := J i/V
  have hV : 0 < V := ENNReal.toReal_pos (hX.fullSupport x R hR).ne'
    (hX.finiteOnBounded _ isBounded_ball).ne
  have hJ (i : ℕ) : 0 ≤ J i := integral_nonneg fun _ => sq_nonneg _
  have hY (i : ℕ) : 0 ≤ Y i := div_nonneg (hJ i) hV.le
  have hstart : Y 0 ≤ δ := by
    have hsub : closedBall x (R/2+R/(4*2^0)) ⊆ ball x R :=
      closedBall_subset_ball (dyadic_inner_radii hR 0).2.2
    have hi : Integrable (fun y => (max (U y-H) 0)^2) μ :=
      ((upperLevelPart_lipschitz H).comp_memLp (upperLevelPart_zero hH) (Lp.memLp U)).integrable_sq
    have hJ0 : J 0 ≤ ∫ y in ball x R, (max (U y-H) 0)^2 ∂μ := by
      dsimp only [J]
      simp only [pow_zero,inv_one,add_sub_cancel_right]
      exact setIntegral_mono_set hi.restrict
        (Eventually.of_forall fun y => sq_nonneg _) (Eventually.of_forall hsub)
    exact (div_le_iff₀ hV).mpr (hJ0.trans hsmall)
  have hrec (i : ℕ) : Y (i+1) ≤ C₀*b^i*(Y i)^(1+α) := by
    have hr := dyadic_inner_radii hR i
    have hk := dyadic_level_gap_bounds hR i
    have hm := shifted_dyadic_middle_level_bounds hR hH i
    let j := (H+1)-(2^i:ℝ)⁻¹
    let h := (H+1)-(2^(i+1):ℝ)⁻¹
    let k := (j+h)/2
    have hjk : j < k := hm.2.1
    have hkh : k < h := hm.2.2.1
    have hh := hstep x R hR hcurv u a ha hu
      (R/2+R/(4*2^(i+1))) (R/2+R/(4*2^i)) j k h hr.1 hr.2.1 hr.2.2 hm.1 hjk hkh
    change J (i+1) ≤ C*V^(2/p-1)*
      (10*R^2*(((R/2+R/(4*2^i))-(R/2+R/(4*2^(i+1))))⁻¹)^2+
        4*R^2*a*(k/(k-j))+1)*J i*(J i/(h-k)^2)^(1-2/p) at hh
    have hgap : J i/(h-k)^2 = (16*4^i)*J i := by
      rw [div_eq_mul_inv,← inv_pow,hm.2.2.2.1]
      ring
    have hpot : 4*R^2*a*(k/(k-j)) ≤ (16*Λ*(H+1))*4^i := by
      calc
        _ = 4*(a*R^2)*(k/(k-j)) := by ring
        _ ≤ 4*Λ*((H+1)*4*4^i) := by
          have hk0 : 0 ≤ k := hm.1.trans hjk.le
          have hh := mul_le_mul haR hm.2.2.2.2
            (div_nonneg hk0 (sub_pos.mpr hjk).le) hΛ
          nlinarith only [hh]
        _ = _ := by ring
    have hcoeff : 10*R^2*(((R/2+R/(4*2^i))-(R/2+R/(4*2^(i+1))))⁻¹)^2+
        4*R^2*a*(k/(k-j))+1 ≤ (641+16*Λ*(H+1))*4^i := by
      nlinarith only [hk.2.2.2,hpot]
    have hexp : 2/p-1 = -α := by dsimp only [α]; ring
    rw [hgap,hexp] at hh
    have hbnd : J (i+1) ≤ C*V^(-α)*((641+16*Λ*(H+1))*4^i)*J i*((16*4^i)*J i)^α := by
      apply hh.trans
      gcongr
    have hnorm := div_le_div_of_nonneg_right hbnd hV.le
    rw [normalized_level_identity hV (hJ i) (by norm_num : (0:ℝ)<16)
      (by norm_num : (0:ℝ)<4) hα i] at hnorm
    exact hnorm
  have hlim := hdecay Y hY hstart hrec
  have hJlim := hlim.mul_const V
  have heq (i : ℕ) : Y i*V = J i := div_mul_cancel₀ _ hV.ne'
  simpa only [heq,zero_mul] using hJlim

end RegularPointCoordinates

end

end OAI
