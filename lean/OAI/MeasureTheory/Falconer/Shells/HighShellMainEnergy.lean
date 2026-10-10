import OAI.MeasureTheory.Falconer.Shells.HighShellOrderForm
import OAI.MeasureTheory.Falconer.Shells.HighShellRadialBounds
import OAI.MeasureTheory.Falconer.Estimates.FiniteSquareIntegrable

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory Filter
namespace PositiveDistanceData

theorem normalizedHighShellF_shell (d : PositiveDistanceData) [IsFiniteMeasure d.ρ]
    (hQ : 0 < d.Q.side) (hs : d.StronglySeparated) (hsig : 0 ≤ d.sig)
    (hq : 0 < d.q) (hqs : d.sig*d.N ≤ (d.q:ℝ)) (hw : d.a+100*d.q < d.t)
    {v : ℝ} (hv : (d.t:ℝ)-d.sig*d.N ≤ v) (n : ℕ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j ∈ Finset.range (n+1),
      ∀ b ∈ inverseLeibnizTerms j (pairMaskIndices d.inverseDescriptorList), ∀ ξ,
      (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖d.inversePhasedForm b.2 ξ r‖^2) ≤ B) :
    (∫ r in Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)), ‖d.normalizedHighShellF n v r‖^2) ≤
      2*(2:ℝ)^(v-d.a) *
        (∑ j ∈ Finset.range (n+1), spatialLeibnizCost 96 2004 (by norm_num) (by norm_num) j
          (fun k => d.mass k-(k:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t)^2*B := by
  let μ := volume.restrict (Icc ((2:ℝ)^(v-1)) ((2:ℝ)^(v+1)))
  let u := fun j (r : ℝ) => ((((r/(2:ℝ)^v)⁻¹)^j:ℝ):ℂ)
  let F := fun j r => u j r*d.inverseOrderForm j v r
  let w := fun j => spatialLeibnizCost 96 2004 (by norm_num) (by norm_num) j
    (fun k => d.mass k-(k:ℝ)/(d.N:ℝ)) d.N d.q d.a d.t
  have hu (j : ℕ) : Measurable (u j) := by dsimp [u]; fun_prop
  have huw (j : ℕ) : ∀ᵐ r ∂μ, ‖u j r‖ ≤ (2:ℝ)^j := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact high_shell_radial_inverse hr.1 j
  have hwn (j : ℕ) : 0 ≤ w j := by
    apply mul_nonneg (spatialFourierCost_nonneg ..)
    apply mul_nonneg _ (by positivity)
    apply List.sum_nonneg
    intro x hx
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hx
    positivity
  have hm (j : ℕ) : Measurable (F j) := (hu j).mul (d.inverseOrderForm_data hQ j v).1
  have hi (j : ℕ) : Integrable (fun r => ‖F j r‖^2) μ := by
    obtain ⟨hm,C,hC,hCb⟩ := d.inverseOrderForm_data hQ j v
    exact (shell_multiplier_square μ (u j) _ (hu j) hm
      (integrable_norm_square_bounded μ _ hm hC (Eventually.of_forall hCb))
      (by positivity) (huw j)).1
  have hE (j : ℕ) (hj : j ∈ Finset.range (n+1)) :
      (∫ r, ‖F j r‖^2 ∂μ) ≤ (w j)^2*B := by
    obtain ⟨hm,C,hC,hCb⟩ := d.inverseOrderForm_data hQ j v
    have he := (shell_multiplier_square μ (u j) _ (hu j) hm
      (integrable_norm_square_bounded μ _ hm hC (Eventually.of_forall hCb))
      (by positivity) (huw j)).2
    apply he.trans
    apply (mul_le_mul_of_nonneg_left
      (d.inverseOrderForm_shell hQ hsig hq hqs hw hv j μ hB0 (hB j hj))
      (sq_nonneg ((2:ℝ)^j))).trans_eq
    dsimp [w,spatialLeibnizCost,inverseDescriptorList]
    ring
  let G := fun r => ∑ j ∈ Finset.range (n+1), F j r
  have hGm : Measurable G := Finset.measurable_sum _ (fun j _ => hm j)
  have hGi : Integrable (fun r => ‖G r‖^2) μ :=
    finite_sum_square_integrable _ μ F (fun j _ => hm j) (fun j _ => hi j)
  have hGE := finite_weighted_shell_square (Finset.range (n+1)) μ F w
    (fun j _ => hwn j) (fun j _ => hi j) (fun j _ => (hm j).aestronglyMeasurable) hE
  let p := fun r : ℝ => (((r*(2:ℝ)^(-(d.a:ℝ)))^(1/2:ℝ):ℝ):ℂ)
  have hpm : Measurable p := by dsimp [p]; fun_prop
  have hp : ∀ᵐ r ∂μ, ‖p r‖ ≤ Real.sqrt (2*(2:ℝ)^(v-d.a)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with r hr
    exact high_shell_radial_sqrt hr
  have hE' := (shell_multiplier_square μ p G hpm hGm hGi (Real.sqrt_nonneg _) hp).2
  rw [Real.sq_sqrt (by positivity)] at hE'
  have he (r : ℝ) : d.normalizedHighShellF n v r = p r*G r :=
    d.normalizedHighShellF_finite_separation hQ hs n v r
  simp_rw [he]
  exact hE'.trans (by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hGE
      (show 0 ≤ 2*(2:ℝ)^(v-d.a) by positivity))

end PositiveDistanceData

end PlanarFalconer

end OAI
