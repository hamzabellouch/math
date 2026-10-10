import Mathlib
import OAI.Analysis.Crouzeix.ExteriorNormal
import OAI.Analysis.Crouzeix.SeparateHolomorphic

namespace OAI

/-! Exterior Kernel. -/

noncomputable section

open Set Filter Metric Topology Function Complex ComplexConjugate MeasureTheory

namespace CrouzeixHilbert.Conformal

namespace ExteriorCollar

variable {U : Set ℂ} (C : ExteriorCollar U)

abbrev reciprocalDisk : Set ℂ := ball 0 C.radius⁻¹

lemma inverse_mem_reciprocalDisk {t : ℂ} (ht : C.radius < ‖t‖) :
    t⁻¹ ∈ C.reciprocalDisk := by
  rw [mem_ball_zero_iff, norm_inv]
  exact (inv_lt_inv₀ (C.radius_pos.trans ht) C.radius_pos).mpr ht

lemma inverse_mem_parameter {u : ℂ} (hu : u ∈ C.reciprocalDisk) (hu0 : u ≠ 0) :
    C.radius < ‖u⁻¹‖ := by
  rw [norm_inv]
  exact (lt_inv_comm₀ C.radius_pos (norm_pos_iff.mpr hu0)).mpr (mem_ball_zero_iff.mp hu)

lemma deriv_laurent {t : ℂ} (ht : C.radius < ‖t‖) :
    deriv C.G t = C.leading - (t⁻¹)^2 * deriv C.regular t⁻¹ := by
  have ht0 : t ≠ 0 := norm_pos_iff.mp (C.radius_pos.trans ht)
  have hd := ((hasDerivAt_id t).const_mul C.leading).add
    ((C.regular_analytic _ (C.inverse_mem_reciprocalDisk ht)).differentiableAt.hasDerivAt.comp t
      (hasDerivAt_inv ht0))
  have he : C.G =ᶠ[𝓝 t] (fun t => C.leading * t + C.regular t⁻¹) := by
    filter_upwards [C.parameter_open.mem_nhds ht] with w hw
    exact C.laurent w hw
  dsimp only [id_eq, Pi.add_apply, comp_apply] at hd
  rw [he.deriv_eq]
  exact hd.deriv.trans (by rw [inv_pow]; ring)

def dividedDenominator (u v : ℂ) : ℂ :=
  C.leading - u * v * dslope C.regular v u

lemma continuousOn_dividedDenominator :
    ContinuousOn (uncurry C.dividedDenominator) (C.reciprocalDisk ×ˢ C.reciprocalDisk) := by
  have hd := continuousOn_dslope_pair isOpen_ball C.regular_analytic.differentiableOn
  apply continuousOn_const.sub
  apply (continuous_fst.mul continuous_snd).continuousOn.mul
  exact hd.comp (f := Prod.swap) continuous_swap.continuousOn (fun _ h => ⟨h.2,h.1⟩)

lemma differentiableOn_dividedDenominator_left {v : ℂ} (hv : v ∈ C.reciprocalDisk) :
    DifferentiableOn ℂ (fun u => C.dividedDenominator u v) C.reciprocalDisk := by
  apply (differentiableOn_const _).sub
  apply (differentiableOn_id.mul_const v).mul
  exact (differentiableOn_dslope (isOpen_ball.mem_nhds hv)).mpr C.regular_analytic.differentiableOn

lemma differentiableOn_dividedDenominator_right {u : ℂ} (hu : u ∈ C.reciprocalDisk) :
    DifferentiableOn ℂ (C.dividedDenominator u) C.reciprocalDisk := by
  have hd : DifferentiableOn ℂ (fun v => dslope C.regular v u) C.reciprocalDisk := by
    exact ((differentiableOn_dslope (isOpen_ball.mem_nhds hu)).mpr
      C.regular_analytic.differentiableOn).congr (fun v _ => dslope_swap C.regular v u)
  exact (differentiableOn_const _).sub ((differentiableOn_id.const_mul u).mul hd)

lemma dividedDenominator_eq {u v : ℂ} (hu : u ∈ C.reciprocalDisk) (hv : v ∈ C.reciprocalDisk)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (huv : u ≠ v) :
    C.dividedDenominator u v = (C.G u⁻¹ - C.G v⁻¹) / (u⁻¹-v⁻¹) := by
  rw [C.laurent _ (C.inverse_mem_parameter hu hu0), C.laurent _ (C.inverse_mem_parameter hv hv0)]
  simp only [dividedDenominator, inv_inv, dslope_of_ne _ huv, slope_def_field]
  field_simp
  ring

lemma dividedDenominator_diag {u : ℂ} (hu : u ∈ C.reciprocalDisk) (hu0 : u ≠ 0) :
    C.dividedDenominator u u = deriv C.G u⁻¹ := by
  rw [C.deriv_laurent (C.inverse_mem_parameter hu hu0), inv_inv]
  simp only [dividedDenominator, dslope_same]
  ring

lemma dividedDenominator_ne_zero {u v : ℂ} (hu : u ∈ C.reciprocalDisk)
    (hv : v ∈ C.reciprocalDisk) : C.dividedDenominator u v ≠ 0 := by
  by_cases hu0 : u = 0
  · simpa only [dividedDenominator, hu0, zero_mul, sub_zero] using C.leading_ne_zero
  by_cases hv0 : v = 0
  · simpa only [dividedDenominator, hv0, mul_zero, zero_mul, sub_zero] using C.leading_ne_zero
  by_cases huv : u = v
  · subst v
    rw [C.dividedDenominator_diag hu hu0]
    exact C.deriv_ne_zero (C.inverse_mem_parameter hu hu0)
  rw [C.dividedDenominator_eq hu hv hu0 hv0 huv]
  apply div_ne_zero
  · intro he
    exact huv (inv_injective (C.injective (C.inverse_mem_parameter hu hu0)
      (C.inverse_mem_parameter hv hv0) (sub_eq_zero.mp he)))
  · exact sub_ne_zero.mpr (fun he => huv (inv_injective he))

def correction (u v : ℂ) : ℂ :=
  -u * deriv (fun z => C.dividedDenominator z v) u / C.dividedDenominator u v

lemma continuousOn_correction :
    ContinuousOn (uncurry C.correction) (C.reciprocalDisk ×ˢ C.reciprocalDisk) := by
  apply ContinuousOn.div
  · apply continuous_fst.neg.continuousOn.mul
    exact continuousOn_first_derivative isOpen_ball isOpen_ball C.continuousOn_dividedDenominator
      (fun _ hv => C.differentiableOn_dividedDenominator_left hv)
  · exact C.continuousOn_dividedDenominator
  · exact fun _ h => C.dividedDenominator_ne_zero h.1 h.2

lemma differentiableOn_correction_left {v : ℂ} (hv : v ∈ C.reciprocalDisk) :
    DifferentiableOn ℂ (fun u => C.correction u v) C.reciprocalDisk :=
  (differentiableOn_id.neg.mul
    ((C.differentiableOn_dividedDenominator_left hv).deriv isOpen_ball)).div
    (C.differentiableOn_dividedDenominator_left hv) (fun _ hu => C.dividedDenominator_ne_zero hu hv)

lemma differentiableOn_correction_right {u : ℂ} (hu : u ∈ C.reciprocalDisk) :
    DifferentiableOn ℂ (C.correction u) C.reciprocalDisk := by
  apply DifferentiableOn.div
  · apply DifferentiableOn.const_mul
    exact differentiableOn_second_first_derivative isOpen_ball isOpen_ball
      C.continuousOn_dividedDenominator
      (fun _ hv => C.differentiableOn_dividedDenominator_left hv)
      (fun _ hu => C.differentiableOn_dividedDenominator_right hu) hu
  · exact C.differentiableOn_dividedDenominator_right hu
  · exact fun _ hv => C.dividedDenominator_ne_zero hu hv

@[simp] lemma correction_zero_left (v : ℂ) : C.correction 0 v = 0 := by
  simp only [correction, neg_zero, zero_mul, zero_div]

@[simp] lemma correction_zero_right (u : ℂ) : C.correction u 0 = 0 := by
  simp only [correction, dividedDenominator, mul_zero, zero_mul, sub_zero,
    deriv_const, mul_zero, zero_div]

lemma correction_eq {t w : ℂ} (ht : C.radius < ‖t‖) (hw : C.radius < ‖w‖)
    (htw : t ≠ w) :
    C.correction t⁻¹ w⁻¹ = t * deriv C.G t / (C.G t - C.G w) - t / (t-w) := by
  have ht0 : t ≠ 0 := norm_pos_iff.mp (C.radius_pos.trans ht)
  have hw0 : w ≠ 0 := norm_pos_iff.mp (C.radius_pos.trans hw)
  have hg : C.G t - C.G w ≠ 0 := sub_ne_zero.mpr (fun he => htw (C.injective ht hw he))
  have htw' : t-w ≠ 0 := sub_ne_zero.mpr htw
  have hQ := C.dividedDenominator_eq (C.inverse_mem_reciprocalDisk ht)
    (C.inverse_mem_reciprocalDisk hw) (inv_ne_zero ht0) (inv_ne_zero hw0)
    (fun he => htw (inv_injective he))
  simp only [inv_inv] at hQ
  have hdQ := ((C.differentiableOn_dividedDenominator_left
    (C.inverse_mem_reciprocalDisk hw)).differentiableAt
      (isOpen_ball.mem_nhds (C.inverse_mem_reciprocalDisk ht))).hasDerivAt.comp t
        (hasDerivAt_inv ht0)
  have hdG := ((C.analytic t ht).differentiableAt.hasDerivAt.sub_const (C.G w)).div
    ((hasDerivAt_id t).sub_const w) htw'
  have he : (fun z => C.dividedDenominator z⁻¹ w⁻¹) =ᶠ[𝓝 t]
      (fun z => (C.G z - C.G w)/(z-w)) := by
    filter_upwards [C.parameter_open.mem_nhds ht, eventually_ne_nhds htw] with z hz hzw
    have hz0 : z ≠ 0 := norm_pos_iff.mp (C.radius_pos.trans hz)
    simpa only [inv_inv] using C.dividedDenominator_eq (C.inverse_mem_reciprocalDisk hz)
      (C.inverse_mem_reciprocalDisk hw) (inv_ne_zero hz0) (inv_ne_zero hw0)
      (fun he => hzw (inv_injective he))
  dsimp only [Function.comp_apply, id_eq] at hdQ hdG
  have hd := (hdQ.congr_of_eventuallyEq he.symm).unique hdG
  dsimp only [correction]
  rw [hQ]
  field_simp at hd ⊢
  exact hd

end ExteriorCollar

end CrouzeixHilbert.Conformal

end

end OAI
