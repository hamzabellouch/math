import Mathlib
import OAI.Analysis.CoulombIonization.Localization.CoreHistoryAverageBarrier
import OAI.Analysis.CoulombIonization.RadialBounds.dShellForm
import OAI.Analysis.CoulombIonization.RadialBounds.ShellBias

namespace OAI

open MeasureTheory Filter
open scoped BigOperators InnerProductSpace
noncomputable section
namespace CoulombAtom
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph
  FermionMultiplier.apply FermionLipschitzMultiplier.apply oneBodySquareTotal
  formEnergy energy sectorExcessOperator fermionGraphValue shellBiasMultiplier

lemma shellBias_double_apply {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (F : fermionGraph N) :
    (shellBiasMultiplier p hc).apply ((shellBiasMultiplier p hc).apply F) = (oneBodySquareTotal p).apply F := by
  apply graph_value_components_ext
  intro s
  apply Lp.ext
  filter_upwards [(shellBiasMultiplier p hc).apply_value ((shellBiasMultiplier p hc).apply F) s,
    (shellBiasMultiplier p hc).apply_value F s,(oneBodySquareTotal p).apply_value F s] with x h1 h2 h3
  have hsq : ((shellBiasMultiplier p hc).value x : ℂ) *
      ((shellBiasMultiplier p hc).value x : ℂ) = ((oneBodySquareTotal p).value x : ℂ) := by
    rw [←sq,←Complex.ofReal_pow,shellBias_value_sq p hc x]
  calc
    _ = ((shellBiasMultiplier p hc).value x : ℂ) *
        (((shellBiasMultiplier p hc).value x : ℂ) * graphComponent s none F x) :=
      h1.trans (congrArg (fun z : ℂ => ((shellBiasMultiplier p hc).value x : ℂ)*z) h2)
    _ = ((oneBodySquareTotal p).value x : ℂ)*graphComponent s none F x := by rw [←mul_assoc,hsq]
    _ = _ := h3.symm

lemma rawFormPair_shellBias {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (F : fermionGraph N) (f : Configuration N → ℝ) :
    rawFormPair (graphFormVector ((shellBiasMultiplier p hc).apply F)) f =
      rawFormPair (graphFormVector F) (fun x => f x*(oneBodySquareTotal p).value x) := by
  unfold rawFormPair
  apply Finset.sum_congr rfl
  intro s _
  apply integral_congr_ae
  filter_upwards [(shellBiasMultiplier p hc).apply_value F s] with x hx
  simp only [graphFormVector_value_eq,hx,scaled_norm_sq,shellBias_value_sq,mul_assoc]

lemma formMass_shellBias {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (F : fermionGraph N) :
    formMass (graphFormVector ((shellBiasMultiplier p hc).apply F)) =
      weightedMass F (oneBodySquareTotal p).value := by
  have hh := rawFormPair_shellBias p hc F (fun _ => 1)
  simpa only [rawFormPair,one_mul,formMass,weightedMass,graphFormVector_value_eq] using hh

lemma oneBody_deriv_integrable {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (F : fermionGraph N) (s : Spins N) (i : Fin N) (a : Fin 3) :
    Integrable (fun x => (lineDeriv ℝ p.value (x i) (spaceDirections a))^2 * ‖graphComponent s none F x‖^2) := by
  obtain ⟨C,hC⟩ := p.gradient_bound a
  have hd : Continuous (fun x : Configuration N => lineDeriv ℝ p.value (x i) (spaceDirections a)) :=
    (smooth_lineDeriv_continuous p.regular (spaceDirections a)).comp (continuous_apply i)
  apply (Lp.memLp (graphComponent s none F)).norm.integrable_sq.bdd_mul (c := C^2) (hd.pow 2).aestronglyMeasurable
  apply ae_of_all
  intro x
  change ‖(lineDeriv ℝ p.value (x i) (spaceDirections a))^2‖ ≤ C^2
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hC (x i)) 2

lemma shellBias_gradient_le {N : ℕ} (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (F : fermionGraph N) :
    (∑ s : Spins N, ∑ i : Fin N, ∑ a : Fin 3,
        ∫ x, (lineDeriv ℝ (shellBiasMultiplier p hc).value x (direction i a))^2 *
          ‖graphComponent s none F x‖^2) ≤ oneBodyGradientError p F := by
  unfold oneBodyGradientError
  apply Finset.sum_le_sum
  intro s _
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro a _
  have hh := oneBody_deriv_integrable p F s i a
  have hn (x : Configuration N) : 0 ≤ (lineDeriv ℝ (shellBiasMultiplier p hc).value x (direction i a))^2 *
          ‖graphComponent s none F x‖^2 := by positivity
  have hb (x : Configuration N) := mul_le_mul_of_nonneg_right (shellBias_deriv_sq_le p hc x i a)
    (sq_nonneg ‖graphComponent s none F x‖)
  have hm := ((aestronglyMeasurable_lineDeriv (𝕜 := ℝ) (v := direction i a) (shellBiasMultiplier p hc).lipschitz.continuous volume).pow 2).mul
    ((Lp.memLp (graphComponent s none F)).aestronglyMeasurable.norm.pow 2)
  apply integral_mono (hh.mono' hm (ae_of_all _ (fun x => by change ‖(lineDeriv ℝ (shellBiasMultiplier p hc).value x (direction i a))^2 * ‖graphComponent s none F x‖^2‖ ≤ _; rw [Real.norm_of_nonneg (hn x)]; exact hb x))) hh
  exact hb

lemma shellBias_price_excess_le {Z lam : ℝ} {N : ℕ}
    (hN : PriceMinimizes (energy Z) lam N) (p : SmoothMultiplier spaceDirections)
    (hc : HasCompactSupport p.value) (F : fermionGraph N) :
    corePriceExcess Z lam (graphFormVector ((shellBiasMultiplier p hc).apply F)) ≤
      (1/2:ℝ)*oneBodyGradientError p F+
        (⟪(oneBodySquareTotal p).apply F,sectorExcessOperator Z N F⟫_ℂ).re := by
  have hh := quantum_lipschitz_ims_residual Z F (shellBiasMultiplier p hc)
  have hpair := congrArg (fun T : fermionGraph N => (⟪T,sectorExcessOperator Z N F⟫_ℂ).re)
    (shellBias_double_apply p hc F)
  have hmass := formMass_graph ((shellBiasMultiplier p hc).apply F)
  dsimp only [corePriceExcess]
  have hprice := priceEnergy_eq_of_minimizes hN
  have hg := shellBias_gradient_le p hc F
  have hpr := congrArg (fun t : ℝ => t*formMass (graphFormVector ((shellBiasMultiplier p hc).apply F))) hprice
  have hmul := congrArg (fun t : ℝ => energy Z N*t) hmass
  nlinarith only [hh,hg,hpair,hpr,hmul]

lemma corePriceExcess_scale {N : ℕ} (Z lam c : ℝ) (psi : FormVector N) :
    corePriceExcess Z lam (scaleForm c psi) = c^2*corePriceExcess Z lam psi := by
  unfold corePriceExcess
  rw [formEnergy_scale,formMass_scale]
  ring
lemma rawFormPair_scale {N : ℕ} (c : ℝ) (psi : FormVector N) (f : Configuration N → ℝ) :
    rawFormPair (scaleForm c psi) f = c^2*rawFormPair psi f := by
  unfold rawFormPair
  simp only [scaleForm,scaled_norm_sq,mul_left_comm _ (c^2),integral_const_mul,Finset.mul_sum]

end CoulombAtom

end

end OAI
