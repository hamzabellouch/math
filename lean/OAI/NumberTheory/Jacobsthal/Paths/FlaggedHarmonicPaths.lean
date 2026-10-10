import OAI.NumberTheory.Jacobsthal.Probability.HighPrefixKernel
import OAI.NumberTheory.Jacobsthal.Sieve.AdmittedExponentMarginal

namespace OAI

namespace Erdos970

section

namespace NumberTheoryLean.FlaggedHarmonicPaths

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open FinitePathMeasures PairedCostGrouping ArrivalKernelGeometry
open AdmittedHarmonicPaths AdmittedExponentMarginal RegeneratingInverseBands

abbrev FlagState := CostState × Bool
abbrev ExponentState := ErdosPrimeInputs.HighPrefixState.State

noncomputable def flagUpdate (S : ℝ) (b : Bool) (y : CostState) : FlagState :=
  (y, if b = true ∨ S < stateRatio y.1 then true else false)

theorem flagUpdate_joint_measurable (S : ℝ) :
    Measurable (fun p : FlagState × CostState => flagUpdate S p.1.2 p.2) := by
  have hb : Measurable (fun p : FlagState × CostState => p.1.2) := by fun_prop
  have hr : Measurable (fun p : FlagState × CostState => stateRatio p.2.1) := stateRatio_measurable.comp (measurable_fst.comp measurable_snd)
  exact measurable_snd.prodMk (Measurable.ite
    ((hb (measurableSet_singleton true)).union (measurableSet_lt measurable_const hr))
    measurable_const measurable_const)

theorem flagUpdate_measurable (S : ℝ) (b : Bool) : Measurable (flagUpdate S b) := by
  have hr : Measurable (fun y : CostState => stateRatio y.1) := stateRatio_measurable.comp measurable_fst
  have hb : Measurable (fun _ : CostState => b) := measurable_const
  exact measurable_id.prodMk (Measurable.ite
    ((hb (measurableSet_singleton true)).union (measurableSet_lt measurable_const hr))
    measurable_const measurable_const)

noncomputable def kernel (v ell S : ℝ) : Kernel FlagState FlagState :=
  ((Kernel.id : Kernel FlagState FlagState).prod
    ((admittedHarmonic v ell).comap (fun z : FlagState => z.1) measurable_fst)).map
      (fun p => flagUpdate S p.1.2 p.2)

instance kernel_isSFinite (v ell S : ℝ) : IsSFiniteKernel (kernel v ell S) := by
  unfold kernel
  infer_instance

theorem kernel_eq_map (v ell S : ℝ) (z : FlagState) :
    kernel v ell S z = (admittedHarmonic v ell z.1).map (flagUpdate S z.2) := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [kernel, Kernel.map_apply _ (flagUpdate_joint_measurable S),
    lintegral_map hf (flagUpdate_joint_measurable S)]
  calc
    _ = ∫⁻ y, f (flagUpdate S z.2 y) ∂admittedHarmonic v ell z.1 :=
      Kernel.lintegral_id_prod (f := fun p : FlagState × CostState => f (flagUpdate S p.1.2 p.2))
        (hf.comp (flagUpdate_joint_measurable S)) _ z
    _ = _ := (lintegral_map hf (flagUpdate_measurable S z.2)).symm

theorem kernel_map_state (v ell S : ℝ) (z : FlagState) :
    (kernel v ell S z).map Prod.fst = admittedHarmonic v ell z.1 := by
  rw [kernel_eq_map, Measure.map_map measurable_fst (flagUpdate_measurable S z.2)]
  change (admittedHarmonic v ell z.1).map id = _
  exact Measure.map_id

noncomputable def coordinates (v : ℝ) (z : FlagState) : ExponentState :=
  (currentExponent v z.1, gapValue v z.1, z.2)

theorem coordinates_measurable (v : ℝ) : Measurable (coordinates v) :=
  ((currentExponent_measurable v).comp measurable_fst).prodMk
    (((gapValue_measurable v).comp measurable_fst).prodMk measurable_snd)

noncomputable def initial (S : ℝ) (z : CostState) : FlagState :=
  (z, if S < stateRatio z.1 then true else false)

theorem gap_div_currentExponent (v : ℝ) (z : CostState) :
    gapValue v z / currentExponent v z = stateRatio z.1 := by
  unfold currentExponent
  have hr : gapValue v z ≠ 0 := (Real.exp_pos _).ne'
  field_simp

theorem initial_coordinates (v S : ℝ) (z : CostState) :
    coordinates v (initial S z) = ErdosPrimeInputs.HighPrefixState.initial S
      (currentExponent v z) (gapValue v z) := by
  simp only [coordinates, initial, ErdosPrimeInputs.HighPrefixState.initial, gap_div_currentExponent]

theorem coordinates_update (v S : ℝ) (z : FlagState) (y : CostState)
    (hflow : gapValue v z.1 = gapValue v y + currentExponent v y) :
    coordinates v (flagUpdate S z.2 y) =
      ErdosPrimeInputs.HighPrefixState.update S (coordinates v z) (currentExponent v y) := by
  have hrem : gapValue v z.1 - currentExponent v y = gapValue v y := by linarith
  have hratio : (gapValue v z.1 - currentExponent v y) / currentExponent v y = stateRatio y.1 := by
    rw [hrem, gap_div_currentExponent]
  simp only [coordinates, flagUpdate, ErdosPrimeInputs.HighPrefixState.update, hrem]
  rw [gap_div_currentExponent]

theorem kernel_map_coordinates (v ell S : ℝ) (z : FlagState) :
    (kernel v ell S z).map (coordinates v) =
      ((admittedHarmonic v ell z.1).map (currentExponent v)).map
        (ErdosPrimeInputs.HighPrefixState.update S (coordinates v z)) := by
  rw [kernel_eq_map, Measure.map_map (coordinates_measurable v) (flagUpdate_measurable S z.2),
    Measure.map_map (ErdosPrimeInputs.HighPrefixKernel.update_at_measurable S (coordinates v z))
      (currentExponent_measurable v)]
  apply Measure.map_congr
  have hflow : ∀ᵐ y ∂admittedHarmonic v ell z.1,
      gapValue v z.1 = gapValue v y + currentExponent v y := by
    rw [admittedHarmonic, Kernel.restrict_apply]
    exact ae_restrict_of_ae (harmonicKernel_gap_flow v z.1)
  filter_upwards [hflow] with y hy
  exact coordinates_update v S z y hy

theorem kernel_map_coordinates_le (v S : ℝ) {ell : ℝ} (hell : 0 ≤ ell) (z : FlagState) :
    (kernel v ell S z).map (coordinates v) ≤
      ErdosPrimeInputs.HighPrefixKernel.kernel ell S (coordinates v z) := by
  rw [kernel_map_coordinates, ErdosPrimeInputs.HighPrefixKernel.kernel_eq_map]
  exact Measure.map_mono (admitted_exponent_marginal_le v hell z.1)
    (ErdosPrimeInputs.HighPrefixKernel.update_at_measurable S (coordinates v z))

end NumberTheoryLean.FlaggedHarmonicPaths

end

end Erdos970

end OAI
