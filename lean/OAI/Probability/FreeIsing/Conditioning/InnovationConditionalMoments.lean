import OAI.Probability.FreeIsing.Brownian.Observation

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Problem367.InnovationConditionalMoments

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}

theorem integral_abs_condExp_sub_const_le [IsFiniteMeasure P]
    {m : MeasurableSpace Ω} {X Y : Ω → ℝ} {c : ℝ}
    (hX : Integrable X P) (hY : Integrable Y P)
    (hmean : P[Y | m] =ᵐ[P] fun _ => c) :
    (∫ ω, |P[X | m] ω - c| ∂P) ≤ ∫ ω, |X ω - Y ω| ∂P := by
  have heq : (fun ω => P[X | m] ω - c) =ᵐ[P] P[X - Y | m] := by
    filter_upwards [condExp_sub hX hY m, hmean] with ω hsub hy
    simpa only [Pi.sub_apply, hy] using hsub.symm
  calc
    (∫ ω, |P[X | m] ω - c| ∂P) = ∫ ω, |P[X - Y | m] ω| ∂P :=
      integral_congr_ae (heq.fun_comp abs)
    _ ≤ ∫ ω, |X ω - Y ω| ∂P := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using
        (integral_norm_condExp_le (μ := P) (m := m) (X - Y))

theorem integral_smul_eq_integral_condExp_smul [IsFiniteMeasure P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : Integrable f P)
    {Z : Ω → E} (hZ : StronglyMeasurable[m] Z) {C : ℝ}
    (hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) :
    (∫ ω, f ω • Z ω ∂P) = ∫ ω, P[f | m] ω • Z ω ∂P := by
  have hprod : Integrable (f • Z) P :=
    hf.smul_bdd C (hZ.mono hm).aestronglyMeasurable hbound
  calc
    (∫ ω, f ω • Z ω ∂P) = ∫ ω, P[f • Z | m] ω ∂P :=
      (integral_condExp hm).symm
    _ = ∫ ω, P[f | m] ω • Z ω ∂P :=
      integral_congr_ae
        (condExp_smul_of_aestronglyMeasurable_right hf hprod hZ.aestronglyMeasurable)

theorem norm_integral_smul_le_conditional_abs [IsFiniteMeasure P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {f : Ω → ℝ} (hf : Integrable f P)
    {Z : Ω → E} (hZ : StronglyMeasurable[m] Z) {C : ℝ}
    (hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) :
    ‖∫ ω, f ω • Z ω ∂P‖ ≤ C * ∫ ω, |P[f | m] ω| ∂P := by
  rw [integral_smul_eq_integral_condExp_smul (mΩ := mΩ) hm hf hZ hbound]
  calc
    ‖∫ ω, P[f | m] ω • Z ω ∂P‖ ≤ ∫ ω, C * |P[f | m] ω| ∂P := by
      apply norm_integral_le_of_norm_le (integrable_condExp.abs.const_mul C)
      filter_upwards [hbound] with ω hω
      rw [norm_smul, Real.norm_eq_abs]
      nlinarith [abs_nonneg (P[f | m] ω)]
    _ = C * ∫ ω, |P[f | m] ω| ∂P := integral_const_mul _ _

theorem norm_integral_test_sub_const_le [IsFiniteMeasure P]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {m : MeasurableSpace Ω} (hm : m ≤ mΩ) {X Y : Ω → ℝ} {c : ℝ}
    (hX : Integrable X P) (hY : Integrable Y P)
    (hmean : P[Y | m] =ᵐ[P] fun _ => c)
    {Z : Ω → E} (hZ : StronglyMeasurable[m] Z) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ C) :
    ‖∫ ω, (X ω - c) • Z ω ∂P‖ ≤ C * ∫ ω, |X ω - Y ω| ∂P := by
  have hce : P[(fun ω => X ω - c) | m] =ᵐ[P]
      fun ω => P[X | m] ω - c := by
    have h := condExp_sub hX (integrable_const c) m
    rw [condExp_const hm] at h
    exact h
  calc
    ‖∫ ω, (X ω - c) • Z ω ∂P‖ ≤
        C * ∫ ω, |P[(fun ω => X ω - c) | m] ω| ∂P :=
      norm_integral_smul_le_conditional_abs (mΩ := mΩ) hm
        (hX.sub (integrable_const c)) hZ hbound
    _ = C * ∫ ω, |P[X | m] ω - c| ∂P := by
      congr 1
      exact integral_congr_ae (hce.fun_comp abs)
    _ ≤ C * ∫ ω, |X ω - Y ω| ∂P :=
      mul_le_mul_of_nonneg_left
        (integral_abs_condExp_sub_const_le (mΩ := mΩ) hX hY hmean) hC

theorem preBrownian_increment_sq_condExp_enlarged
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hmB : ∀ t, StronglyMeasurable (B t))
    {mSignal m : MeasurableSpace Ω} (hSignal : mSignal ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap (fun ω t => B t ω) inferInstance) mSignal P)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hm : m ≤ Filtration.natural B hmB s ⊔ mSignal) :
    P[(fun ω => (B t ω - B s ω)^2) | m] =ᵐ[P]
      fun _ => (t : ℝ) - (s : ℝ) := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  let mPath := MeasurableSpace.comap (fun ω t => B t ω) inferInstance
  let : MeasurableSpace Ω := mΩ
  have hpath : mPath ≤ mΩ :=
    (Measurable.of_eval (fun time => (hmB time).measurable)).comap_le
  have hcoord (u : ℝ≥0) : StronglyMeasurable[mPath] (B u) := by
    have harray : @Measurable Ω (ℝ≥0 → ℝ) mPath inferInstance
        (fun ω t => B t ω) := measurable_iff_comap_le.mpr le_rfl
    exact ((measurable_pi_apply u).comp harray).stronglyMeasurable
  have hnat : Filtration.natural B hmB s ≤ mPath := by
    change (⨆ u ≤ s, MeasurableSpace.comap (B u) inferInstance) ≤ mPath
    exact iSup₂_le fun u _ => (hcoord u).measurable.comap_le
  have hint : Integrable (fun ω => (B t ω - B s ω)^2) P :=
    ((hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.sub
      (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two).integrable_sq
  have hlarge : P[(fun ω => (B t ω - B s ω)^2) |
      Filtration.natural B hmB s ⊔ mSignal] =ᵐ[P]
      fun _ => (t : ℝ) - (s : ℝ) :=
    (condExp_sup_independent_future hnat hpath hSignal hind
      (((hcoord t).sub (hcoord s)).pow 2) hint).trans
      (preBrownian_increment_sq_condExp (mΩ := mΩ) hB hmB hst)
  have hlarge_le : Filtration.natural B hmB s ⊔ mSignal ≤ mΩ :=
    sup_le (Filtration.natural B hmB |>.le s) hSignal
  calc
    P[(fun ω => (B t ω - B s ω)^2) | m] =ᵐ[P]
        P[P[(fun ω => (B t ω - B s ω)^2) |
          Filtration.natural B hmB s ⊔ mSignal] | m] :=
      (condExp_condExp_of_le hm hlarge_le).symm
    _ =ᵐ[P] P[(fun _ : Ω => (t : ℝ) - (s : ℝ)) | m] :=
      condExp_congr_ae hlarge
    _ =ᵐ[P] fun _ => (t : ℝ) - (s : ℝ) := by
      rw [condExp_const (hm.trans hlarge_le)]

theorem preBrownian_integral_abs_conditional_sq_error_le
    {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hmB : ∀ t, StronglyMeasurable (B t))
    {mSignal m : MeasurableSpace Ω} (hSignal : mSignal ≤ mΩ)
    (hind : Indep (MeasurableSpace.comap (fun ω t => B t ω) inferInstance) mSignal P)
    {s t : ℝ≥0} (hst : s ≤ t)
    (hm : m ≤ Filtration.natural B hmB s ⊔ mSignal)
    {D : Ω → ℝ} (hD : MemLp D 2 P) :
    (∫ ω, |P[(fun ω => D ω ^ 2) | m] ω - ((t : ℝ) - (s : ℝ))| ∂P) ≤
      ∫ ω, |D ω ^ 2 - (B t ω - B s ω)^2| ∂P := by
  let : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  exact integral_abs_condExp_sub_const_le (mΩ := mΩ) hD.integrable_sq
    ((hB.isGaussianProcess.hasGaussianLaw_eval t).memLp_two.sub
      (hB.isGaussianProcess.hasGaussianLaw_eval s).memLp_two).integrable_sq
    (preBrownian_increment_sq_condExp_enlarged (mΩ := mΩ) hB hmB hSignal hind hst hm)

end Problem367.InnovationConditionalMoments

end

end OAI
