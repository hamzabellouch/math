import OAI.Probability.FreeIsing.Estimates.PastCompatibility

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped MeasureTheory

namespace Problem367.TerminalSufficiency

variable {Ω ι : Type*}

theorem comap_path_eq_terminal_sup_residual
    (X R : Ω → ι → ℝ) (Y : Ω → ℝ) (a : ι → ℝ) (i₀ : ι)
    (hX : ∀ ω i, X ω i = a i * Y ω + R ω i)
    (hY : ∀ ω, X ω i₀ = Y ω) :
    MeasurableSpace.comap X inferInstance =
      MeasurableSpace.comap Y inferInstance ⊔ MeasurableSpace.comap R inferInstance := by
  let mX := MeasurableSpace.comap X inferInstance
  let mY := MeasurableSpace.comap Y inferInstance
  let mR := MeasurableSpace.comap R inferInstance
  have hXm : Measurable[mX] X := measurable_iff_comap_le.mpr le_rfl
  have hYm : Measurable[mX] Y := by
    have h := (measurable_pi_apply i₀).comp hXm
    have heq : (fun ω => X ω i₀) = Y := funext hY
    simpa only [Function.comp_def, heq] using h
  apply le_antisymm
  · have hY' : Measurable[mY ⊔ mR] Y := measurable_iff_comap_le.mpr le_sup_left
    have hR' : Measurable[mY ⊔ mR] R := measurable_iff_comap_le.mpr le_sup_right
    have h : Measurable[mY ⊔ mR] (fun ω i => a i * Y ω + R ω i) := by
      let : MeasurableSpace Ω := mY ⊔ mR
      apply Measurable.of_eval
      intro i
      exact (hY'.const_mul (a i)).add ((measurable_pi_apply i).comp hR')
    have heq : X = (fun ω i => a i * Y ω + R ω i) := funext (fun ω => funext (hX ω))
    rw [heq]
    exact h.comap_le
  · apply sup_le hYm.comap_le
    have h : Measurable[mX] (fun ω i => X ω i - a i * Y ω) := by
      let : MeasurableSpace Ω := mX
      apply Measurable.of_eval
      intro i
      exact ((measurable_pi_apply i).comp hXm).sub (hYm.const_mul (a i))
    have heq : R = (fun ω i => X ω i - a i * Y ω) := by
      funext ω i
      rw [hX]
      ring
    rw [heq]
    exact h.comap_le

theorem comap_array_eq_terminal_sup_residual {J : Type*}
    (X R : Ω → ι → J → ℝ) (Y : Ω → J → ℝ) (a : ι → ℝ) (i₀ : ι)
    (hX : ∀ ω i j, X ω i j = a i * Y ω j + R ω i j)
    (hY : ∀ ω j, X ω i₀ j = Y ω j) :
    MeasurableSpace.comap X inferInstance =
      MeasurableSpace.comap Y inferInstance ⊔ MeasurableSpace.comap R inferInstance := by
  let mX := MeasurableSpace.comap X inferInstance
  let mY := MeasurableSpace.comap Y inferInstance
  let mR := MeasurableSpace.comap R inferInstance
  have hXm : Measurable[mX] X := measurable_iff_comap_le.mpr le_rfl
  have hYm : Measurable[mX] Y := by
    have h := (measurable_pi_apply i₀).comp hXm
    have heq : (fun ω => X ω i₀) = Y := funext (fun ω => funext (hY ω))
    simpa only [Function.comp_def, heq] using h
  apply le_antisymm
  · have hY' : Measurable[mY ⊔ mR] Y := measurable_iff_comap_le.mpr le_sup_left
    have hR' : Measurable[mY ⊔ mR] R := measurable_iff_comap_le.mpr le_sup_right
    have h : Measurable[mY ⊔ mR] (fun ω i j => a i * Y ω j + R ω i j) := by
      let : MeasurableSpace Ω := mY ⊔ mR
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro j
      exact (((measurable_pi_apply j).comp hY').const_mul (a i)).add
        ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hR'))
    have heq : X = (fun ω i j => a i * Y ω j + R ω i j) :=
      funext (fun ω => funext (fun i => funext (hX ω i)))
    rw [heq]
    exact h.comap_le
  · apply sup_le hYm.comap_le
    have h : Measurable[mX] (fun ω i j => X ω i j - a i * Y ω j) := by
      let : MeasurableSpace Ω := mX
      apply Measurable.of_eval
      intro i
      apply Measurable.of_eval
      intro j
      exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hXm)).sub
        (((measurable_pi_apply j).comp hYm).const_mul (a i))
    have heq : R = (fun ω i j => X ω i j - a i * Y ω j) := by
      funext ω i j
      rw [hX]
      ring
    rw [heq]
    exact h.comap_le

theorem comap_swap_indices {J : Type*} (X : Ω → ι → J → ℝ) :
    MeasurableSpace.comap (fun ω j i => X ω i j) inferInstance =
      MeasurableSpace.comap X inferInstance := by
  change MeasurableSpace.comap (fun ω j i => X ω i j) inferInstance =
    MeasurableSpace.comap (fun ω i j => X ω i j) inferInstance
  rw [MeasurableSpace.comap_process_pi (fun j (ω : Ω) (i : ι) => X ω i j),
    MeasurableSpace.comap_process_pi (fun i (ω : Ω) (j : J) => X ω i j)]
  simp_rw [MeasurableSpace.comap_process_pi]
  rw [iSup_comm]

theorem condExp_observation_eq_statistic
    {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (Y : Ω → A) (R : Ω → B) (X : Ω → C)
    (hf : Measurable f) (hY : Measurable Y) (hR : Measurable R)
    (hfint : Integrable f μ)
    (hindep : IndepFun (fun ω => (f ω, Y ω)) R μ)
    (hcomap : MeasurableSpace.comap X inferInstance =
      MeasurableSpace.comap Y inferInstance ⊔ MeasurableSpace.comap R inferInstance) :
    μ[f | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      μ[f | MeasurableSpace.comap Y inferInstance] := by
  rw [hcomap]
  let mPast := MeasurableSpace.comap (fun ω => (f ω, Y ω)) inferInstance
  have hmPair : Measurable[mPast] (fun ω => (f ω, Y ω)) :=
    measurable_iff_comap_le.mpr le_rfl
  have hSmall : MeasurableSpace.comap Y inferInstance ≤ mPast :=
    (measurable_snd.comp hmPair).comap_le
  have hPast : mPast ≤ m := (hf.prodMk hY).comap_le
  have hfm : StronglyMeasurable[mPast] f :=
    (measurable_fst.comp hmPair).stronglyMeasurable
  exact Problem367.condExp_sup_independent_future hSmall hPast hR.comap_le
    hindep hfm hfint

theorem condExp_path_eq_terminal_of_indep_residual
    {m : MeasurableSpace Ω} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f Y : Ω → ℝ) (X R : Ω → ι → ℝ) (a : ι → ℝ) (i₀ : ι)
    (hf : Measurable f) (hYm : Measurable Y) (hRm : Measurable R)
    (hfint : Integrable f μ)
    (hindep : IndepFun (fun ω => (f ω, Y ω)) R μ)
    (hX : ∀ ω i, X ω i = a i * Y ω + R ω i)
    (hY : ∀ ω, X ω i₀ = Y ω) :
    μ[f | MeasurableSpace.comap X inferInstance] =ᵐ[μ]
      μ[f | MeasurableSpace.comap Y inferInstance] := by
  exact condExp_observation_eq_statistic μ f Y R X hf hYm hRm hfint hindep
    (comap_path_eq_terminal_sup_residual X R Y a i₀ hX hY)

end Problem367.TerminalSufficiency

end

end OAI
