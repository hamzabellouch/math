import OAI.Analysis.ModularTheory.NormalAdjointMap
import OAI.Analysis.ModularTheory.ProjectionExhaustion

namespace OAI

/-! The concrete cutoff orbits are total in the modular Hilbert space.
This supplies the density needed when gluing finite tracial corners. -/

noncomputable section
open MeasureTheory Filter Set FourierTransform
open scoped Topology InnerProductSpace ENNReal

namespace WeakPureInfiniteness
open BoundedRecovery

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup K] [NormedSpace ℂ K]

lemma modularCutoff_annihilator_scalar (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] K)
    (hz : ∀ a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ),
      a ∈ modularCrossedProduct volume S → ∀ n, T (a (modularCoreWeightVector S n)) = 0)
    (a : H →L[ℂ] H) (ha : a ∈ S.M) (f : Lp ℂ 2 (volume : Measure ℝ)) :
    T (modularLpRepresentation volume S.D a (modularScalarInclusion volume S f)) = 0 := by
  let R : Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] K :=
    T.comp ((modularLpRepresentation volume S.D a).comp
      (modularFourierInclusion S).toContinuousLinearMap)
  have hfzero (b : BoundedContinuousFunction ℝ ℂ) (hb : MemLp b 2 (volume : Measure ℝ)) :
      R (hb.toLp b) = 0 := by
    have hcut (n : ℕ) : R (scalarIntervalProjection n (hb.toLp b)) = 0 := by
      rw [← modularWeightCutoffInverse_apply n b hb]
      change T (modularLpRepresentation volume S.D a
        (modularFourierInclusion S (scalarLpRepresentation volume
          (b * modularWeightCutoffInverse n) (modularWeightCutoffVector n)))) = 0
      rw [← modularTranslationCalculus_fourierInclusion]
      exact hz (modularLpRepresentation volume S.D a *
        modularTranslationCalculus (b * modularWeightCutoffInverse n))
        (modularNormalOrdered_mem S a ha _) n
    exact tendsto_nhds_unique
      (R.continuous.continuousAt.tendsto.comp (scalarIntervalProjection_strong (hb.toLp b)))
      (by simpa only [Function.comp_def, hcut] using
        tendsto_const_nhds (x := (0 : K)))
  have hR (g : Lp ℂ 2 (volume : Measure ℝ)) : R g = 0 := by
    refine (Lp.boundedContinuousFunction_dense ℂ (volume : Measure ℝ)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).induction ?_
      (isClosed_eq R.continuous continuous_const) g
    intro x hx
    obtain ⟨b, hb⟩ := Lp.mem_boundedContinuousFunction_iff.mp hx
    have hxb : (x : ℝ → ℂ) =ᵐ[volume] b := by
      have h := b.toContinuousMap.coeFn_toAEEqFun (volume : Measure ℝ)
      rw [hb] at h
      exact h
    have hbLp : MemLp b 2 (volume : Measure ℝ) := MemLp.ae_eq hxb (Lp.memLp x)
    have he : hbLp.toLp b = x := by
      apply Lp.ext
      exact (MemLp.coeFn_toLp hbLp).trans hxb.symm
    rw [← he]
    exact hfzero b hbLp
  have he := hR (𝓕 f)
  change T (modularLpRepresentation volume S.D a
    (modularScalarInclusion volume S (𝓕⁻ (𝓕 f)))) = 0 at he
  simpa only [fourierInv_fourier_eq] using he

lemma modularCutoff_annihilator_eq_zero (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] K)
    (hz : ∀ a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ),
      a ∈ modularCrossedProduct volume S → ∀ n, T (a (modularCoreWeightVector S n)) = 0) :
    T = 0 := by
  let U := S.D.lpGaugeEquiv (volume : Measure ℝ) 1
  let R : Lp H 2 (volume : Measure ℝ) →L[ℂ] K := T.comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap
  have hind {s : Set ℝ} (hs : MeasurableSet s) (hμ : volume s ≠ ⊤) (x : H) :
      R (indicatorConstLp 2 hs hμ x) = 0 := by
    refine S.cyclic.induction ?_
      (isClosed_eq (R.continuous.comp (indicatorVectorCLM volume hs hμ).continuous)
        continuous_const) x
    rintro y ⟨a, ha, rfl⟩
    have hi : (ContinuousLinearMap.toSpanSingleton ℂ (a S.xi)).compLpL 2 volume
        (indicatorConstLp 2 hs hμ (1 : ℂ)) = indicatorConstLp 2 hs hμ (a S.xi) := by
      apply Lp.ext
      filter_upwards [(ContinuousLinearMap.toSpanSingleton ℂ (a S.xi)).coeFn_compLpL
          (indicatorConstLp 2 hs hμ (1 : ℂ)),
        indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := (1 : ℂ)),
        indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμ) (c := a S.xi)]
        with t h₁ h₂ h₃
      rw [h₁, h₂, h₃]
      by_cases ht : t ∈ s <;> simp [ht]
    rw [← hi, ← modularGauge_coefficient_scalar S]
    change T (U.symm (U (modularLpRepresentation volume S.D a
      (modularScalarInclusion volume S (indicatorConstLp 2 hs hμ (1 : ℂ)))))) = 0
    rw [U.symm_apply_apply]
    exact modularCutoff_annihilator_scalar S T hz a ha _
  have hR : R = 0 := by
    apply ContinuousLinearMap.ext
    intro f
    change R f = 0
    refine (Lp.simpleFunc.dense (E := H) (μ := volume)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).induction ?_
      (isClosed_eq R.continuous continuous_const) f
    intro g hg
    let g' : Lp.simpleFunc H 2 volume := ⟨g, hg⟩
    change R (g' : Lp H 2 volume) = 0
    induction g' using Lp.simpleFunc.induction (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) with
    | indicatorConst x hs hμ => exact hind hs hμ.ne x
    | add hf hg hfg h₁ h₂ =>
        change R (_ + _) = 0
        rw [map_add, h₁, h₂, add_zero]
  apply ContinuousLinearMap.ext
  intro f
  change T f = 0
  have he := congrArg (fun A : Lp H 2 (volume : Measure ℝ) →L[ℂ] K => A (U f)) hR
  change T (U.symm (U f)) = 0 at he
  simpa only [LinearIsometryEquiv.symm_apply_apply] using he

/-- The positive-size supported corners already have total cutoff orbits. -/
lemma modularFiniteCorner_annihilator_eq_zero (S : StandardModularData H)
    (T : Lp H 2 (volume : Measure ℝ) →L[ℂ] K)
    (hz : ∀ n (a : Lp H 2 (volume : Measure ℝ) →L[ℂ] Lp H 2 (volume : Measure ℝ)),
      a ∈ modularCrossedProduct volume S →
      T ((modularFiniteProjection (H := H) (n + 1) * a * modularFiniteProjection (H := H) (n + 1))
        (modularCoreWeightVector S (n + 1))) = 0) : T = 0 := by
  apply modularCutoff_annihilator_eq_zero S T
  intro a ha m
  have he : ∀ᶠ n in atTop,
      T (modularFiniteProjection (H := H) (n + 1) (a (modularCoreWeightVector S m))) = 0 := by
    filter_upwards [eventually_ge_atTop m] with n hn
    have h := hz n (a * modularFiniteProjection m)
      (mul_mem ha (modularFiniteProjection_mem S m))
    simpa only [mul_apply_eq_comp,
      modularFiniteProjection_weightVector S (n + 1) (n + 1) le_rfl,
      modularFiniteProjection_weightVector S m (n + 1) (hn.trans (Nat.le_succ n))] using h
  exact tendsto_nhds_unique
    (T.continuous.continuousAt.tendsto.comp
      ((modularFiniteProjection_strong (a (modularCoreWeightVector S m))).comp
        (tendsto_add_atTop_nat 1)))
    (tendsto_const_nhds.congr' (he.mono fun _ hn => hn.symm))

end WeakPureInfiniteness

end

end OAI
