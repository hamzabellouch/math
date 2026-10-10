import OAI.NumberTheory.DukePrimeDegree.Dynamics.FiniteKoopmanAverages
import OAI.NumberTheory.DukePrimeDegree.Geometry.DenseDiagonalGenerators
import OAI.NumberTheory.DukePrimeDegree.Dynamics.L2ToL1Averages
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

namespace OAI

/-!
# Jointly ergodic averaging for a continuous group action

The averaged Koopman operator uses a finite topologically generating
family. Its common fixed vectors are constant by group ergodicity and
continuity of the L2 action. No generator is assumed ergodic.
-/

noncomputable section
open MeasureTheory Filter Set TopologicalSpace
open scoped Topology ENNReal

namespace DukePrimeDegree

variable {G X I : Type*} [Group G] [TopologicalSpace G]
  [MeasurableSpace G] [OpensMeasurableSpace G]
  [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  [MulAction G X] [ContinuousSMul G X]
  [Fintype I] [Nonempty I]
  (μ : Measure X) [IsProbabilityMeasure μ] [μ.InnerRegularCompactLTTop]
  [ErgodicSMul G X μ]

def actionKoopman (g : Gᵈᵐᵃ) : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  (Lp.compMeasurePreservingₗᵢ ℝ (fun x => DomMulAct.mk.symm g • x)
    (measurePreserving_smul (DomMulAct.mk.symm g) μ)).toContinuousLinearMap

omit [R1Space X] [IsProbabilityMeasure μ] [μ.InnerRegularCompactLTTop] in
lemma actionKoopman_apply (g : Gᵈᵐᵃ) (f : Lp ℝ 2 μ) :
    actionKoopman μ g f = g • f := rfl

omit [R1Space X] [IsProbabilityMeasure μ] [μ.InnerRegularCompactLTTop] in
lemma actionKoopman_norm (g : Gᵈᵐᵃ) (f : Lp ℝ 2 μ) :
    ‖actionKoopman μ g f‖ = ‖f‖ := by
  exact Lp.norm_compMeasurePreserving f _

/-- The fixed space of the finite averaging operator consists of
constants, using ergodicity of the entire acting group. -/
theorem finite_action_average_fixed_constant
    (a : I → Gᵈᵐᵃ)
    (hdense : Dense (Subgroup.closure (range a) : Set Gᵈᵐᵃ))
    (f : Lp ℝ 2 μ)
    (hfix : finiteIsometryAverage (actionKoopman μ ∘ a) f = f) :
    ∃ c : ℝ, f = constantL2 μ c := by
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  have hall : ∀ i, actionKoopman μ (a i) f = f :=
    (finiteIsometryAverage_fixed_iff (actionKoopman μ ∘ a)
      (fun i q => actionKoopman_norm μ (a i) q) f).mp hfix
  have haction : ∀ g : Gᵈᵐᵃ, g • f = f :=
    fixed_of_dense_generators a hdense f (fun i => hall i)
  have hae : ∀ g : G, (fun x => f (g • x)) =ᵐ[μ] (f : X → ℝ) := by
    intro g
    have he := (DomMulAct.smul_Lp_ae_eq (DomMulAct.mk g) f).symm
    rwa [haction (DomMulAct.mk g)] at he
  obtain ⟨c, hc⟩ := ae_eq_const_of_group_invariant μ f (Lp.aestronglyMeasurable f) hae
  exact ⟨c, Lp.ext (hc.trans (constantL2_ae μ c).symm)⟩

theorem finite_action_average_tendsto_constant
    (a : I → Gᵈᵐᵃ)
    (hdense : Dense (Subgroup.closure (range a) : Set Gᵈᵐᵃ))
    (f : Lp ℝ 2 μ) :
    ∃ c : ℝ, Tendsto
      (fun N => birkhoffAverage ℝ (finiteIsometryAverage (actionKoopman μ ∘ a)) id N f)
      atTop (𝓝 (constantL2 μ c)) := by
  let P := finiteIsometryAverage (actionKoopman μ ∘ a)
  have hP : ‖P‖ ≤ 1 := finiteIsometryAverage_norm_le (actionKoopman μ ∘ a)
    (fun i q => actionKoopman_norm μ (a i) q)
  let S := P.eqLocus (1 : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
  let q : S := S.orthogonalProjectionOnto f
  have hq : P (q : Lp ℝ 2 μ) = (q : Lp ℝ 2 μ) := by
    have h := q.property
    change P (q : Lp ℝ 2 μ) = (q : Lp ℝ 2 μ) at h
    exact h
  obtain ⟨c, hc⟩ := finite_action_average_fixed_constant μ a hdense q hq
  refine ⟨c, ?_⟩
  have hav := P.tendsto_birkhoffAverage_orthogonalProjection hP f
  change Tendsto (fun N => birkhoffAverage ℝ P id N f) atTop (𝓝 (q : Lp ℝ 2 μ)) at hav
  rw [hc] at hav
  exact hav

omit [R1Space X] [μ.InnerRegularCompactLTTop] in
lemma meanL2_actionKoopman (g : Gᵈᵐᵃ) (f : Lp ℝ 2 μ) :
    meanL2 μ (actionKoopman μ g f) = meanL2 μ f :=
  meanL2_koopman μ (fun x => DomMulAct.mk.symm g • x)
    (measurePreserving_smul (DomMulAct.mk.symm g) μ) f

omit [R1Space X] [μ.InnerRegularCompactLTTop] in
lemma meanL2_finite_action_average (a : I → Gᵈᵐᵃ) (f : Lp ℝ 2 μ) :
    meanL2 μ (finiteIsometryAverage (actionKoopman μ ∘ a) f) = meanL2 μ f := by
  classical
  have hcard : (Fintype.card I : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [finiteIsometryAverage_apply, map_smul, map_sum]
  simp only [Function.comp_apply, meanL2_actionKoopman, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hcard, one_mul]

omit [R1Space X] [μ.InnerRegularCompactLTTop] in
lemma meanL2_finite_action_iterate (a : I → Gᵈᵐᵃ) (f : Lp ℝ 2 μ) (N : ℕ) :
    meanL2 μ ((finiteIsometryAverage (actionKoopman μ ∘ a))^[N] f) = meanL2 μ f := by
  induction N with
  | zero => rfl
  | succ N ih =>
    rw [Function.iterate_succ_apply', meanL2_finite_action_average, ih]

omit [R1Space X] [μ.InnerRegularCompactLTTop] in
lemma meanL2_finite_action_birkhoff (a : I → Gᵈᵐᵃ) (f : Lp ℝ 2 μ)
    (N : ℕ) (hN : N ≠ 0) :
    meanL2 μ (birkhoffAverage ℝ (finiteIsometryAverage (actionKoopman μ ∘ a)) id N f) =
      meanL2 μ f := by
  simp only [birkhoffAverage, birkhoffSum, map_smul, map_sum,
    meanL2_finite_action_iterate, id_eq, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, smul_eq_mul]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  field_simp

/-- Joint ergodicity gives convergence to the integral without assuming
ergodicity of any single member of the finite generating family. -/
theorem finite_action_average_tendsto_integral
    (a : I → Gᵈᵐᵃ)
    (hdense : Dense (Subgroup.closure (range a) : Set Gᵈᵐᵃ))
    (f : Lp ℝ 2 μ) :
    Tendsto
      (fun N => birkhoffAverage ℝ (finiteIsometryAverage (actionKoopman μ ∘ a)) id N f)
      atTop (𝓝 (constantL2 μ (∫ x, f x ∂μ))) := by
  obtain ⟨c, hc⟩ := finite_action_average_tendsto_constant μ a hdense f
  have hmean := (meanL2 μ).continuous.tendsto (constantL2 μ c) |>.comp hc
  have hequal : Tendsto
      (fun N => meanL2 μ (birkhoffAverage ℝ
        (finiteIsometryAverage (actionKoopman μ ∘ a)) id N f))
      atTop (𝓝 (meanL2 μ f)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    exact (meanL2_finite_action_birkhoff μ a f N (Nat.ne_of_gt hN)).symm
  have he := tendsto_nhds_unique hmean hequal
  rw [meanL2_constant, meanL2_apply] at he
  rwa [he] at hc

end DukePrimeDegree

namespace DukePrimeDegree

variable {J X : Type*} [Fintype J] [DecidableEq J] [Nonempty J]
  [TopologicalSpace X] [R1Space X] [MeasurableSpace X] [BorelSpace X]
  [MulAction (Multiplicative (J → ℝ)) X] [ContinuousSMul (Multiplicative (J → ℝ)) X]
  (μ : Measure X) [IsProbabilityMeasure μ] [μ.InnerRegularCompactLTTop]
  [ErgodicSMul (Multiplicative (J → ℝ)) X μ]

local instance : MeasurableSpace (Multiplicative (J → ℝ)) := borel _
local instance : BorelSpace (Multiplicative (J → ℝ)) := ⟨rfl⟩

/-- The concrete one-and-square-root-of-two coordinate generators give
the full diagonal-action average, assuming only A-ergodicity. -/
theorem diagonal_action_average_tendsto_integral (f : Lp ℝ 2 μ) :
    Tendsto (fun N => birkhoffAverage ℝ
      (finiteIsometryAverage (actionKoopman μ ∘ domainParameterGenerators (I := J))) id N f)
      atTop (𝓝 (constantL2 μ (∫ x, f x ∂μ))) :=
  finite_action_average_tendsto_integral μ _ dense_domainParameterGenerators f

/-- The same concrete group averages converge under moving laws with
a uniform density bound. None of the individual diagonal translations
needs to be ergodic. -/
theorem dominated_diagonal_action_average_tendsto_integral (f : Lp ℝ 2 μ)
    (ν : ℕ → Measure X) [∀ n, IsProbabilityMeasure (ν n)]
    (C : ℝ) (hC : 0 ≤ C) (hdom : ∀ n, ν n ≤ ENNReal.ofReal C • μ) :
    Tendsto (fun N => ∫ x,
      (birkhoffAverage ℝ
        (finiteIsometryAverage (actionKoopman μ ∘ domainParameterGenerators (I := J))) id N f) x
          ∂ν N) atTop (𝓝 (∫ x, f x ∂μ)) := by
  apply integral_tendsto_of_dominated_sampling μ ν C _ hC hdom
  · intro N
    exact memLp_one_iff_integrable.mp ((Lp.memLp _).mono_exponent (by norm_num))
  · exact L1_tendsto_of_L2_tendsto_constant μ _ _
      (diagonal_action_average_tendsto_integral μ f)

end DukePrimeDegree

end

end OAI
