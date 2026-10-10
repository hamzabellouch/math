import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Integral.Prod

namespace OAI

/-! # Successive averages in the real bulk coordinates

Finite measures act on bounded continuous functions by replacing one
coordinate and integrating it. The operators commute at distinct coordinates,
so a uniform one-coordinate error may be used before or after other replacements.
-/

namespace Ostmann
open MeasureTheory
open scoped Classical BoundedContinuousFunction

noncomputable def coordinateSlice {σ : Type*} [Fintype σ] (f : (σ → ℝ) →ᵇ ℂ)
    (i : σ) (x : σ → ℝ) : ℝ →ᵇ ℂ :=
  f.compContinuous ⟨fun t => Function.update x i t,
    continuous_const.update i continuous_id⟩

noncomputable def coordinateAverage {σ : Type*} [Fintype σ] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (i : σ) (f : (σ → ℝ) →ᵇ ℂ) : (σ → ℝ) →ᵇ ℂ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x => ∫ t, f (Function.update x i t) ∂μ)
    (continuous_of_dominated
      (fun x => (coordinateSlice f i x).continuous.aestronglyMeasurable)
      (fun _x => Filter.Eventually.of_forall fun _t => f.norm_coe_le_norm _)
      (integrable_const ‖f‖)
      (Filter.Eventually.of_forall fun _t =>
        f.continuous.comp (continuous_id.update i continuous_const)))
    (μ.real Set.univ * ‖f‖)
    (fun x => (coordinateSlice f i x).norm_integral_le_mul_norm μ |>.trans
      (mul_le_mul_of_nonneg_left
        (BoundedContinuousFunction.norm_compContinuous_le _ _) (measureReal_nonneg)))

@[simp] theorem coordinateAverage_apply {σ : Type*} [Fintype σ] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (i : σ) (f : (σ → ℝ) →ᵇ ℂ) (x : σ → ℝ) :
    coordinateAverage μ i f x = ∫ t, f (Function.update x i t) ∂μ := rfl

theorem coordinateAverage_norm {σ : Type*} [Fintype σ] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (i : σ) (f : (σ → ℝ) →ᵇ ℂ) :
    ‖coordinateAverage μ i f‖ ≤ μ.real Set.univ * ‖f‖ :=
  BoundedContinuousFunction.norm_ofNormedAddCommGroup_le _
    (mul_nonneg measureReal_nonneg (norm_nonneg _)) _

theorem coordinateAverage_sub {σ : Type*} [Fintype σ] (μ : Measure ℝ) [IsFiniteMeasure μ]
    (i : σ) (f g : (σ → ℝ) →ᵇ ℂ) :
    coordinateAverage μ i (f - g) = coordinateAverage μ i f - coordinateAverage μ i g := by
  ext x
  exact integral_sub ((coordinateSlice f i x).integrable μ)
    ((coordinateSlice g i x).integrable μ)

theorem coordinateAverage_commute {σ : Type*} [Fintype σ] (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (i j : σ) (hij : i ≠ j)
    (f : (σ → ℝ) →ᵇ ℂ) :
    coordinateAverage μ i (coordinateAverage ν j f) =
      coordinateAverage ν j (coordinateAverage μ i f) := by
  ext x
  simp only [coordinateAverage_apply]
  let g : (ℝ × ℝ) →ᵇ ℂ := f.compContinuous
    ⟨fun z => Function.update (Function.update x i z.1) j z.2,
      ((show Continuous (fun _ : ℝ × ℝ => x) from continuous_const).update i continuous_fst).update j continuous_snd⟩
  have h := integral_integral_swap (μ := μ) (ν := ν)
    (f := fun t s => f (Function.update (Function.update x i t) j s)) (g.integrable (μ.prod ν))
  change (∫ t, ∫ s, f (Function.update (Function.update x i t) j s) ∂ν ∂μ) = _ at h
  rw [h]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun s => integral_congr_ae
    (Filter.Eventually.of_forall fun t => by dsimp only; rw [Function.update_comm hij])

noncomputable def coordinateAverages {σ : Type*} [Fintype σ] (μ : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] : List σ → ((σ → ℝ) →ᵇ ℂ) → ((σ → ℝ) →ᵇ ℂ)
  | [], f => f
  | i :: l, f => coordinateAverage (μ i) i (coordinateAverages μ l f)

theorem coordinateAverages_sub {σ : Type*} [Fintype σ] (μ : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (l : List σ) (f g : (σ → ℝ) →ᵇ ℂ) :
    coordinateAverages μ l (f - g) = coordinateAverages μ l f - coordinateAverages μ l g := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [coordinateAverages, ih, coordinateAverage_sub]

theorem coordinateAverages_norm {σ : Type*} [Fintype σ] (μ : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (l : List σ)
    (hμ : ∀ i ∈ l, (μ i).real Set.univ ≤ 2) (f : (σ → ℝ) →ᵇ ℂ) :
    ‖coordinateAverages μ l f‖ ≤ 2 ^ l.length * ‖f‖ := by
  induction l with
  | nil => simp [coordinateAverages]
  | cons i l ih =>
    calc
      _ ≤ (μ i).real Set.univ * ‖coordinateAverages μ l f‖ := coordinateAverage_norm _ _ _
      _ ≤ 2 * (2 ^ l.length * ‖f‖) := mul_le_mul (hμ i (by simp))
        (ih (fun j hj => hμ j (by simp [hj]))) (norm_nonneg _) (by norm_num)
      _ = _ := by simp only [List.length_cons, pow_succ]; ring

theorem coordinateAverages_commute {σ : Type*} [Fintype σ] (μ : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] (ν : Measure ℝ) [IsFiniteMeasure ν]
    (l : List σ) (i : σ) (hi : i ∉ l) (f : (σ → ℝ) →ᵇ ℂ) :
    coordinateAverage ν i (coordinateAverages μ l f) =
      coordinateAverages μ l (coordinateAverage ν i f) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    have hij : i ≠ j := fun h => hi (by simp [h])
    have hil : i ∉ l := fun h => hi (by simp [h])
    simp only [coordinateAverages, coordinateAverage_commute ν (μ j) i j hij, ih hil]

/-- A uniform slice comparison accumulates only the masses of the other
coordinates. It is applied to the original function, not assumed for functions
which have already been averaged. -/
theorem coordinateAverages_comparison {σ : Type*} [Fintype σ] (μ ν : σ → Measure ℝ)
    [∀ i, IsFiniteMeasure (μ i)] [∀ i, IsFiniteMeasure (ν i)]
    (l : List σ) (hl : l.Nodup)
    (hμ : ∀ i ∈ l, (μ i).real Set.univ ≤ 2)
    (hν : ∀ i ∈ l, (ν i).real Set.univ ≤ 2)
    (f : (σ → ℝ) →ᵇ ℂ) (ε : σ → ℝ) (hε : ∀ i ∈ l, 0 ≤ ε i)
    (herr : ∀ i ∈ l, ‖coordinateAverage (μ i) i f - coordinateAverage (ν i) i f‖ ≤ ε i) :
    ‖coordinateAverages μ l f - coordinateAverages ν l f‖ ≤
      2 ^ l.length * (l.map ε).sum := by
  induction l with
  | nil => simp [coordinateAverages]
  | cons i l ih =>
    obtain ⟨hi, hl⟩ := List.nodup_cons.mp hl
    have hμl : ∀ j ∈ l, (μ j).real Set.univ ≤ 2 := fun j hj => hμ j (by simp [hj])
    have hνl : ∀ j ∈ l, (ν j).real Set.univ ≤ 2 := fun j hj => hν j (by simp [hj])
    have he0 := hε i (by simp)
    have heSum : 0 ≤ (l.map ε).sum := List.sum_nonneg (by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ha
      exact hε j (by simp [hj]))
    have htail := ih hl hμl hνl (fun j hj => hε j (by simp [hj]))
      (fun j hj => herr j (by simp [hj]))
    have hfirst :
        ‖coordinateAverage (μ i) i (coordinateAverages ν l f) -
          coordinateAverage (ν i) i (coordinateAverages ν l f)‖ ≤ 2 ^ l.length * ε i := by
      rw [coordinateAverages_commute ν (μ i) l i hi,
        coordinateAverages_commute ν (ν i) l i hi, ← coordinateAverages_sub]
      exact (coordinateAverages_norm ν l hνl _).trans
        (mul_le_mul_of_nonneg_left (herr i (by simp)) (by positivity))
    change ‖coordinateAverage (μ i) i (coordinateAverages μ l f) -
      coordinateAverage (ν i) i (coordinateAverages ν l f)‖ ≤ _
    calc
      _ ≤ ‖coordinateAverage (μ i) i (coordinateAverages μ l f) -
            coordinateAverage (μ i) i (coordinateAverages ν l f)‖ +
          ‖coordinateAverage (μ i) i (coordinateAverages ν l f) -
            coordinateAverage (ν i) i (coordinateAverages ν l f)‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ 2 * (2 ^ l.length * (l.map ε).sum) + 2 ^ l.length * ε i := by
        apply add_le_add _ hfirst
        rw [← coordinateAverage_sub]
        exact (coordinateAverage_norm _ _ _).trans
          (mul_le_mul (hμ i (by simp)) htail (norm_nonneg _) (by norm_num))
      _ ≤ 2 ^ (i :: l).length * ((i :: l).map ε).sum := by
        simp only [List.length_cons, List.map_cons, List.sum_cons, pow_succ]
        nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) l.length]

end Ostmann

end OAI
