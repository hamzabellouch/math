import OAI.MeasureTheory.Falconer.Estimates.SphericalEnergy
import Mathlib.MeasureTheory.Measure.Continuity

namespace OAI

/-! # Shrinking affine slabs have vanishing mass when their hyperplanes are null -/

namespace Falconer
open Set MeasureTheory Filter NormedSpace
open scoped ENNReal Topology

theorem exists_small_sublevel_of_null_fiber {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (f : X → ℝ) (hf : Measurable f)
    (hzero : μ {x | f x = 0} = 0) {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ μ {x | |f x| ≤ r} < η := by
  let E : ℝ → Set X := fun r => {x | |f x| ≤ r}
  have hlim := tendsto_measure_biInter_gt (μ := μ) (s := E) (a := (0:ℝ))
    (fun r _ => (measurableSet_le
      (by simpa only [Real.norm_eq_abs] using hf.norm) measurable_const).nullMeasurableSet)
    (fun _ _ _ hij => fun _ hx => hx.trans hij)
    ⟨1,by norm_num,measure_ne_top μ _⟩
  have heq : (⋂ r > (0:ℝ), E r) = {x | f x = 0} := by
    ext x
    simp only [mem_iInter,mem_ofPred_eq,E]
    constructor
    · intro hx
      have hh : |f x| = 0 := by
        by_contra hn
        have hp : 0 < |f x| := lt_of_le_of_ne (abs_nonneg _) (Ne.symm hn)
        have h := hx (|f x|/2) (by positivity)
        linarith only [h,hp]
      exact abs_eq_zero.mp hh
    · intro hx r hr
      simpa only [hx,abs_zero] using hr.le
  rw [heq,hzero] at hlim
  have hevent : ∀ᶠ r : ℝ in 𝓝[>] 0, μ (E r) < η := hlim.eventually (gt_mem_nhds hη)
  have hpos : ∀ᶠ r : ℝ in 𝓝[>] 0, 0 < r := self_mem_nhdsWithin
  obtain ⟨r,hr,hsmall⟩ := (hpos.and hevent).exists
  exact ⟨r,hr,hsmall⟩

theorem exists_small_affine_slab {d : ℕ} (μ : Measure (Space d)) [IsFiniteMeasure μ]
    (w : Space d) (a : ℝ) (hzero : μ {x | inner ℝ w x = a} = 0)
    {η : ℝ≥0∞} (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ μ {x | |inner ℝ w x-a| ≤ r} < η := by
  apply exists_small_sublevel_of_null_fiber μ (fun x => inner ℝ w x-a)
    ((continuous_const.inner continuous_id).sub continuous_const).measurable _ hη
  simpa only [sub_eq_zero] using hzero

theorem affine_slab_parameter_bound {d : ℕ} {w w' x : Space d} {a a' M : ℝ}
    (hx : ‖x‖ ≤ M) :
    |(inner ℝ w x-a)-(inner ℝ w' x-a')| ≤ M*‖w-w'‖+|a-a'| := by
  calc
    _ = |inner ℝ (w-w') x-(a-a')| := by congr 1; rw [inner_sub_left]; ring
    _ ≤ |inner ℝ (w-w') x|+|a-a'| := abs_sub _ _
    _ ≤ ‖w-w'‖*‖x‖+|a-a'| := add_le_add (abs_real_inner_le_norm _ _) le_rfl
    _ ≤ M*‖w-w'‖+|a-a'| := by nlinarith only [hx,norm_nonneg (w-w')]

end Falconer

end OAI
