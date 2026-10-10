import OAI.Analysis.CircleDomains.Topology.PhysicalSimpleArcPortion
import OAI.Analysis.CircleDomains.Probability.ArcImageMeasures

namespace OAI

/-! Physical occupation of a simple quotient arc is bounded by Hausdorff
length on its physical image. This retains arbitrary measurable densities. -/

open Set Function MeasureTheory
open scoped ENNReal Classical

noncomputable section
namespace CircleDomainRigidity

theorem simple_arc_physical_stage_occupation_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (hinj : Injective γ.val) (n : ℕ) :
    physicalStageOccupation e y₀ n γ.val ≤ (μH[1] : Measure Y).restrict
      ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U)) := by
  let f := physicalValue e y₀ ∘ γ.val
  let J := {i : Fin (2 ^ n) | Icc (dyadicLeft n i) (dyadicRight n i) ⊆ γ.val ⁻¹' U}
  let : NullSingletonClass (μH[1] : Measure Y) :=
    Measure.nullSingletonClass_hausdorff Y (by norm_num)
  have hdis : Pairwise (fun i j : J => Disjoint
      (Ioc (dyadicLeft n i.val) (dyadicRight n i.val))
      (Ioc (dyadicLeft n j.val) (dyadicRight n j.val))) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro t ht hs
    have hne : i.val ≠ j.val := fun h => hij (Subtype.ext h)
    rcases lt_or_gt_of_ne hne with h | h
    · have hsep : dyadicRight n i.val ≤ dyadicLeft n j.val :=
        dyadicReal_mono n (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (ht.2.trans hsep)) hs.1
    · have hsep : dyadicRight n j.val ≤ dyadicLeft n i.val :=
        dyadicReal_mono n (Nat.succ_le_of_lt h)
      exact (not_lt_of_ge (hs.2.trans hsep)) ht.1
  have he : physicalStageOccupation e y₀ n γ.val =
      ∑ i : J, (μH[1] : Measure Y).restrict
        (f '' Icc (dyadicLeft n i.val) (dyadicRight n i.val)) := by
    apply Finset.sum_congr_set J
    · intro i hi
      rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi]
      apply physical_simple_arc_portion_occupation e hU y₀ γ hinj _ hi
      change (i.val : ℝ) / (2 : ℝ) ^ n < ((i.val + 1 : ℕ) : ℝ) / (2 : ℝ) ^ n
      exact div_lt_div_of_pos_right (by exact_mod_cast Nat.lt_succ_self i.val) (by positivity)
    · intro i hi
      have hi' : γ.val ∉ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i) := hi
      simp only [physicalDyadicPath, totalPhysicalSubpath, dite_eq_right hi',
        rectifiableOccupationCode_const]
  rw [he]
  exact sum_disjoint_arc_image_measures_le (μH[1] : Measure Y) f
    (physicalValue_path_continuousOn e y₀ γ.val) (physicalValue_path_injOn e y₀ γ.val hinj)
    (fun i : J => dyadicLeft n i.val) (fun i : J => dyadicRight n i.val)
    (fun i => dyadicLeft_le_right n i.val) (fun i => i.property) hdis

theorem simple_arc_physical_occupation_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (hinj : Injective γ.val) :
    dyadicPhysicalOccupation e y₀ γ ≤ (μH[1] : Measure Y).restrict
      ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U)) := by
  apply Measure.le_iff.mpr
  intro S hS
  rw [dyadicPhysicalOccupation_apply e y₀ γ hS]
  exact iSup_le fun n => Measure.le_iff.mp
    (simple_arc_physical_stage_occupation_le e hU y₀ γ hinj n) S hS

theorem simple_arc_physical_integral_le
    {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}
    (e : G ≃ₜ U) (hU : IsOpen U) (y₀ : Y) (γ : FinitePhysicalPath e y₀)
    (hinj : Injective γ.val) (g : Y → ℝ≥0∞) :
    ∫⁻ y, g y ∂dyadicPhysicalOccupation e y₀ γ ≤
      ∫⁻ y in (physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U), g y ∂(μH[1] : Measure Y) :=
  lintegral_mono' (simple_arc_physical_occupation_le e hU y₀ γ hinj) le_rfl

end CircleDomainRigidity

end

end OAI
