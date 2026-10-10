import OAI.Analysis.CircleDomains.Probability.PathImageOccupation
import OAI.Analysis.CircleDomains.Modulus.PartialSimpleArcLength
import OAI.Analysis.CircleDomains.Probability.SimplePhysicalArcOccupation

namespace OAI

/-! General physical paths pay for the Hausdorff measure of their images.
Together with the opposite simple-arc bound this makes erasing loops decrease
physical occupation, including for arbitrary measurable densities. -/

open Set Function MeasureTheory
open scoped ENNReal Topology Classical

noncomputable section
namespace CircleDomainRigidity

variable {X Y : Type*} [MetricSpace X] [MetricSpace Y]
  [MeasurableSpace Y] [BorelSpace Y] {G : Set Y} {U : Set X}

def physicalStageImage (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) (n : ℕ) : Set Y :=
  ⋃ i : Fin (2 ^ n), if γ ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
    then (physicalValue e y₀ ∘ γ) '' Icc (dyadicLeft n i) (dyadicRight n i) else ∅

omit [MeasurableSpace Y] [BorelSpace Y] in
lemma physicalSubpath_range (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X))
    {a b : PathTime} (hab : a ≤ b) (hγ : γ ∈ pathsInsideOn U a b) :
    range (physicalSubpath e hab ⟨γ, hγ⟩) =
      (physicalValue e y₀ ∘ γ) '' Icc a b := by
  have he : (physicalSubpath e hab ⟨γ, hγ⟩ : PathTime → Y) =
      (physicalValue e y₀ ∘ γ) ∘ timeClip a b := by
    funext t
    have ht : timeClip a b t ∈ Icc a b := by
      rw [← range_timeClip hab]
      exact mem_range_self t
    exact ((congrArg (fun f : C(PathTime, Y) => f t)
      (physicalSubpath_comp_clip e hab ⟨γ, hγ⟩)).symm).trans
        (physicalValue_subpath e y₀ hab ⟨γ, hγ⟩ ht).symm
  rw [he, range_comp, range_timeClip hab]

omit [MeasurableSpace Y] [BorelSpace Y] in
lemma physicalStageImage_subset (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) (n : ℕ) :
    physicalStageImage e y₀ γ n ⊆ (physicalValue e y₀ ∘ γ) '' (γ ⁻¹' U) := by
  intro y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  split_ifs at hi with hgood
  · exact image_mono hgood hi
  · exact False.elim hi

omit [MeasurableSpace Y] [BorelSpace Y] in
lemma monotone_physicalStageImage (e : G ≃ₜ U) (y₀ : Y) (γ : C(PathTime, X)) :
    Monotone (physicalStageImage e y₀ γ) := by
  apply monotone_nat_of_le_succ
  intro n y hy
  obtain ⟨i, hi⟩ := mem_iUnion.mp hy
  split_ifs at hi with hgood
  · obtain ⟨t, ht, rfl⟩ := hi
    rw [dyadicCell_split] at ht
    rcases ht with ht | ht
    · apply mem_iUnion.mpr
      refine ⟨dyadicEven n i, ?_⟩
      have hc : γ ∈ pathsInsideOn U (dyadicLeft (n+1) (dyadicEven n i))
          (dyadicRight (n+1) (dyadicEven n i)) := by
        apply hgood.mono_left
        rw [dyadicCell_split n i]
        exact subset_union_left
      simp only [ite_eq_left hc]
      exact ⟨t, ht, rfl⟩
    · apply mem_iUnion.mpr
      refine ⟨dyadicOdd n i, ?_⟩
      have hc : γ ∈ pathsInsideOn U (dyadicLeft (n+1) (dyadicOdd n i))
          (dyadicRight (n+1) (dyadicOdd n i)) := by
        apply hgood.mono_left
        rw [dyadicCell_split n i]
        exact subset_union_right
      simp only [ite_eq_left hc]
      exact ⟨t, ht, rfl⟩
  · exact False.elim hi

omit [MeasurableSpace Y] [BorelSpace Y] in
lemma iUnion_physicalStageImage (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : C(PathTime, X)) :
    (⋃ n, physicalStageImage e y₀ γ n) = (physicalValue e y₀ ∘ γ) '' (γ ⁻¹' U) := by
  apply Subset.antisymm (iUnion_subset (physicalStageImage_subset e y₀ γ))
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨p, hp⟩ := mem_iUnion.mp ((iUnion_insideDyadicCell (hU.preimage γ.continuous)).symm ▸ ht)
  apply mem_iUnion.mpr
  refine ⟨p.val.1, mem_iUnion.mpr ⟨p.val.2, ?_⟩⟩
  have hg : γ ∈ pathsInsideOn U (dyadicLeft p.val.1 p.val.2) (dyadicRight p.val.1 p.val.2) := p.property
  rw [ite_eq_left hg]
  exact ⟨t, hp, rfl⟩

lemma physicalStageImage_hausdorff_le (e : G ≃ₜ U) (y₀ : Y)
    (γ : FinitePhysicalPath e y₀) (n : ℕ) :
    (μH[1] : Measure Y).restrict (physicalStageImage e y₀ γ.val n) ≤
      physicalStageOccupation e y₀ n γ.val := by
  unfold physicalStageImage physicalStageOccupation
  apply le_trans Measure.restrict_iUnion_le
  rw [Measure.sum_fintype]
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
  · rw [ite_eq_left hi]
    have hr := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hi] at hr ⊢
    rw [← physicalSubpath_range e y₀ γ.val (dyadicLeft_le_right n i) hi,
      rectifiableOccupationCode_eq hr]
    exact path_image_hausdorff_le_occupation ⟨_, hr⟩
  · rw [ite_eq_right hi, Measure.restrict_empty]
    exact bot_le

theorem physical_image_hausdorff_le_occupation (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) :
    (μH[1] : Measure Y).restrict ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U)) ≤
      dyadicPhysicalOccupation e y₀ γ := by
  rw [← iUnion_physicalStageImage e hU y₀ γ.val]
  apply Measure.le_iff.mpr
  intro S hS
  rw [Measure.restrict_iUnion_apply_eq_iSup (monotone_physicalStageImage e y₀ γ.val).directed_le hS,
    dyadicPhysicalOccupation_apply e y₀ γ hS]
  exact iSup_mono fun n => physicalStageImage_hausdorff_le e y₀ γ n S

theorem simple_subarc_physical_length_le (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) (α : C(PathTime, X))
    (hinj : Injective α) (hsub : range α ⊆ range γ.val) :
    physicalDomainLength e y₀ α ≤ physicalDomainLength e y₀ γ.val := by
  apply (simple_quotient_arc_physical_length_le e y₀ α hinj).trans
  have hs : (physicalValue e y₀ ∘ α) '' (α ⁻¹' U) ⊆
      (physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U) := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨s, hs⟩ := hsub (mem_range_self t)
    exact ⟨s, by simpa only [mem_preimage, hs] using ht, by simp only [comp_apply, hs]⟩
  calc
    (μH[1] : Measure Y) ((physicalValue e y₀ ∘ α) '' (α ⁻¹' U)) ≤
      (μH[1] : Measure Y) ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U)) := measure_mono hs
    _ = ((μH[1] : Measure Y).restrict
      ((physicalValue e y₀ ∘ γ.val) '' (γ.val ⁻¹' U))) univ := (Measure.restrict_apply_univ _).symm
    _ ≤ dyadicPhysicalOccupation e y₀ γ univ := physical_image_hausdorff_le_occupation e hU y₀ γ univ
    _ = _ := dyadicPhysicalOccupation_univ e y₀ γ

theorem simple_subarc_physical_occupation_le (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ α : FinitePhysicalPath e y₀)
    (hinj : Injective α.val) (hsub : range α.val ⊆ range γ.val) :
    dyadicPhysicalOccupation e y₀ α ≤ dyadicPhysicalOccupation e y₀ γ := by
  apply (simple_arc_physical_occupation_le e hU y₀ α hinj).trans
  apply le_trans (Measure.restrict_mono_set _ ?_) (physical_image_hausdorff_le_occupation e hU y₀ γ)
  rintro _ ⟨t, ht, rfl⟩
  obtain ⟨s, hs⟩ := hsub (mem_range_self t)
  exact ⟨s, by simpa only [mem_preimage, hs] using ht, by simp only [comp_apply, hs]⟩

end CircleDomainRigidity

end

end OAI
