import OAI.Analysis.CircleDomains.Modulus.DyadicTimeLength
import OAI.Analysis.CircleDomains.Modulus.PhysicalCompactLength
import OAI.Analysis.CircleDomains.Probability.DyadicMeasurePartition

namespace OAI

/-! The global time measure restricts to ordinary physical arclength on
 every compact interval contained in the open physical-domain times. -/

open Set Filter MeasureTheory
open scoped Topology ENNReal

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  {G : Set Y} {U : Set X}

theorem physicalSubpath_length_inter (e : G ≃ₜ U)
    {a b c d : PathTime} (hab : a ≤ b) (hcd : c ≤ d) (γ : C(PathTime, X))
    (h₁ : γ ∈ pathsInsideOn U a b) (h₂ : γ ∈ pathsInsideOn U c d)
    (hb₁ : BoundedVariationOn (physicalSubpath e hab ⟨γ, h₁⟩) univ)
    (hb₂ : BoundedVariationOn (physicalSubpath e hcd ⟨γ, h₂⟩) univ) :
    (rectifiableLengthCode (physicalSubpath e hab ⟨γ, h₁⟩)).restrict (Icc c d) =
      (rectifiableLengthCode (physicalSubpath e hcd ⟨γ, h₂⟩)).restrict (Icc a b) := by
  rw [physicalSubpath_timeLength_portion e hab _ hb₁,
    physicalSubpath_timeLength_portion e hcd _ hb₂,
    Measure.restrict_restrict measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, inter_comm (Icc c d), Icc_inter_Icc]
  apply pathLengthMeasure_restrict_congr
  intro t ht
  rw [← Icc_inter_Icc] at ht
  exact physicalSubpath_eq_on e hab hcd γ h₁ h₂ ht.1 ht.2

theorem physicalDyadicTimeLength_restrict (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a ≤ b)
    (hγ : γ.val ∈ pathsInsideOn U a b) (n : ℕ) (i : Fin (2 ^ n))
    (hgood : (Icc (dyadicLeft n i) (dyadicRight n i) ∩ Icc a b).Nonempty →
      γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)) :
    (rectifiableLengthCode (physicalDyadicPath e y₀ n i γ.val)).restrict (Icc a b) =
      (rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩)).restrict
        (Icc (dyadicLeft n i) (dyadicRight n i)) := by
  classical
  by_cases hi : (Icc (dyadicLeft n i) (dyadicRight n i) ∩ Icc a b).Nonempty
  · have hg := hgood hi
    have hc := physicalDyadicPath_rectifiable e y₀ γ.property n i
    rw [physicalDyadicPath_of_mem e y₀ n i γ.val hg] at hc ⊢
    exact physicalSubpath_length_inter e (dyadicLeft_le_right n i) hab γ.val hg hγ hc
      (physicalSubpath_rectifiable e hU hab γ.val hγ y₀ γ.property)
  · have hzero : (rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩)).restrict
        (Icc (dyadicLeft n i) (dyadicRight n i)) = 0 := by
      rw [physicalSubpath_timeLength_portion e hab _
        (physicalSubpath_rectifiable e hU hab γ.val hγ y₀ γ.property),
        Measure.restrict_restrict measurableSet_Icc, not_nonempty_iff_eq_empty.mp hi,
        Measure.restrict_empty]
    rw [hzero]
    by_cases hg : γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)
    · rw [physicalDyadicPath_of_mem e y₀ n i γ.val hg,
        physicalSubpath_timeLength_portion e (dyadicLeft_le_right n i) _ (by
          have h := physicalDyadicPath_rectifiable e y₀ γ.property n i
          rwa [physicalDyadicPath_of_mem e y₀ n i γ.val hg] at h),
        Measure.restrict_restrict measurableSet_Icc, inter_comm,
        not_nonempty_iff_eq_empty.mp hi, Measure.restrict_empty]
    · simp [physicalDyadicPath, totalPhysicalSubpath, hg, rectifiableLengthCode_const]

theorem physicalStageTimeLength_restrict (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a ≤ b)
    (hγ : γ.val ∈ pathsInsideOn U a b) (n : ℕ)
    (hgood : ∀ i : Fin (2 ^ n),
      (Icc (dyadicLeft n i) (dyadicRight n i) ∩ Icc a b).Nonempty →
      γ.val ∈ pathsInsideOn U (dyadicLeft n i) (dyadicRight n i)) :
    (physicalStageTimeLength e y₀ n γ.val).restrict (Icc a b) =
      rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩) := by
  calc
    _ = ∑ i : Fin (2 ^ n),
        (rectifiableLengthCode (physicalDyadicPath e y₀ n i γ.val)).restrict (Icc a b) := by
      ext s hs
      simp [physicalStageTimeLength, Measure.restrict_apply hs,
        Measure.coe_finsetSum, Finset.sum_apply]
    _ = ∑ i : Fin (2 ^ n),
        (rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩)).restrict
          (Icc (dyadicLeft n i) (dyadicRight n i)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact physicalDyadicTimeLength_restrict e hU y₀ γ hab hγ n i (hgood i)
    _ = _ := sum_dyadic_restrict _ n

theorem physicalTimeLength_restrict_compact (e : G ≃ₜ U) (hU : IsOpen U)
    (y₀ : Y) (γ : FinitePhysicalPath e y₀) {a b : PathTime} (hab : a ≤ b)
    (hγ : γ.val ∈ pathsInsideOn U a b) :
    (physicalTimeLength e y₀ γ).restrict (Icc a b) =
      rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩) := by
  have hevent : ∀ᶠ n : ℕ in atTop,
      (physicalStageTimeLength e y₀ n γ.val).restrict (Icc a b) =
        rectifiableLengthCode (physicalSubpath e hab ⟨γ.val, hγ⟩) := by
    filter_upwards [eventually_dyadic_cells_inside (hU.preimage γ.val.continuous) hγ]
      with n hn
    exact physicalStageTimeLength_restrict e hU y₀ γ hab hγ n hn
  ext s hs
  rw [Measure.restrict_apply hs, physicalTimeLength_apply _ _ _ (hs.inter measurableSet_Icc)]
  apply le_antisymm
  · apply iSup_le
    intro n
    obtain ⟨m, hm, hnm⟩ := (hevent.and (eventually_ge_atTop n)).exists
    have hval := congrArg (fun μ : Measure PathTime => μ s) hm
    rw [Measure.restrict_apply hs] at hval
    exact ((monotone_physicalStageTimeLength e y₀ γ.property hnm) _).trans_eq hval
  · obtain ⟨n, hn⟩ := hevent.exists
    have hval := congrArg (fun μ : Measure PathTime => μ s) hn
    rw [Measure.restrict_apply hs] at hval
    rw [← hval]
    exact le_iSup (fun n => physicalStageTimeLength e y₀ n γ.val (s ∩ Icc a b)) n

end CircleDomainRigidity

end

end OAI
