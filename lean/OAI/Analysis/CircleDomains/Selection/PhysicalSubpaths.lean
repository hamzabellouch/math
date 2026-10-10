import OAI.Analysis.CircleDomains.Topology.ClippedPaths

namespace OAI

/-! Actual physical lifts of quotient paths on a compact time interval.
The quotient is inverted only where it is a homeomorphism. Constant extension
at the interval ends gives an ordinary continuous physical path. -/

open Set MeasureTheory
open scoped Topology

noncomputable section

namespace CircleDomainRigidity

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def pathsInsideOn (U : Set X) (a b : PathTime) : Set C(PathTime, X) :=
  {γ | MapsTo γ (Icc a b) U}

theorem isOpen_pathsInsideOn {U : Set X} (hU : IsOpen U) (a b : PathTime) :
    IsOpen (pathsInsideOn U a b) :=
  ContinuousMap.isOpen_setOfPred_mapsTo isCompact_Icc hU

def physicalSubpath {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b) : C(PathTime, Y) where
  toFun t := (e.symm ⟨γ.val (timeClip a b t), γ.property (by
    rw [← range_timeClip hab]
    exact mem_range_self t)⟩).val
  continuous_toFun := continuous_subtype_val.comp
    (e.symm.continuous.comp ((γ.val.continuous.comp (timeClip a b).continuous).subtype_mk _))

theorem continuous_physicalSubpath {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) : Continuous (physicalSubpath e hab) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  exact continuous_subtype_val.comp (e.symm.continuous.comp
    ((continuous_eval.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      ((timeClip a b).continuous.comp continuous_snd))).subtype_mk _))

theorem physicalSubpath_mem {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b) (t : PathTime) :
    physicalSubpath e hab γ t ∈ G :=
  (e.symm _).property

theorem physicalSubpath_eq_on {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    {a b c d : PathTime} (hab : a ≤ b) (hcd : c ≤ d) (γ : C(PathTime, X))
    (h₁ : γ ∈ pathsInsideOn U a b) (h₂ : γ ∈ pathsInsideOn U c d)
    {t : PathTime} (ht₁ : t ∈ Icc a b) (ht₂ : t ∈ Icc c d) :
    physicalSubpath e hab ⟨γ, h₁⟩ t = physicalSubpath e hcd ⟨γ, h₂⟩ t := by
  simp only [physicalSubpath, ContinuousMap.coe_mk, timeClip,
    min_eq_right ht₁.2, max_eq_right ht₁.1,
    min_eq_right ht₂.2, max_eq_right ht₂.1]

theorem physicalSubpath_comp_clip {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b) :
    (physicalSubpath e hab γ).comp (timeClip a b) = physicalSubpath e hab γ := by
  apply ContinuousMap.ext
  intro t
  have ht : timeClip a b t ∈ Icc a b := by
    rw [← range_timeClip hab]
    exact mem_range_self t
  simp only [ContinuousMap.comp_apply, physicalSubpath, ContinuousMap.coe_mk]
  apply congrArg Subtype.val
  apply congrArg e.symm
  apply Subtype.ext
  apply congrArg γ.val
  change max a (min b (timeClip a b t)) = timeClip a b t
  rw [min_eq_right ht.2, max_eq_right ht.1]

theorem physicalSubpath_projects {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    (π : Y → X) (hπ : ∀ y : G, π y = (e y).val)
    {a b : PathTime} (hab : a ≤ b) (γ : pathsInsideOn U a b) (t : PathTime) :
    π (physicalSubpath e hab γ t) = γ.val (timeClip a b t) := by
  change π (e.symm ⟨γ.val (timeClip a b t), _⟩).val = _
  rw [hπ]
  simp

def totalPhysicalSubpath {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    {a b : PathTime} (hab : a ≤ b) (y₀ : Y) (γ : C(PathTime, X)) : C(PathTime, Y) := by
  classical
  exact if h : γ ∈ pathsInsideOn U a b then physicalSubpath e hab ⟨γ, h⟩
    else ContinuousMap.const _ y₀

variable [MeasurableSpace C(PathTime, X)] [BorelSpace C(PathTime, X)]
  [MeasurableSpace C(PathTime, Y)] [BorelSpace C(PathTime, Y)]

theorem measurable_totalPhysicalSubpath {G : Set Y} {U : Set X} (e : G ≃ₜ U)
    (hU : IsOpen U) {a b : PathTime} (hab : a ≤ b) (y₀ : Y) :
    Measurable (totalPhysicalSubpath e hab y₀) := by
  classical
  exact (continuous_physicalSubpath e hab).measurable.dite
    measurable_const (isOpen_pathsInsideOn hU a b).measurableSet

end CircleDomainRigidity

end

end OAI
