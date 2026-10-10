import OAI.Dynamics.EntropyCounterexample.SphereInfinityChart
import OAI.Geometry.SingularHomology.HomologyConstant
import OAI.Geometry.SingularHomology.HomologyHomotopyEquiv

namespace OAI

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Problem340.SphereCover

def northComplement : Set StandardSphere2 := {chartNorthPole}ᶜ

def southComplement : Set StandardSphere2 := {chartSouthPole}ᶜ

lemma south_ne_north : chartSouthPole ≠ chartNorthPole :=
  sphereOfComplex_ne_north 0

lemma isOpen_northComplement : IsOpen northComplement := isOpen_compl_singleton

lemma isOpen_southComplement : IsOpen southComplement := isOpen_compl_singleton

lemma cover : northComplement ∪ southComplement = Set.univ := by
  ext x
  simp only [northComplement, southComplement, Set.mem_union, Set.mem_compl_iff,
    Set.mem_singleton_iff, Set.mem_univ, iff_true]
  by_cases h : x = chartNorthPole
  · exact Or.inr (by simpa [h] using south_ne_north.symm)
  · exact Or.inl h

def northHomeomorph : northComplement ≃ₜ ℂ where
  toFun x := sphereToComplex x.val
  invFun z := ⟨sphereOfComplex z, sphereOfComplex_ne_north z⟩
  left_inv x := Subtype.ext (sphereOfComplex_sphereToComplex x.property)
  right_inv z := sphereToComplex_sphereOfComplex z
  continuous_toFun := continuousOn_sphereToComplex.domRestrict
  continuous_invFun := continuous_sphereOfComplex.subtype_mk _

def flipHomeomorph : StandardSphere2 ≃ₜ StandardSphere2 where
  toFun := sphereInfinityFlip
  invFun := sphereInfinityFlip
  left_inv := sphereInfinityFlip_involutive
  right_inv := sphereInfinityFlip_involutive
  continuous_toFun := (sphereInfinityFlipLinear.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (sphereInfinityFlipLinear.continuous.comp continuous_subtype_val).subtype_mk _

def southToNorthHomeomorph : southComplement ≃ₜ northComplement :=
  flipHomeomorph.subtype (fun x => by
    change x ≠ chartSouthPole ↔ sphereInfinityFlip x ≠ chartNorthPole
    constructor
    · intro hx heq
      apply hx
      have h := congrArg sphereInfinityFlip heq
      simpa only [sphereInfinityFlip_involutive, sphereInfinityFlip_north] using h
    · intro hx heq
      apply hx
      rw [heq, sphereInfinityFlip_south])

def southHomeomorph : southComplement ≃ₜ ℂ :=
  southToNorthHomeomorph.trans northHomeomorph

instance north_contractible : ContractibleSpace northComplement :=
  northHomeomorph.contractibleSpace

instance south_contractible : ContractibleSpace southComplement :=
  southHomeomorph.contractibleSpace

lemma north_homology_subsingleton (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (RealSingularHomology n northComplement) :=
  realSingularHomology_subsingleton_of_contractible n hn northComplement

lemma south_homology_subsingleton (n : ℕ) (hn : n ≠ 0) :
    Subsingleton (RealSingularHomology n southComplement) :=
  realSingularHomology_subsingleton_of_contractible n hn southComplement

abbrev PuncturedPlane := {z : ℂ // z ≠ 0}

def overlapHomeomorph : ↥(northComplement ∩ southComplement) ≃ₜ PuncturedPlane where
  toFun x := ⟨sphereToComplex x.val, by
    intro hz
    apply x.property.2
    change x.val = sphereOfComplex 0
    rw [← sphereOfComplex_sphereToComplex x.property.1, hz]⟩
  invFun z := ⟨sphereOfComplex z.val, sphereOfComplex_ne_north z.val, by
    intro h
    apply z.property
    exact sphereOfComplex_injective h⟩
  left_inv x := Subtype.ext (sphereOfComplex_sphereToComplex x.property.1)
  right_inv z := Subtype.ext (sphereToComplex_sphereOfComplex z.val)
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact (continuousOn_sphereToComplex.mono Set.inter_subset_left).domRestrict
  continuous_invFun := (continuous_sphereOfComplex.comp continuous_subtype_val).subtype_mk _

abbrev ComplexCircle := Metric.sphere (0 : ℂ) (1 : ℝ)

def radialRetraction : C(PuncturedPlane, ComplexCircle) where
  toFun z := ⟨‖z.val‖⁻¹ • z.val, by
    have hz : ‖z.val‖ ≠ 0 := norm_ne_zero_iff.mpr z.property
    simp [hz]⟩
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    exact ((continuous_norm.comp continuous_subtype_val).inv₀
      (fun z => norm_ne_zero_iff.mpr z.property)).smul continuous_subtype_val

def circleInclusion : C(ComplexCircle, PuncturedPlane) where
  toFun z := ⟨z.val, ne_zero_of_mem_unit_sphere z⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

lemma radialRetraction_circleInclusion (z : ComplexCircle) :
    radialRetraction (circleInclusion z) = z := by
  apply Subtype.ext
  change ‖z.val‖⁻¹ • z.val = z.val
  rw [norm_eq_of_mem_sphere z]
  simp

lemma radial_coefficient_pos (t : unitInterval) (z : PuncturedPlane) :
    0 < (1 - (t : ℝ)) * ‖z.val‖⁻¹ + (t : ℝ) := by
  have hr : 0 < ‖z.val‖ := norm_pos_iff.mpr z.property
  by_cases ht : 0 < (t : ℝ)
  · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (sub_nonneg.mpr t.property.2) (inv_nonneg.mpr hr.le)) ht
  · have ht0 : (t : ℝ) = 0 := le_antisymm (le_of_not_gt ht) t.property.1
    simp only [ht0, sub_zero, one_mul, add_zero]
    exact inv_pos.mpr hr

def radialHomotopy : ContinuousMap.Homotopy
    (circleInclusion.comp radialRetraction) (ContinuousMap.id PuncturedPlane) where
  toFun p := ⟨((1 - (p.1 : ℝ)) * ‖p.2.val‖⁻¹ + (p.1 : ℝ)) • p.2.val,
    smul_ne_zero (ne_of_gt (radial_coefficient_pos p.1 p.2)) p.2.property⟩
  continuous_toFun := by
    apply continuous_induced_rng.mpr
    have ht : Continuous (fun p : unitInterval × PuncturedPlane => (p.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    have hz : Continuous (fun p : unitInterval × PuncturedPlane => p.2.val) :=
      continuous_subtype_val.comp continuous_snd
    exact (((continuous_const.sub ht).mul
      (hz.norm.inv₀ (fun p => norm_ne_zero_iff.mpr p.2.property))).add ht).smul hz
  map_zero_left z := by
    apply Subtype.ext
    change ((1 - (0 : ℝ)) * ‖z.val‖⁻¹ + 0) • z.val = ‖z.val‖⁻¹ • z.val
    simp
  map_one_left z := by
    apply Subtype.ext
    change ((1 - (1 : ℝ)) * ‖z.val‖⁻¹ + 1) • z.val = z.val
    simp

def puncturedPlaneEquivCircle : PuncturedPlane ≃ₕ ComplexCircle where
  toFun := radialRetraction
  invFun := circleInclusion
  left_inv := ⟨radialHomotopy⟩
  right_inv := by
    have h : radialRetraction.comp circleInclusion = ContinuousMap.id ComplexCircle := by
      apply ContinuousMap.ext
      intro z
      exact radialRetraction_circleInclusion z
    rw [h]

def overlapEquivCircle : ↥(northComplement ∩ southComplement) ≃ₕ ComplexCircle :=
  overlapHomeomorph.toHomotopyEquiv.trans puncturedPlaneEquivCircle

lemma radialHomotopy_fixes_circle (t : unitInterval) (z : ComplexCircle) :
    radialHomotopy (t, circleInclusion z) = circleInclusion z := by
  apply Subtype.ext
  change ((1 - (t : ℝ)) * ‖z.val‖⁻¹ + (t : ℝ)) • z.val = z.val
  rw [norm_eq_of_mem_sphere z]
  simp

def circleHomeomorphClock : ComplexCircle ≃ₜ StandardClock :=
  Complex.orthonormalBasisOneI.repr.toHomeomorph.subtype (fun z => by
    simp only [Metric.mem_sphere, dist_zero_right]
    change ‖z‖ = 1 ↔ ‖Complex.orthonormalBasisOneI.repr z‖ = 1
    rw [LinearIsometryEquiv.norm_map])

def overlapEquivClock : ↥(northComplement ∩ southComplement) ≃ₕ StandardClock :=
  overlapEquivCircle.trans circleHomeomorphClock.toHomotopyEquiv

def overlapHomologyEquivClock (n : ℕ) :
    RealSingularHomology n ↥(northComplement ∩ southComplement) ≃ₗ[ℝ]
      RealSingularHomology n StandardClock :=
  realHomologyEquivOfHomotopyEquiv n overlapEquivClock

end Problem340.SphereCover

end

end OAI
