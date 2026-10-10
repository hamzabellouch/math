import Mathlib
import OAI.Probability.LogConcave.LowerBounds.TranscriptRejection
import OAI.Probability.LogConcave.Sampling.MapProdFiberLaw

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise

namespace LogConcaveSampling.LowerBound
open Matrix WithLp ProbabilityTheory
open scoped RealInnerProductSpace

def rotationIsometry {d : ℕ} (O : Rotations d) : Point d ≃ₗᵢ[ℝ] Point d :=
  Unitary.linearIsometryEquiv
    (Unitary.map (StarMonoidHom.ofClass (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ))) O)

@[simp] theorem rotationIsometry_apply {d : ℕ} (O : Rotations d) (x : Point d) :
    rotationIsometry O x = toLp 2 ((O : Matrix (Fin d) (Fin d) ℝ) *ᵥ ofLp x) := rfl

def rotationFromIsometry {d : ℕ} (T : Point d ≃ₗᵢ[ℝ] Point d) : Rotations d :=
  Unitary.map (StarMonoidHom.ofClass
    (A := Point d →L[ℝ] Point d) (B := Matrix (Fin d) (Fin d) ℝ)
    ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm.toStarAlgHom))
    (Unitary.linearIsometryEquiv.symm T)

@[simp] theorem rotationIsometry_from {d : ℕ} (T : Point d ≃ₗᵢ[ℝ] Point d) :
    rotationIsometry (rotationFromIsometry T) = T := by
  apply Unitary.linearIsometryEquiv.symm.injective
  simp only [rotationIsometry, MulEquiv.symm_apply_apply]
  apply Subtype.ext
  change (Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ))
    ((Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℝ)).symm (T : Point d →L[ℝ] Point d)) = _
  exact (Matrix.toEuclideanCLM).apply_symm_apply _

@[simp] theorem rotationIsometry_mul {d : ℕ} (O P : Rotations d) (x : Point d) :
    rotationIsometry (O * P) x = rotationIsometry O (rotationIsometry P x) := by
  simp only [rotationIsometry_apply]
  change toLp 2 (((O : Matrix (Fin d) (Fin d) ℝ) * (P : Matrix (Fin d) (Fin d) ℝ)) *ᵥ ofLp x) = _
  rw [← Matrix.mulVec_mulVec]

@[fun_prop] theorem continuous_rotation_apply {d : ℕ} :
    Continuous (fun p : Rotations d × Point d => rotationIsometry p.1 p.2) := by
  simp only [rotationIsometry_apply]
  fun_prop

theorem exists_rotation_of_norm_eq {d : ℕ} {x y : Point d} (h : ‖x‖ = ‖y‖) :
    ∃ P : Rotations d, rotationIsometry P x = y := by
  refine ⟨rotationFromIsometry (Submodule.reflection (ℝ ∙ (x-y))ᗮ), ?_⟩
  rw [rotationIsometry_from, Submodule.reflection_sub h]

instance rotationHaar_rightInvariant (d : ℕ) : (rotationHaar d).IsMulRightInvariant := by
  constructor
  intro P
  have : IsProbabilityMeasure ((rotationHaar d).map (· * P)) :=
    inferInstance
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace
    ((rotationHaar d).map (· * P)) (rotationHaar d)
  have hm := congrArg (fun μ : Measure (Rotations d) => μ Set.univ) h
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hm
  have hc : (((rotationHaar d).map (· * P)).haarScalarFactor (rotationHaar d)) = 1 := by
    exact ENNReal.coe_injective hm.symm
  rw [hc, one_smul] at h
  exact h

theorem haar_orbit_eq {d : ℕ} {x y : Point d} (h : ‖x‖ = ‖y‖) :
    (rotationHaar d).map (fun O => rotationIsometry O x) =
      (rotationHaar d).map (fun O => rotationIsometry O y) := by
  obtain ⟨P, hP⟩ := exists_rotation_of_norm_eq h
  have hf : Measurable (fun O : Rotations d => rotationIsometry O x) := by fun_prop
  calc
    _ = ((rotationHaar d).map (· * P)).map (fun O => rotationIsometry O x) := by
      rw [map_mul_right_eq_self]
    _ = _ := by
      rw [Measure.map_map hf (by fun_prop)]
      congr 1
      ext O
      simp only [Function.comp_apply, rotationIsometry_mul, hP]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open ProbabilityTheory

@[simp] theorem rotationIsometry_one {d : ℕ} (x : Point d) :
    rotationIsometry (1 : Rotations d) x = x := by
  simp [rotationIsometry_apply]

@[simp] theorem rotationIsometry_inv_apply {d : ℕ} (O : Rotations d) (x : Point d) :
    rotationIsometry O⁻¹ x = (rotationIsometry O).symm x := by
  apply (rotationIsometry O).injective
  rw [← rotationIsometry_mul, mul_inv_cancel, rotationIsometry_one,
    LinearIsometryEquiv.apply_symm_apply]

theorem haar_inverse_orbit_eq {d : ℕ} {x y : Point d} (h : ‖x‖ = ‖y‖) :
    (rotationHaar d).map (fun O => (rotationIsometry O).symm x) =
      (rotationHaar d).map (fun O => (rotationIsometry O).symm y) := by
  simp_rw [← rotationIsometry_inv_apply]
  obtain ⟨P, hP⟩ := exists_rotation_of_norm_eq h
  have hf : Measurable (fun O : Rotations d => rotationIsometry O⁻¹ x) := by fun_prop
  calc
    _ = ((rotationHaar d).map (P⁻¹ * ·)).map (fun O => rotationIsometry O⁻¹ x) := by
      rw [map_mul_left_eq_self]
    _ = _ := by
      rw [Measure.map_map hf (by fun_prop)]
      congr 1
      ext O
      simp only [Function.comp_apply, _root_.mul_inv_rev, inv_inv, rotationIsometry_mul, hP]

theorem gaussian_radius_haar_direction {d : ℕ} {w : Point d} (hw : ‖w‖ = 1) :
    ((rotationHaar d).prod (stdGaussian (Point d))).map
      (fun p => ‖p.2‖ • (rotationIsometry p.1).symm w) = stdGaussian (Point d) := by
  have hf : Measurable (fun p : Rotations d × Point d =>
      ‖p.2‖ • (rotationIsometry p.1).symm w) := by
    simp_rw [← rotationIsometry_inv_apply]
    fun_prop
  have hg : Measurable (fun p : Rotations d × Point d =>
      (rotationIsometry p.1).symm p.2) := by
    simp_rw [← rotationIsometry_inv_apply]
    fun_prop
  calc
    _ = ((rotationHaar d).prod (stdGaussian (Point d))).map
        (fun p => (rotationIsometry p.1).symm p.2) := by
      apply map_prod_eq_of_fiber_law hf hg
      intro y
      have hxy : ‖(‖y‖ • w)‖ = ‖y‖ := by simp [norm_smul, hw]
      have h := haar_inverse_orbit_eq hxy
      simpa only [map_smul] using h
    _ = _ := by
      apply map_prod_eq_of_constant_fiber_law hg
      intro O
      exact stdGaussian_map (rotationIsometry O).symm

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace

def vectorStabilizer {d : ℕ} (w : Point d) : Subgroup (Rotations d) where
  carrier := {O | rotationIsometry O w = w}
  one_mem' := rotationIsometry_one w
  mul_mem' := by
    intro O P hO hP
    simp only [Set.mem_ofPred_eq] at *
    rw [rotationIsometry_mul, hP, hO]
  inv_mem' := by
    intro O hO
    simp only [Set.mem_ofPred_eq] at *
    rw [rotationIsometry_inv_apply]
    exact (rotationIsometry O).symm_apply_eq.mpr hO.symm

@[simp] theorem mem_vectorStabilizer {d : ℕ} (w : Point d) (O : Rotations d) :
    O ∈ vectorStabilizer w ↔ rotationIsometry O w = w := Iff.rfl

theorem vectorStabilizer_isClosed {d : ℕ} (w : Point d) :
    IsClosed (vectorStabilizer w : Set (Rotations d)) :=
  isClosed_eq (by fun_prop) continuous_const

instance vectorStabilizer_compactSpace {d : ℕ} (w : Point d) :
    CompactSpace (vectorStabilizer w) :=
  isCompact_iff_compactSpace.mp (vectorStabilizer_isClosed w).isCompact

def vectorStabilizerHaar {d : ℕ} (w : Point d) : Measure (vectorStabilizer w) :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ :
    PositiveCompacts (vectorStabilizer w))

instance vectorStabilizerHaar_probability {d : ℕ} (w : Point d) :
    IsProbabilityMeasure (vectorStabilizerHaar w) := by
  constructor
  exact Measure.haarMeasure_self

instance vectorStabilizerHaar_isHaar {d : ℕ} (w : Point d) :
    (vectorStabilizerHaar w).IsHaarMeasure := by
  unfold vectorStabilizerHaar
  infer_instance

def sphereSection {d : ℕ} (w v : Point d) : Rotations d :=
  rotationFromIsometry (Submodule.reflection (ℝ ∙ (w-v))ᗮ)

@[simp] theorem sphereSection_apply {d : ℕ} (w v x : Point d) :
    rotationIsometry (sphereSection w v) x =
      x - (2 * (inner ℝ (w-v) x / ‖w-v‖^2)) • (w-v) := by
  rw [sphereSection, rotationIsometry_from, Submodule.reflection_orthogonal_apply,
    Submodule.reflection_singleton_apply]
  simp only [neg_sub, two_smul, two_mul, add_smul, RCLike.ofReal_real_eq_id, id_eq]

theorem sphereSection_sends {d : ℕ} {w v : Point d} (h : ‖w‖ = ‖v‖) :
    rotationIsometry (sphereSection w v) w = v := by
  rw [sphereSection, rotationIsometry_from]
  exact Submodule.reflection_sub h

theorem rotation_entry_eq {d : ℕ} (O : Rotations d) (i j : Fin d) :
    (O : Matrix (Fin d) (Fin d) ℝ) i j =
      (rotationIsometry O (EuclideanSpace.single j 1)) i := by
  simp [rotationIsometry_apply, EuclideanSpace.single]

@[fun_prop] theorem measurable_sphereSection {d : ℕ} :
    Measurable (fun p : Point d × Point d => sphereSection p.1 p.2) := by
  let : MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (MeasurableSpace (Fin d → Fin d → ℝ))
  let : BorelSpace (Matrix (Fin d) (Fin d) ℝ) :=
    inferInstanceAs (BorelSpace (Fin d → Fin d → ℝ))
  have he : IsClosedEmbedding (fun O : Rotations d => (O : Matrix (Fin d) (Fin d) ℝ)) :=
    (isClosed_unitary (R := Matrix (Fin d) (Fin d) ℝ)).isClosedEmbedding_subtypeVal
  apply he.measurableEmbedding.measurable_comp_iff.mp
  apply Measurable.of_eval
  intro i
  apply Measurable.of_eval
  intro j
  change Measurable (fun p : Point d × Point d =>
    (sphereSection p.1 p.2 : Matrix (Fin d) (Fin d) ℝ) i j)
  simp_rw [rotation_entry_eq, sphereSection_apply]
  fun_prop

@[fun_prop] theorem measurable_sphereSection_left {d : ℕ} (w : Point d) :
    Measurable (sphereSection w) := by
  have measurable_pair : Measurable (fun vector : Point d => (w, vector)) :=
    measurable_const.prodMk measurable_id
  have measurable_composition : Measurable
      ((fun pair : Point d × Point d => sphereSection pair.1 pair.2) ∘
        (fun vector : Point d => (w, vector))) :=
    (measurable_sphereSection (d := d)).comp measurable_pair
  exact measurable_composition

def sectionCocycle {d : ℕ} (w : Point d) (P : Rotations d) (v : Point d)
    (hv : ‖v‖ = ‖w‖) : vectorStabilizer w :=
  ⟨(sphereSection w (rotationIsometry P v))⁻¹ * P * sphereSection w v, by
    apply (mem_vectorStabilizer _ _).mpr
    rw [rotationIsometry_mul, rotationIsometry_mul, sphereSection_sends hv.symm]
    rw [rotationIsometry_inv_apply]
    apply (rotationIsometry _).symm_apply_eq.mpr
    symm
    apply sphereSection_sends
    rw [LinearIsometryEquiv.norm_map, hv]⟩

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
