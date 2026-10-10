import Mathlib
import OAI.Probability.LogConcave.LowerBounds.RotationIsometry
import OAI.Probability.LogConcave.Sampling.MapProdSecondFiber

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

def revealRotation {d : ℕ} (w : Point d)
    (p : Rotations d × vectorStabilizer w) : Rotations d :=
  sphereSection w (rotationIsometry p.1 w) * p.2.1

@[fun_prop] theorem measurable_revealRotation {d : ℕ} (w : Point d) :
    Measurable (revealRotation w) := by
  unfold revealRotation
  apply Measurable.mul
  · exact (measurable_sphereSection_left w).comp (by fun_prop)
  · exact continuous_subtype_val.measurable.comp measurable_snd

theorem revealRotation_sends {d : ℕ} (w : Point d)
    (p : Rotations d × vectorStabilizer w) :
    rotationIsometry (revealRotation w p) w = rotationIsometry p.1 w := by
  rw [revealRotation, rotationIsometry_mul, p.2.property]
  exact sphereSection_sends (LinearIsometryEquiv.norm_map _ _).symm

theorem revealRotation_law {d : ℕ} (w : Point d) :
    ((rotationHaar d).prod (vectorStabilizerHaar w)).map (revealRotation w) =
      rotationHaar d := by
  let ν := ((rotationHaar d).prod (vectorStabilizerHaar w)).map (revealRotation w)
  have hν : IsProbabilityMeasure ν :=
    inferInstance
  have hi : ν.IsMulLeftInvariant := by
    constructor
    intro P
    change ν.map (P * ·) = ν
    dsimp only [ν]
    rw [Measure.map_map (by fun_prop) (measurable_revealRotation w)]
    calc
      _ = ((rotationHaar d).prod (vectorStabilizerHaar w)).map
          (fun p => sphereSection w (rotationIsometry P (rotationIsometry p.1 w)) * p.2.1) := by
        apply map_prod_eq_of_second_fiber_law (by fun_prop) (by fun_prop)
        intro T
        let C := sectionCocycle w P (rotationIsometry T w) (LinearIsometryEquiv.norm_map _ _)
        have hg : Measurable (fun h : vectorStabilizer w =>
            sphereSection w (rotationIsometry P (rotationIsometry T w)) * h.1) := by fun_prop
        calc
          _ = ((vectorStabilizerHaar w).map (C * ·)).map
              (fun h => sphereSection w (rotationIsometry P (rotationIsometry T w)) * h.1) := by
            rw [Measure.map_map hg (by fun_prop)]
            congr 1
            ext h
            simp only [Function.comp_apply, revealRotation, Subgroup.coe_mul, C, sectionCocycle]
            group
          _ = _ := by rw [map_mul_left_eq_self]
      _ = ((rotationHaar d).prod (vectorStabilizerHaar w)).map (revealRotation w) := by
        apply map_prod_eq_of_fiber_law (by fun_prop) (measurable_revealRotation w)
        intro h
        calc
          _ = ((rotationHaar d).map (P * ·)).map
              (fun T => revealRotation w (T,h)) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            congr 1
            ext T
            simp only [Function.comp_apply, revealRotation, rotationIsometry_mul]
          _ = _ := by rw [map_mul_left_eq_self]
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace ν (rotationHaar d)
  have hm := congrArg (fun μ : Measure (Rotations d) => μ Set.univ) h
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hm
  have hc : ν.haarScalarFactor (rotationHaar d) = 1 := ENNReal.coe_injective hm.symm
  rw [hc, one_smul] at h
  exact h

theorem haar_single_vector_revelation {d : ℕ} (w : Point d) :
    ((rotationHaar d).prod (vectorStabilizerHaar w)).map
      (fun p => (rotationIsometry p.1 w, revealRotation w p)) =
    (rotationHaar d).map (fun O => (rotationIsometry O w, O)) := by
  calc
    _ = (((rotationHaar d).prod (vectorStabilizerHaar w)).map (revealRotation w)).map
        (fun O => (rotationIsometry O w, O)) := by
      rw [Measure.map_map (by fun_prop) (measurable_revealRotation w)]
      congr 1
      funext p
      exact Prod.ext (revealRotation_sends w p).symm rfl
    _ = _ := by rw [revealRotation_law]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open ProbabilityTheory
open scoped RealInnerProductSpace

def subspaceStabilizer {d : ℕ} (E : Submodule ℝ (Point d)) : Subgroup (Rotations d) where
  carrier := {O | ∀ x ∈ E, rotationIsometry O x = x}
  one_mem' := by intro x _; exact rotationIsometry_one x
  mul_mem' := by
    intro O P hO hP x hx
    rw [rotationIsometry_mul, hP x hx, hO x hx]
  inv_mem' := by
    intro O hO x hx
    rw [rotationIsometry_inv_apply]
    exact (rotationIsometry O).symm_apply_eq.mpr (hO x hx).symm

@[simp] theorem mem_subspaceStabilizer {d : ℕ} (E : Submodule ℝ (Point d)) (O : Rotations d) :
    O ∈ subspaceStabilizer E ↔ ∀ x ∈ E, rotationIsometry O x = x := Iff.rfl

theorem subspaceStabilizer_isClosed {d : ℕ} (E : Submodule ℝ (Point d)) :
    IsClosed (subspaceStabilizer E : Set (Rotations d)) := by
  have he : (subspaceStabilizer E : Set (Rotations d)) =
      ⋂ x : E, {O : Rotations d | rotationIsometry O x = x} := by
    ext O
    simp only [Set.mem_iInter, Set.mem_ofPred_eq]
    exact ⟨fun h x => h x x.property, fun h x hx => h ⟨x,hx⟩⟩
  rw [he]
  exact isClosed_iInter (fun _ => isClosed_eq (by fun_prop) continuous_const)

instance subspaceStabilizer_compactSpace {d : ℕ} (E : Submodule ℝ (Point d)) :
    CompactSpace (subspaceStabilizer E) :=
  isCompact_iff_compactSpace.mp (subspaceStabilizer_isClosed E).isCompact

instance subspaceStabilizer_secondCountable {d : ℕ} (E : Submodule ℝ (Point d)) :
    SecondCountableTopology (subspaceStabilizer E) :=
  (Topology.IsEmbedding.subtypeVal (p := fun O : Rotations d =>
    O ∈ subspaceStabilizer E)).isInducing.secondCountableTopology

instance subspaceStabilizer_measurableMul {d : ℕ} (E : Submodule ℝ (Point d)) :
    MeasurableMul₂ (subspaceStabilizer E) := ⟨continuous_mul.measurable⟩

instance subspaceStabilizer_measurableInv {d : ℕ} (E : Submodule ℝ (Point d)) :
    MeasurableInv (subspaceStabilizer E) := ⟨continuous_inv.measurable⟩

def subspaceHaar {d : ℕ} (E : Submodule ℝ (Point d)) : Measure (subspaceStabilizer E) :=
  Measure.haarMeasure (⟨⟨Set.univ, isCompact_univ⟩, by simp⟩ :
    PositiveCompacts (subspaceStabilizer E))

instance subspaceHaar_probability {d : ℕ} (E : Submodule ℝ (Point d)) :
    IsProbabilityMeasure (subspaceHaar E) := ⟨Measure.haarMeasure_self⟩

instance subspaceHaar_isHaar {d : ℕ} (E : Submodule ℝ (Point d)) :
    (subspaceHaar E).IsHaarMeasure := by
  unfold subspaceHaar
  infer_instance

instance subspaceHaar_rightInvariant {d : ℕ} (E : Submodule ℝ (Point d)) :
    (subspaceHaar E).IsMulRightInvariant := by
  constructor
  intro P
  have : IsProbabilityMeasure ((subspaceHaar E).map (· * P)) :=
    inferInstance
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace
    ((subspaceHaar E).map (· * P)) (subspaceHaar E)
  have hm := congrArg (fun μ : Measure (subspaceStabilizer E) => μ Set.univ) h
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hm
  have hc : ((subspaceHaar E).map (· * P)).haarScalarFactor (subspaceHaar E) = 1 :=
    ENNReal.coe_injective hm.symm
  rw [hc, one_smul] at h
  exact h

lemma stabilizer_map_orthogonal {d : ℕ} (E : Submodule ℝ (Point d))
    (O : subspaceStabilizer E) {x : Point d} (hx : x ∈ Eᗮ) :
    rotationIsometry O.1 x ∈ Eᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  have hf := O.property y hy
  rw [← hf, LinearIsometryEquiv.inner_map_map]
  exact E.inner_right_of_mem_orthogonal hy hx

def complementIsometry {d : ℕ} (E : Submodule ℝ (Point d))
    (O : subspaceStabilizer E) : Eᗮ ≃ₗᵢ[ℝ] Eᗮ where
  toFun x := ⟨rotationIsometry O.1 x, stabilizer_map_orthogonal E O x.property⟩
  invFun x := ⟨rotationIsometry (O⁻¹).1 x, stabilizer_map_orthogonal E (O⁻¹) x.property⟩
  left_inv x := by
    apply Subtype.ext
    change rotationIsometry (O.1)⁻¹ (rotationIsometry O.1 (x : Point d)) = (x : Point d)
    rw [rotationIsometry_inv_apply, LinearIsometryEquiv.symm_apply_apply]
  right_inv x := by
    apply Subtype.ext
    change rotationIsometry O.1 (rotationIsometry (O.1)⁻¹ (x : Point d)) = (x : Point d)
    rw [rotationIsometry_inv_apply, LinearIsometryEquiv.apply_symm_apply]
  map_add' x y := by apply Subtype.ext; exact map_add (rotationIsometry O.1) (x : Point d) (y : Point d)
  map_smul' c x := by apply Subtype.ext; exact map_smul (rotationIsometry O.1) c (x : Point d)
  norm_map' x := (rotationIsometry O.1).norm_map x

@[simp] theorem complementIsometry_apply_coe {d : ℕ} (E : Submodule ℝ (Point d))
    (O : subspaceStabilizer E) (x : Eᗮ) :
    (complementIsometry E O x : Point d) = rotationIsometry O.1 x := rfl

@[fun_prop] theorem continuous_complementIsometry_apply {d : ℕ} (E : Submodule ℝ (Point d)) :
    Continuous (fun p : subspaceStabilizer E × Eᗮ => complementIsometry E p.1 p.2) := by
  have h₁ : Continuous (fun p : subspaceStabilizer E × Eᗮ => (p.1.1, (p.2 : Point d))) :=
    (continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)
  have h₂ := (continuous_rotation_apply (d := d)).comp h₁
  exact h₂.subtype_mk _

lemma sphereSection_mem_subspaceStabilizer {d : ℕ} (E : Submodule ℝ (Point d))
    {x y : Point d} (hx : x ∈ Eᗮ) (hy : y ∈ Eᗮ) :
    sphereSection x y ∈ subspaceStabilizer E := by
  intro z hz
  rw [sphereSection_apply, E.inner_left_of_mem_orthogonal hz (Eᗮ.sub_mem hx hy)]
  simp

def complementSection {d : ℕ} (E : Submodule ℝ (Point d)) (x y : Eᗮ) :
    subspaceStabilizer E :=
  ⟨sphereSection x y, sphereSection_mem_subspaceStabilizer E x.property y.property⟩

theorem measurable_complementSection {d : ℕ} (E : Submodule ℝ (Point d)) :
    Measurable (fun p : Eᗮ × Eᗮ => complementSection E p.1 p.2) := by
  have h₁ : Measurable (fun p : Eᗮ × Eᗮ => ((p.1 : Point d), (p.2 : Point d))) :=
    (measurable_subtype_coe.comp measurable_fst).prodMk
      (measurable_subtype_coe.comp measurable_snd)
  have h₂ := (measurable_sphereSection (d := d)).comp h₁
  exact h₂.subtype_mk

lemma complementSection_sends {d : ℕ} (E : Submodule ℝ (Point d)) {x y : Eᗮ}
    (h : ‖x‖ = ‖y‖) : complementIsometry E (complementSection E x y) x = y := by
  apply Subtype.ext
  exact sphereSection_sends h

@[simp] theorem complementIsometry_mul {d : ℕ} (E : Submodule ℝ (Point d))
    (O P : subspaceStabilizer E) (x : Eᗮ) :
    complementIsometry E (O * P) x = complementIsometry E O (complementIsometry E P x) := by
  apply Subtype.ext
  exact rotationIsometry_mul O.1 P.1 x

@[simp] theorem complementIsometry_inv {d : ℕ} (E : Submodule ℝ (Point d))
    (O : subspaceStabilizer E) (x : Eᗮ) :
    complementIsometry E (O⁻¹) x = (complementIsometry E O).symm x := rfl

lemma complement_haar_orbit_eq {d : ℕ} (E : Submodule ℝ (Point d)) {x y : Eᗮ}
    (h : ‖x‖ = ‖y‖) :
    (subspaceHaar E).map (fun O => complementIsometry E O x) =
    (subspaceHaar E).map (fun O => complementIsometry E O y) := by
  let P := complementSection E x y
  have hP : complementIsometry E P x = y := complementSection_sends E h
  calc
    _ = ((subspaceHaar E).map (· * P)).map (fun O => complementIsometry E O x) := by
      rw [map_mul_right_eq_self]
    _ = _ := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1
      funext O
      change complementIsometry E (O * P) x = complementIsometry E O y
      rw [complementIsometry_mul, hP]

theorem complementary_gaussian_radius_haar_direction {d : ℕ}
    (E : Submodule ℝ (Point d)) {w : Eᗮ} (hw : ‖w‖ = 1) :
    ((subspaceHaar E).prod (stdGaussian Eᗮ)).map
      (fun p => ‖p.2‖ • complementIsometry E p.1 w) = stdGaussian Eᗮ := by
  have hf : Measurable (fun p : subspaceStabilizer E × Eᗮ =>
      ‖p.2‖ • complementIsometry E p.1 w) := by fun_prop
  have hg : Measurable (fun p : subspaceStabilizer E × Eᗮ =>
      complementIsometry E p.1 p.2) := by fun_prop
  calc
    _ = ((subspaceHaar E).prod (stdGaussian Eᗮ)).map
        (fun p => complementIsometry E p.1 p.2) := by
      apply map_prod_eq_of_fiber_law hf hg
      intro y
      have hxy : ‖(‖y‖ • w)‖ = ‖y‖ := by simp [norm_smul, hw]
      have h := complement_haar_orbit_eq E hxy
      simpa only [map_smul] using h
    _ = _ := by
      apply map_prod_eq_of_constant_fiber_law hg
      intro O
      exact stdGaussian_map (complementIsometry E O)

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace

lemma stabilizer_sup_line {d : ℕ} (E : Submodule ℝ (Point d)) (w : Point d)
    {O : Rotations d} (hE : O ∈ subspaceStabilizer E) (hw : rotationIsometry O w = w) :
    O ∈ subspaceStabilizer (E ⊔ ℝ ∙ w) := by
  intro x hx
  rcases Submodule.mem_sup.mp hx with ⟨a,ha,b,hb,rfl⟩
  rcases Submodule.mem_span_singleton.mp hb with ⟨c,rfl⟩
  rw [map_add, hE a ha, map_smul, hw]

def residualInclusion {d : ℕ} (E : Submodule ℝ (Point d)) (w : Point d)
    (O : subspaceStabilizer (E ⊔ ℝ ∙ w)) : subspaceStabilizer E :=
  ⟨O.1, fun x hx => O.property x ((show E ≤ E ⊔ ℝ ∙ w from le_sup_left) hx)⟩

@[fun_prop] theorem continuous_residualInclusion {d : ℕ}
    (E : Submodule ℝ (Point d)) (w : Point d) : Continuous (residualInclusion E w) := by
  exact continuous_subtype_val.subtype_mk _

@[simp] theorem residualInclusion_mul {d : ℕ} (E : Submodule ℝ (Point d)) (w : Point d)
    (O P : subspaceStabilizer (E ⊔ ℝ ∙ w)) :
    residualInclusion E w (O * P) = residualInclusion E w O * residualInclusion E w P := rfl

lemma residualInclusion_fixes {d : ℕ} (E : Submodule ℝ (Point d)) (w : Eᗮ)
    (O : subspaceStabilizer (E ⊔ ℝ ∙ (w : Point d))) :
    complementIsometry E (residualInclusion E w O) w = w := by
  apply Subtype.ext
  exact O.property w ((show ℝ ∙ (w : Point d) ≤ E ⊔ ℝ ∙ (w : Point d) from le_sup_right)
    (Submodule.mem_span_singleton_self _))

def complementCocycle {d : ℕ} (E : Submodule ℝ (Point d)) (w : Eᗮ)
    (P : subspaceStabilizer E) (v : Eᗮ) (hv : ‖v‖ = ‖w‖) :
    subspaceStabilizer (E ⊔ ℝ ∙ (w : Point d)) :=
  ⟨((complementSection E w (complementIsometry E P v))⁻¹ * P *
      complementSection E w v).1, by
    apply stabilizer_sup_line E w
    · exact ((complementSection E w (complementIsometry E P v))⁻¹ * P *
        complementSection E w v).property
    · have he : complementIsometry E
          ((complementSection E w (complementIsometry E P v))⁻¹ * P *
            complementSection E w v) w = w := by
        rw [complementIsometry_mul, complementIsometry_mul, complementSection_sends E hv.symm,
          complementIsometry_inv]
        apply (complementIsometry E _).symm_apply_eq.mpr
        symm
        apply complementSection_sends
        rw [LinearIsometryEquiv.norm_map, hv]
      exact congrArg Subtype.val he⟩

@[fun_prop] theorem measurable_complementSection_left {d : ℕ}
    (E : Submodule ℝ (Point d)) (w : Eᗮ) : Measurable (complementSection E w) := by
  have hg : Measurable (fun v : Eᗮ => (w,v)) := measurable_const.prodMk measurable_id
  have h := (measurable_complementSection E).comp hg
  exact h

def revealComplement {d : ℕ} (E : Submodule ℝ (Point d)) (w : Eᗮ)
    (p : subspaceStabilizer E × subspaceStabilizer (E ⊔ ℝ ∙ (w : Point d))) :
    subspaceStabilizer E :=
  complementSection E w (complementIsometry E p.1 w) * residualInclusion E w p.2

@[fun_prop] theorem measurable_revealComplement {d : ℕ}
    (E : Submodule ℝ (Point d)) (w : Eᗮ) : Measurable (revealComplement E w) := by
  unfold revealComplement
  apply Measurable.mul
  · exact (measurable_complementSection_left E w).comp (by fun_prop)
  · exact (continuous_residualInclusion E w).measurable.comp measurable_snd

lemma revealComplement_sends {d : ℕ} (E : Submodule ℝ (Point d)) (w : Eᗮ)
    (p : subspaceStabilizer E × subspaceStabilizer (E ⊔ ℝ ∙ (w : Point d))) :
    complementIsometry E (revealComplement E w p) w = complementIsometry E p.1 w := by
  rw [revealComplement, complementIsometry_mul, residualInclusion_fixes]
  exact complementSection_sends E (LinearIsometryEquiv.norm_map _ _).symm

theorem revealComplement_law {d : ℕ} (E : Submodule ℝ (Point d)) (w : Eᗮ) :
    ((subspaceHaar E).prod (subspaceHaar (E ⊔ ℝ ∙ (w : Point d)))).map
      (revealComplement E w) = subspaceHaar E := by
  let ν := ((subspaceHaar E).prod (subspaceHaar (E ⊔ ℝ ∙ (w : Point d)))).map
    (revealComplement E w)
  have hν : IsProbabilityMeasure ν :=
    inferInstance
  have hi : ν.IsMulLeftInvariant := by
    constructor
    intro P
    change ν.map (P * ·) = ν
    dsimp only [ν]
    have hf : Measurable (fun p : subspaceStabilizer E ×
        subspaceStabilizer (E ⊔ ℝ ∙ (w : Point d)) =>
        complementSection E w (complementIsometry E P (complementIsometry E p.1 w)) *
          residualInclusion E w p.2) := by
      apply Measurable.mul
      · exact (measurable_complementSection_left E w).comp (by fun_prop)
      · exact (continuous_residualInclusion E w).measurable.comp measurable_snd
    rw [Measure.map_map (by fun_prop) (measurable_revealComplement E w)]
    calc
      _ = ((subspaceHaar E).prod (subspaceHaar (E ⊔ ℝ ∙ (w : Point d)))).map
          (fun p => complementSection E w (complementIsometry E P (complementIsometry E p.1 w)) *
            residualInclusion E w p.2) := by
        apply map_prod_eq_of_second_fiber_law (by fun_prop) hf
        intro T
        let C := complementCocycle E w P (complementIsometry E T w)
          (LinearIsometryEquiv.norm_map _ _)
        have hg : Measurable (fun h : subspaceStabilizer (E ⊔ ℝ ∙ (w : Point d)) =>
            complementSection E w (complementIsometry E P (complementIsometry E T w)) *
              residualInclusion E w h) := by fun_prop
        calc
          _ = ((subspaceHaar (E ⊔ ℝ ∙ (w : Point d))).map (C * ·)).map
              (fun h => complementSection E w (complementIsometry E P (complementIsometry E T w)) *
                residualInclusion E w h) := by
            rw [Measure.map_map hg (by fun_prop)]
            congr 1
            funext h
            apply Subtype.ext
            simp only [Function.comp_apply, revealComplement, Subgroup.coe_mul,
              C, complementCocycle, residualInclusion, Subgroup.coe_inv]
            group
          _ = _ := by rw [map_mul_left_eq_self]
      _ = ((subspaceHaar E).prod (subspaceHaar (E ⊔ ℝ ∙ (w : Point d)))).map
          (revealComplement E w) := by
        apply map_prod_eq_of_fiber_law hf (measurable_revealComplement E w)
        intro h
        calc
          _ = ((subspaceHaar E).map (P * ·)).map (fun T => revealComplement E w (T,h)) := by
            rw [Measure.map_map (by fun_prop) (by fun_prop)]
            congr 1
            funext T
            simp only [Function.comp_apply, revealComplement, complementIsometry_mul]
          _ = _ := by rw [map_mul_left_eq_self]
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace ν (subspaceHaar E)
  have hm := congrArg (fun μ : Measure (subspaceStabilizer E) => μ Set.univ) h
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hm
  have hc : ν.haarScalarFactor (subspaceHaar E) = 1 := ENNReal.coe_injective hm.symm
  rw [hc, one_smul] at h
  exact h

theorem haar_complement_single_vector_revelation {d : ℕ}
    (E : Submodule ℝ (Point d)) (w : Eᗮ) :
    ((subspaceHaar E).prod (subspaceHaar (E ⊔ ℝ ∙ (w : Point d)))).map
      (fun p => (complementIsometry E p.1 w, revealComplement E w p)) =
    (subspaceHaar E).map (fun O => (complementIsometry E O w, O)) := by
  calc
    _ = (((subspaceHaar E).prod (subspaceHaar (E ⊔ ℝ ∙ (w : Point d)))).map
        (revealComplement E w)).map (fun O => (complementIsometry E O w, O)) := by
      rw [Measure.map_map (by fun_prop) (measurable_revealComplement E w)]
      congr 1
      funext p
      exact Prod.ext (revealComplement_sends E w p).symm rfl
    _ = _ := by rw [revealComplement_law]

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
