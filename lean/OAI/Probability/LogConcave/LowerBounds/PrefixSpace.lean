import Mathlib
import OAI.Probability.LogConcave.LowerBounds.RevealRotation
import OAI.Probability.LogConcave.Sampling.NormalizedDirection

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
open ProbabilityTheory

theorem complementary_gaussian_direction_law {d : ℕ} (E : Submodule ℝ (Point d))
    {w : Eᗮ} (hw : ‖w‖ = 1) :
    (stdGaussian Eᗮ).map (normalizedDirection w) =
      (subspaceHaar E).map (fun O => complementIsometry E O w) := by
  have hn := ae_stdGaussian_ne_zero_of_unit hw
  have hp : ∀ᵐ p ∂(subspaceHaar E).prod (stdGaussian Eᗮ), p.2 ≠ 0 :=
    Measure.quasiMeasurePreserving_snd.ae hn
  calc
    _ = (((subspaceHaar E).prod (stdGaussian Eᗮ)).map
        (fun p => ‖p.2‖ • complementIsometry E p.1 w)).map (normalizedDirection w) := by
      rw [complementary_gaussian_radius_haar_direction E hw]
    _ = ((subspaceHaar E).prod (stdGaussian Eᗮ)).map
        (fun p => complementIsometry E p.1 w) := by
      rw [Measure.map_map (measurable_normalizedDirection w) (by fun_prop)]
      apply Measure.map_congr
      filter_upwards [hp] with p hp
      exact normalizedDirection_scale (by simpa using hw) (norm_pos_iff.mpr hp)
    _ = _ := by
      change Measure.map ((fun O => complementIsometry E O w) ∘ Prod.fst) _ = _
      rw [← Measure.map_map (f := Prod.fst) (g := fun O => complementIsometry E O w)
        (by fun_prop) measurable_fst]
      simp

theorem projected_gaussian_direction_law {d : ℕ} (E : Submodule ℝ (Point d))
    {w : Eᗮ} (hw : ‖w‖ = 1) :
    (stdGaussian (Point d)).map
      (fun g => normalizedDirection w (Eᗮ.orthogonalProjectionOnto g)) =
      (subspaceHaar E).map (fun O => complementIsometry E O w) := by
  change Measure.map (normalizedDirection w ∘ Eᗮ.orthogonalProjectionOnto) _ = _
  rw [← Measure.map_map (f := Eᗮ.orthogonalProjectionOnto)
    (g := normalizedDirection w) (measurable_normalizedDirection w) (by fun_prop),
    stdGaussian_orthogonalProjection, complementary_gaussian_direction_law E hw]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling
namespace LowerBound

def prefixSpace (d k : ℕ) : Submodule ℝ (Point d) where
  carrier := {x | ∀ i : Fin d, k ≤ i.val → x i = 0}
  zero_mem' := by intro i _; rfl
  add_mem' := by intro x y hx hy i hi; simp [hx i hi, hy i hi]
  smul_mem' := by intro c x hx i hi; simp [hx i hi]

@[simp] theorem mem_prefixSpace {d k : ℕ} (x : Point d) :
    x ∈ prefixSpace d k ↔ ∀ i : Fin d, k ≤ i.val → x i = 0 := Iff.rfl

def coordinateVector {d : ℕ} (i : Fin d) : Point d := EuclideanSpace.single i 1

@[simp] theorem coordinateVector_apply {d : ℕ} (i j : Fin d) :
    coordinateVector i j = if j = i then 1 else 0 := by
  simp [coordinateVector, eq_comm]

@[simp] theorem coordinateVector_norm {d : ℕ} (i : Fin d) : ‖coordinateVector i‖ = 1 := by
  simp [coordinateVector]

@[simp] theorem inner_coordinateVector {d : ℕ} (i : Fin d) (x : Point d) :
    inner ℝ (coordinateVector i) x = x i := by
  simp [coordinateVector, EuclideanSpace.inner_single_left]

@[simp] theorem prefixSpace_zero (d : ℕ) : prefixSpace d 0 = ⊥ := by
  ext x
  simp only [mem_prefixSpace, zero_le, forall_true_left, Submodule.mem_bot]
  exact ⟨fun h => by ext i; exact h i, fun h i => by simp [h]⟩

lemma prefixSpace_mono (d : ℕ) {k l : ℕ} (hkl : k ≤ l) :
    prefixSpace d k ≤ prefixSpace d l := by
  intro x hx i hi
  exact hx i (hkl.trans hi)

lemma coordinateVector_orthogonal_prefix {d k : ℕ} (hk : k < d) :
    coordinateVector ⟨k,hk⟩ ∈ (prefixSpace d k)ᗮ := by
  rw [Submodule.mem_orthogonal']
  intro y hy
  rw [inner_coordinateVector]
  exact hy ⟨k,hk⟩ le_rfl

lemma prefixSpace_succ {d k : ℕ} (hk : k < d) :
    prefixSpace d (k+1) = prefixSpace d k ⊔ ℝ ∙ coordinateVector ⟨k,hk⟩ := by
  apply le_antisymm
  · intro x hx
    have ht : x - (x ⟨k,hk⟩) • coordinateVector ⟨k,hk⟩ ∈ prefixSpace d k := by
      intro i hi
      by_cases hik : i.val = k
      · have he : i = ⟨k,hk⟩ := Fin.ext hik
        simp [he]
      · have hki : k+1 ≤ i.val := by omega
        have hine : i ≠ ⟨k,hk⟩ := by intro h; apply hik; exact congrArg Fin.val h
        simp [hx i hki, coordinateVector_apply, hine]
    have hs : x ⟨k,hk⟩ • coordinateVector ⟨k,hk⟩ ∈ ℝ ∙ coordinateVector ⟨k,hk⟩ :=
      Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    convert (prefixSpace d k ⊔ ℝ ∙ coordinateVector ⟨k,hk⟩).add_mem
      ((le_sup_left : prefixSpace d k ≤ _ ) ht) ((le_sup_right : ℝ ∙ coordinateVector ⟨k,hk⟩ ≤ _) hs)
      using 1
    module
  · apply sup_le
    · exact prefixSpace_mono d (Nat.le_succ k)
    · apply Submodule.span_le.mpr
      intro x hx
      rcases Set.mem_singleton_iff.mp hx with rfl
      intro i hi
      have hine : i ≠ ⟨k,hk⟩ := by intro h; have := congrArg Fin.val h; dsimp at this; omega
      simp [coordinateVector_apply, hine]

def prefixProject {d : ℕ} (k : ℕ) (x : Point d) : Point d :=
  toLp 2 (fun i => if i.val < k then x i else 0)

@[simp] theorem prefixProject_apply {d : ℕ} (k : ℕ) (x : Point d) (i : Fin d) :
    prefixProject k x i = if i.val < k then x i else 0 := rfl

@[fun_prop] theorem continuous_prefixProject {d : ℕ} (k : ℕ) :
    Continuous (prefixProject (d := d) k) := by
  unfold prefixProject
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  split_ifs <;> fun_prop

lemma prefixProject_mem {d : ℕ} (k : ℕ) (x : Point d) :
    prefixProject k x ∈ prefixSpace d k := by
  intro i hi
  simp [prefixProject_apply, not_lt_of_ge hi]

lemma sub_prefixProject_mem_orthogonal {d : ℕ} (k : ℕ) (x : Point d) :
    x - prefixProject k x ∈ (prefixSpace d k)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro y hy
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  apply Finset.sum_eq_zero
  intro i _
  by_cases hi : i.val < k
  · simp [prefixProject_apply, hi]
  · simp [prefixProject_apply, hi, hy i (Nat.le_of_not_gt hi)]

lemma prefixProject_eq_projection {d : ℕ} (k : ℕ) (x : Point d) :
    prefixProject k x = (prefixSpace d k).starProjection x := by
  symm
  apply (Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (prefixProject_mem k x))
  intro y hy
  exact (prefixSpace d k).inner_left_of_mem_orthogonal hy
    (sub_prefixProject_mem_orthogonal k x)

end LowerBound
end LogConcaveSampling

namespace LogConcaveSampling.LowerBound
open ProbabilityTheory

instance subspaceHaar_invInvariant {d : ℕ} (E : Submodule ℝ (Point d)) :
    (subspaceHaar E).IsInvInvariant := by
  constructor
  have : IsProbabilityMeasure (subspaceHaar E).inv := by
    unfold Measure.inv
    infer_instance
  have h := Measure.isMulInvariant_eq_smul_of_compactSpace
    (subspaceHaar E).inv (subspaceHaar E)
  have hm := congrArg (fun μ : Measure (subspaceStabilizer E) => μ Set.univ) h
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hm
  have hc : (subspaceHaar E).inv.haarScalarFactor (subspaceHaar E) = 1 :=
    ENNReal.coe_injective hm.symm
  rw [hc, one_smul] at h
  exact h

def gaussianSection {d : ℕ} (E : Submodule ℝ (Point d)) (e : Eᗮ)
    (g : Point d) : subspaceStabilizer E :=
  complementSection E e (normalizedDirection e (Eᗮ.orthogonalProjectionOnto g))

@[fun_prop] theorem measurable_gaussianSection {d : ℕ}
    (E : Submodule ℝ (Point d)) (e : Eᗮ) : Measurable (gaussianSection E e) := by
  exact (measurable_complementSection_left E e).comp
    ((measurable_normalizedDirection e).comp (by fun_prop))

def gaussianForward {d : ℕ} (E : Submodule ℝ (Point d)) (e : Eᗮ)
    (p : Point d × subspaceStabilizer (E ⊔ ℝ ∙ (e : Point d))) : subspaceStabilizer E :=
  gaussianSection E e p.1 * residualInclusion E e p.2

@[fun_prop] theorem measurable_gaussianForward {d : ℕ}
    (E : Submodule ℝ (Point d)) (e : Eᗮ) : Measurable (gaussianForward E e) := by
  unfold gaussianForward
  exact ((measurable_gaussianSection E e).comp measurable_fst).mul
    ((continuous_residualInclusion E e).measurable.comp measurable_snd)

theorem gaussianForward_law {d : ℕ} (E : Submodule ℝ (Point d))
    {e : Eᗮ} (he : ‖e‖ = 1) :
    ((stdGaussian (Point d)).prod (subspaceHaar (E ⊔ ℝ ∙ (e : Point d)))).map
      (gaussianForward E e) = subspaceHaar E := by
  calc
    _ = ((subspaceHaar E).prod (subspaceHaar (E ⊔ ℝ ∙ (e : Point d)))).map
        (revealComplement E e) := by
      ext s hs
      rw [Measure.map_apply (measurable_gaussianForward E e) hs,
        Measure.map_apply (measurable_revealComplement E e) hs,
        Measure.prod_apply_symm (hs.preimage (measurable_gaussianForward E e)),
        Measure.prod_apply_symm (hs.preimage (measurable_revealComplement E e))]
      apply lintegral_congr
      intro h
      have hM : (stdGaussian (Point d)).map (fun g => gaussianForward E e (g,h)) =
          (subspaceHaar E).map (fun O => revealComplement E e (O,h)) := by
        have hm : Measurable (fun v : Eᗮ => complementSection E e v * residualInclusion E e h) :=
          (measurable_complementSection_left E e).mul_const _
        have hl := congrArg (fun μ : Measure Eᗮ => μ.map
          (fun v => complementSection E e v * residualInclusion E e h))
          (projected_gaussian_direction_law E he)
        rw [Measure.map_map hm (by fun_prop), Measure.map_map hm (by fun_prop)] at hl
        exact hl
      have ha := congrArg (fun μ : Measure (subspaceStabilizer E) => μ s) hM
      rw [Measure.map_apply (f := fun g => gaussianForward E e (g,h)) (by fun_prop) hs,
        Measure.map_apply (f := fun O => revealComplement E e (O,h)) (by fun_prop) hs] at ha
      exact ha
    _ = _ := revealComplement_law E e

def gaussianBackward {d : ℕ} (E : Submodule ℝ (Point d)) (e w : Eᗮ)
    (p : Point d × subspaceStabilizer (E ⊔ ℝ ∙ (e : Point d))) : subspaceStabilizer E :=
  complementSection E e w * residualInclusion E e p.2 * (gaussianSection E e p.1)⁻¹

@[fun_prop] theorem measurable_gaussianBackward {d : ℕ}
    (E : Submodule ℝ (Point d)) (e w : Eᗮ) : Measurable (gaussianBackward E e w) := by
  unfold gaussianBackward
  fun_prop

theorem gaussianBackward_law {d : ℕ} (E : Submodule ℝ (Point d))
    {e : Eᗮ} (he : ‖e‖ = 1) (w : Eᗮ) :
    ((stdGaussian (Point d)).prod (subspaceHaar (E ⊔ ℝ ∙ (e : Point d)))).map
      (gaussianBackward E e w) = subspaceHaar E := by
  calc
    _ = ((stdGaussian (Point d)).prod (subspaceHaar (E ⊔ ℝ ∙ (e : Point d)))).map
        (fun p => complementSection E e w * (gaussianForward E e p)⁻¹) := by
      apply map_prod_eq_of_second_fiber_law (measurable_gaussianBackward E e w) (by fun_prop)
      intro g
      calc
        _ = ((subspaceHaar (E ⊔ ℝ ∙ (e : Point d))).map Inv.inv).map
            (fun h => complementSection E e w * (gaussianForward E e (g,h))⁻¹) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          congr 1
          funext h
          apply Subtype.ext
          simp only [Function.comp_apply, gaussianForward, gaussianBackward,
            residualInclusion, Subgroup.coe_mul, Subgroup.coe_inv]
          group
        _ = _ := by rw [Measure.map_inv_eq_self]
    _ = (((stdGaussian (Point d)).prod (subspaceHaar (E ⊔ ℝ ∙ (e : Point d)))).map
        (gaussianForward E e)).map (fun O => complementSection E e w * O⁻¹) := by
      rw [Measure.map_map (by fun_prop) (measurable_gaussianForward E e)]
      rfl
    _ = _ := by
      rw [gaussianForward_law E he]
      simpa only [div_eq_mul_inv] using
        (Measure.map_div_left_eq_self (subspaceHaar E) (complementSection E e w))

lemma gaussianBackward_sends {d : ℕ} (E : Submodule ℝ (Point d))
    {e w : Eᗮ} (he : ‖e‖ = 1) (hw : ‖w‖ = 1)
    (p : Point d × subspaceStabilizer (E ⊔ ℝ ∙ (e : Point d))) :
    complementIsometry E (gaussianBackward E e w p)
      (normalizedDirection e (Eᗮ.orthogonalProjectionOnto p.1)) = w := by
  have hs := complementSection_sends E
    (show ‖e‖ = ‖normalizedDirection e (Eᗮ.orthogonalProjectionOnto p.1)‖ by simp [he])
  rw [gaussianBackward, complementIsometry_mul, complementIsometry_mul,
    complementIsometry_inv]
  have hi : (complementIsometry E (gaussianSection E e p.1)).symm
      (normalizedDirection e (Eᗮ.orthogonalProjectionOnto p.1)) = e :=
    (complementIsometry E (gaussianSection E e p.1)).symm_apply_eq.mpr hs.symm
  rw [hi, residualInclusion_fixes]
  exact complementSection_sends E (he.trans hw.symm)

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

def remainingHaar {d : ℕ} (E : Submodule ℝ (Point d)) : Measure (Rotations d) :=
  (subspaceHaar E).map Subtype.val

instance remainingHaar_probability {d : ℕ} (E : Submodule ℝ (Point d)) :
    IsProbabilityMeasure (remainingHaar E) := by
  unfold remainingHaar
  infer_instance

lemma remainingHaar_fixes {d : ℕ} (E : Submodule ℝ (Point d)) :
    ∀ᵐ H ∂remainingHaar E, H ∈ subspaceStabilizer E := by
  apply (ae_map_iff measurable_subtype_coe.aemeasurable
    (subspaceStabilizer_isClosed E).measurableSet).mpr
  exact Filter.Eventually.of_forall Subtype.property

def ambientBackward {d : ℕ} (E : Submodule ℝ (Point d)) (e w : Eᗮ)
    (p : Point d × Rotations d) : Rotations d :=
  (complementSection E e w).1 * p.2 * (gaussianSection E e p.1).1⁻¹

@[fun_prop] lemma measurable_ambientBackward {d : ℕ}
    (E : Submodule ℝ (Point d)) (e w : Eᗮ) : Measurable (ambientBackward E e w) := by
  unfold ambientBackward
  fun_prop

lemma ambientBackward_law {d : ℕ} (E : Submodule ℝ (Point d))
    {e : Eᗮ} (he : ‖e‖ = 1) (w : Eᗮ) :
    ((stdGaussian (Point d)).prod (remainingHaar (E ⊔ ℝ ∙ (e : Point d)))).map
      (ambientBackward E e w) = remainingHaar E := by
  have hp := Measure.map_prod_map (stdGaussian (Point d))
    (subspaceHaar (E ⊔ ℝ ∙ (e : Point d))) measurable_id measurable_subtype_coe
  rw [Measure.map_id] at hp
  unfold remainingHaar
  rw [hp, Measure.map_map (measurable_ambientBackward E e w) (by fun_prop)]
  calc
    _ = (((stdGaussian (Point d)).prod (subspaceHaar (E ⊔ ℝ ∙ (e : Point d)))).map
        (gaussianBackward E e w)).map Subtype.val := by
      rw [Measure.map_map measurable_subtype_coe (measurable_gaussianBackward E e w)]
      rfl
    _ = _ := by rw [gaussianBackward_law E he]

lemma ambientBackward_mem {d : ℕ} (E : Submodule ℝ (Point d)) (e w : Eᗮ)
    (g : Point d) {H : Rotations d} (hH : H ∈ subspaceStabilizer (E ⊔ ℝ ∙ (e : Point d))) :
    ambientBackward E e w (g,H) ∈ subspaceStabilizer E :=
  (gaussianBackward E e w (g,⟨H,hH⟩)).property

lemma ambientBackward_sends {d : ℕ} (E : Submodule ℝ (Point d))
    {e w : Eᗮ} (he : ‖e‖ = 1) (hw : ‖w‖ = 1) (g : Point d)
    {H : Rotations d} (hH : H ∈ subspaceStabilizer (E ⊔ ℝ ∙ (e : Point d))) :
    rotationIsometry (ambientBackward E e w (g,H))
      ((normalizedDirection e (Eᗮ.orthogonalProjectionOnto g) : Eᗮ) : Point d) = (w : Point d) :=
  congrArg Subtype.val (gaussianBackward_sends E he hw (g,⟨H,hH⟩))

def prefixUnit {d k : ℕ} (hk : k < d) : (prefixSpace d k)ᗮ :=
  ⟨coordinateVector ⟨k,hk⟩, coordinateVector_orthogonal_prefix hk⟩

@[simp] lemma norm_prefixUnit {d k : ℕ} (hk : k < d) : ‖prefixUnit hk‖ = 1 := by
  exact coordinateVector_norm _

abbrev Frames (d : ℕ) := Rotations d × Rotations d

def frameCompletion {d : ℕ} (F : Frames d) (H : Rotations d) : Rotations d :=
  F.1 * H * F.2⁻¹

@[fun_prop] lemma measurable_frameCompletion {d : ℕ} :
    Measurable (fun p : Frames d × Rotations d => frameCompletion p.1 p.2) := by
  unfold frameCompletion
  fun_prop

def flagDirection {d k : ℕ} (hk : k < d) (x : Point d) : (prefixSpace d k)ᗮ :=
  normalizedDirection (prefixUnit hk) ((prefixSpace d k)ᗮ.orthogonalProjectionOnto x)

@[fun_prop] lemma measurable_flagDirection {d k : ℕ} (hk : k < d) :
    Measurable (flagDirection hk) := by
  exact (measurable_normalizedDirection _).comp (by fun_prop)

@[simp] lemma norm_flagDirection {d k : ℕ} (hk : k < d) (x : Point d) :
    ‖flagDirection hk x‖ = 1 := norm_normalizedDirection (norm_prefixUnit hk) _

def inverseFrameUpdate {d k : ℕ} (hk : k < d) (F : Frames d) (x g : Point d) : Frames d :=
  (F.1 * (complementSection (prefixSpace d k) (prefixUnit hk)
      (flagDirection hk (rotationIsometry F.1⁻¹ x))).1,
   F.2 * (gaussianSection (prefixSpace d k) (prefixUnit hk) (rotationIsometry F.2⁻¹ g)).1)

@[fun_prop] lemma measurable_inverseFrameUpdate {d k : ℕ} (hk : k < d) :
    Measurable (fun p : Frames d × Point d × Point d => inverseFrameUpdate hk p.1 p.2.1 p.2.2) := by
  unfold inverseFrameUpdate
  apply Measurable.prodMk
  · apply Measurable.mul (by fun_prop)
    apply measurable_subtype_coe.comp
    exact (measurable_complementSection_left _ _).comp (by fun_prop)
  · fun_prop

theorem inverseFrameUpdate_law {d k : ℕ} (hk : k < d) (F : Frames d) (x : Point d) :
    ((stdGaussian (Point d)).prod (remainingHaar (prefixSpace d (k+1)))).map
      (fun p => frameCompletion (inverseFrameUpdate hk F x p.1) p.2) =
    (remainingHaar (prefixSpace d k)).map (frameCompletion F) := by
  let E := prefixSpace d k
  let e := prefixUnit hk
  let w := flagDirection hk (rotationIsometry F.1⁻¹ x)
  have hg : (stdGaussian (Point d)).map (rotationIsometry F.2⁻¹) = stdGaussian (Point d) :=
    stdGaussian_map (rotationIsometry F.2⁻¹)
  have hP := Measure.map_prod_map (stdGaussian (Point d))
    (remainingHaar (prefixSpace d (k+1))) (by fun_prop : Measurable (rotationIsometry F.2⁻¹))
      measurable_id
  rw [hg, Measure.map_id] at hP
  have hl := congrArg (fun μ : Measure (Rotations d) => μ.map (frameCompletion F))
    (ambientBackward_law E (norm_prefixUnit hk) w)
  have hEq : E ⊔ ℝ ∙ (e : Point d) = prefixSpace d (k+1) := (prefixSpace_succ hk).symm
  rw [hEq, Measure.map_map (by fun_prop) (measurable_ambientBackward E e w)] at hl
  rw [hP, Measure.map_map (by fun_prop) (by fun_prop)] at hl
  convert hl using 1
  congr 1
  funext p
  simp only [Function.comp_apply, frameCompletion,
    inverseFrameUpdate, ambientBackward, E, e, w]
  group; rfl

lemma remainingHaar_map_inv {d : ℕ} (E : Submodule ℝ (Point d)) :
    (remainingHaar E).map Inv.inv = remainingHaar E := by
  unfold remainingHaar
  rw [Measure.map_map (by fun_prop) measurable_subtype_coe]
  calc
    _ = ((subspaceHaar E).map Inv.inv).map Subtype.val := by
      rw [Measure.map_map measurable_subtype_coe (by fun_prop)]
      rfl
    _ = _ := by rw [Measure.map_inv_eq_self]

@[simp] lemma frameCompletion_swap {d : ℕ} (F : Frames d) (H : Rotations d) :
    frameCompletion F.swap H⁻¹ = (frameCompletion F H)⁻¹ := by
  simp [frameCompletion]; group

def forwardFrameUpdate {d k : ℕ} (hk : k < d) (F : Frames d) (y g : Point d) : Frames d :=
  (inverseFrameUpdate hk F.swap y g).swap

@[fun_prop] lemma measurable_forwardFrameUpdate {d k : ℕ} (hk : k < d) :
    Measurable (fun p : Frames d × Point d × Point d => forwardFrameUpdate hk p.1 p.2.1 p.2.2) := by
  unfold forwardFrameUpdate
  have h := (measurable_inverseFrameUpdate hk).comp
    (show Measurable (fun p : Frames d × Point d × Point d => (p.1.swap,p.2)) by fun_prop)
  exact h.snd.prodMk h.fst

theorem forwardFrameUpdate_law {d k : ℕ} (hk : k < d) (F : Frames d) (y : Point d) :
    ((stdGaussian (Point d)).prod (remainingHaar (prefixSpace d (k+1)))).map
      (fun p => frameCompletion (forwardFrameUpdate hk F y p.1) p.2) =
    (remainingHaar (prefixSpace d k)).map (frameCompletion F) := by
  have hl := congrArg (fun μ : Measure (Rotations d) => μ.map Inv.inv)
    (inverseFrameUpdate_law hk F.swap y)
  rw [Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)] at hl
  have hP := Measure.map_prod_map (stdGaussian (Point d))
    (remainingHaar (prefixSpace d (k+1))) measurable_id (by fun_prop : Measurable (Inv.inv : Rotations d → _))
  rw [Measure.map_id, remainingHaar_map_inv] at hP
  rw [hP, Measure.map_map (by fun_prop) (by fun_prop)]
  change ((stdGaussian (Point d)).prod (remainingHaar (prefixSpace d (k+1)))).map
    (fun p => frameCompletion (forwardFrameUpdate hk F y p.1) p.2⁻¹) = _
  simp only [forwardFrameUpdate, frameCompletion_swap]
  simp only [Function.comp_def] at hl
  rw [hl]
  calc
    _ = ((remainingHaar (prefixSpace d k)).map Inv.inv).map (frameCompletion F) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      congr 1; funext H
      simp [frameCompletion, mul_assoc]
    _ = _ := by rw [remainingHaar_map_inv]

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound
open scoped RealInnerProductSpace

def frameSpace {d : ℕ} (O : Rotations d) (E : Submodule ℝ (Point d)) : Submodule ℝ (Point d) :=
  E.map (rotationIsometry O).toLinearEquiv.toLinearMap

lemma mem_frameSpace {d : ℕ} (O : Rotations d) (E : Submodule ℝ (Point d)) (x : Point d) :
    x ∈ frameSpace O E ↔ rotationIsometry O⁻¹ x ∈ E := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    rw [rotationIsometry_inv_apply]
    change (rotationIsometry O).symm (rotationIsometry O y) ∈ E
    rw [LinearIsometryEquiv.symm_apply_apply]
    exact hy
  · intro hx
    refine ⟨rotationIsometry O⁻¹ x,hx,?_⟩
    simp only [LinearEquiv.coe_toLinearMap, LinearIsometryEquiv.coe_toLinearEquiv,
      rotationIsometry_inv_apply, LinearIsometryEquiv.apply_symm_apply]

lemma frameSpace_mul {d : ℕ} (O P : Rotations d) (E : Submodule ℝ (Point d)) :
    frameSpace (O*P) E = frameSpace O (frameSpace P E) := by
  ext x
  simp only [mem_frameSpace, _root_.mul_inv_rev, rotationIsometry_mul]

lemma frameSpace_sup {d : ℕ} (O : Rotations d) (E F : Submodule ℝ (Point d)) :
    frameSpace O (E ⊔ F) = frameSpace O E ⊔ frameSpace O F := Submodule.map_sup _ _ _

lemma frameSpace_line {d : ℕ} (O : Rotations d) (x : Point d) :
    frameSpace O (ℝ ∙ x) = ℝ ∙ rotationIsometry O x := by
  simp only [frameSpace, Submodule.map_span, Set.image_singleton,
    LinearEquiv.coe_toLinearMap, LinearIsometryEquiv.coe_toLinearEquiv]

lemma frameSpace_fixed {d : ℕ} (E : Submodule ℝ (Point d))
    {O : Rotations d} (hO : O ∈ subspaceStabilizer E) : frameSpace O E = E := by
  apply le_antisymm
  · rintro x ⟨y,hy,rfl⟩
    change rotationIsometry O y ∈ E
    rw [hO y hy]
    exact hy
  · intro x hx
    exact ⟨x,hx,hO x hx⟩

lemma frameSpace_mono {d : ℕ} (O : Rotations d) {E F : Submodule ℝ (Point d)}
    (h : E ≤ F) : frameSpace O E ≤ frameSpace O F := Submodule.map_mono h

lemma complementSection_frameSpace {d : ℕ} (E : Submodule ℝ (Point d))
    {e w : Eᗮ} (h : ‖e‖ = ‖w‖) :
    frameSpace (complementSection E e w).1 (E ⊔ ℝ ∙ (e : Point d)) =
      E ⊔ ℝ ∙ (w : Point d) := by
  rw [frameSpace_sup, frameSpace_fixed E (complementSection E e w).property, frameSpace_line]
  have hs := congrArg Subtype.val (complementSection_sends E h)
  change rotationIsometry (complementSection E e w).1 e = w at hs
  rw [hs]

lemma flagSection_frameSpace {d k : ℕ} (hk : k < d) (x : Point d) :
    frameSpace (complementSection (prefixSpace d k) (prefixUnit hk) (flagDirection hk x)).1
      (prefixSpace d (k+1)) = prefixSpace d k ⊔ ℝ ∙ (flagDirection hk x : Point d) := by
  rw [prefixSpace_succ hk]
  exact complementSection_frameSpace (prefixSpace d k)
    (e := prefixUnit hk) (w := flagDirection hk x) (by rw [norm_prefixUnit, norm_flagDirection])

lemma vector_mem_flagDirection {d k : ℕ} (hk : k < d) (x : Point d) :
    x ∈ prefixSpace d k ⊔ ℝ ∙ (flagDirection hk x : Point d) := by
  let E := prefixSpace d k
  have ht : ((Eᗮ.orthogonalProjectionOnto x : Eᗮ) : Point d) ∈
      ℝ ∙ (flagDirection hk x : Point d) := by
    change _ ∈ ℝ ∙ ((normalizedDirection (prefixUnit hk) (Eᗮ.orthogonalProjectionOnto x) : Eᗮ) : Point d)
    by_cases hn : Eᗮ.orthogonalProjectionOnto x = 0
    · simp [hn]
    · have hs := (ℝ ∙ ((normalizedDirection (prefixUnit hk) (Eᗮ.orthogonalProjectionOnto x) : Eᗮ) : Point d)).smul_mem
        ‖Eᗮ.orthogonalProjectionOnto x‖ (Submodule.mem_span_singleton_self _)
      simpa only [normalizedDirection, ite_eq_right hn, Submodule.coe_smul_of_tower, smul_smul,
        mul_inv_cancel₀ (norm_ne_zero_iff.mpr hn), one_smul] using hs
  have hp : E.starProjection x ∈ E := E.starProjection_apply_mem x
  have hs := (E ⊔ ℝ ∙ (flagDirection hk x : Point d)).add_mem
    ((le_sup_left : E ≤ _) hp) ((le_sup_right : ℝ ∙ _ ≤ _) ht)
  convert hs using 1
  exact (E.starProjection_add_starProjection_orthogonal x).symm

lemma flagDirection_mem_span {d k : ℕ} (hk : k < d) (x : Point d)
    (hn : (prefixSpace d k)ᗮ.orthogonalProjectionOnto x ≠ 0) :
    (flagDirection hk x : Point d) ∈ prefixSpace d k ⊔ ℝ ∙ x := by
  let E := prefixSpace d k
  have hx : x ∈ E ⊔ ℝ ∙ x := (le_sup_right : ℝ ∙ x ≤ _) (Submodule.mem_span_singleton_self x)
  have hp : E.starProjection x ∈ E ⊔ ℝ ∙ x :=
    (le_sup_left : E ≤ _) (E.starProjection_apply_mem x)
  have ht := (E ⊔ ℝ ∙ x).sub_mem hx hp
  rw [← Submodule.starProjection_orthogonal_val] at ht
  have hs := (E ⊔ ℝ ∙ x).smul_mem ‖Eᗮ.orthogonalProjectionOnto x‖⁻¹ ht
  simp only [flagDirection, normalizedDirection, ite_eq_right hn]
  exact hs

end LogConcaveSampling.LowerBound

namespace LogConcaveSampling.LowerBound

def extendFrame {d k : ℕ} (hk : k < d) (O : Rotations d) (x : Point d) : Rotations d :=
  O * (complementSection (prefixSpace d k) (prefixUnit hk)
    (flagDirection hk (rotationIsometry O⁻¹ x))).1

@[fun_prop] lemma measurable_extendFrame {d k : ℕ} (hk : k < d) :
    Measurable (fun p : Rotations d × Point d => extendFrame hk p.1 p.2) := by
  unfold extendFrame
  apply Measurable.mul measurable_fst
  apply measurable_subtype_coe.comp
  exact (measurable_complementSection_left _ _).comp (by fun_prop)

lemma inverseFrameUpdate_eq {d k : ℕ} (hk : k < d) (F : Frames d) (x g : Point d) :
    inverseFrameUpdate hk F x g = (extendFrame hk F.1 x, extendFrame hk F.2 g) := rfl

lemma forwardFrameUpdate_eq {d k : ℕ} (hk : k < d) (F : Frames d) (y g : Point d) :
    forwardFrameUpdate hk F y g = (extendFrame hk F.1 g, extendFrame hk F.2 y) := rfl

lemma frameSpace_extendFrame {d k : ℕ} (hk : k < d) (O : Rotations d) (x : Point d) :
    frameSpace (extendFrame hk O x) (prefixSpace d (k+1)) =
      frameSpace O (prefixSpace d k) ⊔
        ℝ ∙ rotationIsometry O (flagDirection hk (rotationIsometry O⁻¹ x) : Point d) := by
  rw [extendFrame, frameSpace_mul, flagSection_frameSpace, frameSpace_sup, frameSpace_line]

lemma frameSpace_le_extendFrame {d k : ℕ} (hk : k < d) (O : Rotations d) (x : Point d) :
    frameSpace O (prefixSpace d k) ≤ frameSpace (extendFrame hk O x) (prefixSpace d (k+1)) := by
  rw [frameSpace_extendFrame]
  exact le_sup_left

lemma mem_frameSpace_extendFrame {d k : ℕ} (hk : k < d) (O : Rotations d) (x : Point d) :
    x ∈ frameSpace (extendFrame hk O x) (prefixSpace d (k+1)) := by
  rw [extendFrame, frameSpace_mul, flagSection_frameSpace, mem_frameSpace]
  exact vector_mem_flagDirection hk _

lemma frameSpace_extendFrame_le {d k : ℕ} (hk : k < d) (O : Rotations d) (x : Point d)
    (hn : (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry O⁻¹ x) ≠ 0) :
    frameSpace (extendFrame hk O x) (prefixSpace d (k+1)) ≤
      frameSpace O (prefixSpace d k) ⊔ ℝ ∙ x := by
  rw [extendFrame, frameSpace_mul, flagSection_frameSpace]
  have hs : prefixSpace d k ⊔ ℝ ∙ (flagDirection hk (rotationIsometry O⁻¹ x) : Point d) ≤
      prefixSpace d k ⊔ ℝ ∙ rotationIsometry O⁻¹ x := by
    apply sup_le le_sup_left
    exact Submodule.span_le.mpr (by
      intro v hv
      rcases Set.mem_singleton_iff.mp hv with rfl
      exact flagDirection_mem_span hk _ hn)
  have h := frameSpace_mono O hs
  simp only [frameSpace_sup, frameSpace_line, rotationIsometry_inv_apply,
    LinearIsometryEquiv.apply_symm_apply] at h
  rw [frameSpace_sup, frameSpace_line]
  simpa only [rotationIsometry_inv_apply] using h

lemma ae_frameGaussian_nonzero {d k : ℕ} (hk : k < d) (O : Rotations d) :
    ∀ᵐ g ∂stdGaussian (Point d),
      (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry O⁻¹ g) ≠ 0 := by
  have h := ae_stdGaussian_ne_zero_of_unit (norm_prefixUnit hk)
  rw [← stdGaussian_orthogonalProjection (prefixSpace d k)ᗮ] at h
  have hp : ∀ᵐ x ∂stdGaussian (Point d), (prefixSpace d k)ᗮ.orthogonalProjectionOnto x ≠ 0 :=
    (ae_map_iff (by fun_prop) (measurableSet_singleton 0).compl).mp h
  rw [← stdGaussian_map (rotationIsometry O⁻¹)] at hp
  exact (ae_map_iff (by fun_prop) ((measurableSet_singleton 0).compl.preimage (by fun_prop))).mp hp

def filledObservation {d k : ℕ} (O : Rotations d) (x g : Point d) : Point d :=
  if (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry O⁻¹ x) = 0 then g else x

@[fun_prop] lemma measurable_filledObservation {d k : ℕ} :
    Measurable (fun p : Rotations d × Point d × Point d => filledObservation (k := k) p.1 p.2.1 p.2.2) := by
  unfold filledObservation
  exact Measurable.ite (measurableSet_eq_fun (by fun_prop) measurable_const) (by fun_prop) (by fun_prop)

lemma mem_frameSpace_of_projection_zero {d k : ℕ} (O : Rotations d) (x : Point d)
    (hz : (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry O⁻¹ x) = 0) :
    x ∈ frameSpace O (prefixSpace d k) := by
  rw [mem_frameSpace]
  have hz' := congrArg Subtype.val hz
  change (prefixSpace d k)ᗮ.starProjection (rotationIsometry O⁻¹ x) = 0 at hz'
  rw [Submodule.starProjection_orthogonal_val, sub_eq_zero] at hz'
  rw [hz']
  exact Submodule.starProjection_apply_mem _ _

lemma mem_frameSpace_filledExtend {d k : ℕ} (hk : k < d) (O : Rotations d) (x g : Point d) :
    x ∈ frameSpace (extendFrame hk O (filledObservation (k := k) O x g)) (prefixSpace d (k+1)) := by
  unfold filledObservation
  split_ifs with hz
  · exact frameSpace_le_extendFrame hk O g (mem_frameSpace_of_projection_zero O x hz)
  · exact mem_frameSpace_extendFrame hk O x

lemma frameSpace_filledExtend_le {d k : ℕ} (hk : k < d) (O : Rotations d) (x g : Point d)
    (hg : (prefixSpace d k)ᗮ.orthogonalProjectionOnto (rotationIsometry O⁻¹ g) ≠ 0) :
    frameSpace (extendFrame hk O (filledObservation (k := k) O x g)) (prefixSpace d (k+1)) ≤
      (frameSpace O (prefixSpace d k) ⊔ ℝ ∙ x) ⊔ ℝ ∙ g := by
  unfold filledObservation
  split_ifs with hx
  · exact (frameSpace_extendFrame_le hk O g hg).trans (sup_le_sup le_sup_left le_rfl)
  · exact (frameSpace_extendFrame_le hk O x hx).trans le_sup_left

end LogConcaveSampling.LowerBound

end LowerProof
end
end
end

end OAI
