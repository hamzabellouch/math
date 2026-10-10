import OAI.Geometry.CylinderCovering.Nilpotent.DomainExampleDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.C1
import OAI.Geometry.CylinderCovering.Ruled.NullDomain

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped Topology ContDiff
namespace RuledApproximation.NilpotentDomainExample

lemma field_apply (p : Plane) : field p = vec2 (p 1) ((p 0)^3) := by
  ext i
  fin_cases i <;> simp [field, vec2]

lemma field_contDiff : ContDiff ℝ ∞ field := by
  exact ((EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).contDiff.smul_const (vec2 1 0)).add
    (((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).contDiff.pow 3).smul_const (vec2 0 1))

lemma field_fderiv_apply (p q : Plane) :
    fderiv ℝ field p q = vec2 (q 1) (3*(p 0)^2*(q 0)) := by
  have hd := ((EuclideanSpace.proj (1 : Fin 2) : Plane →L[ℝ] ℝ).hasFDerivAt (x := p)).smul_const (vec2 1 0)
  have he := (((EuclideanSpace.proj (0 : Fin 2) : Plane →L[ℝ] ℝ).hasFDerivAt (x := p)).pow 3).smul_const (vec2 0 1)
  change (fderiv ℝ ((fun y : Plane => (EuclideanSpace.proj 1) y • vec2 1 0) +
    fun y : Plane => ((EuclideanSpace.proj 0) y)^3 • vec2 0 1) p) q = _
  rw [(hd.add he).fderiv]
  ext i
  fin_cases i <;> simp [vec2]

lemma field_squareZero_iff (p : Plane) :
    (fderiv ℝ field p).comp (fderiv ℝ field p) = 0 ↔ p 0 = 0 := by
  constructor
  · intro h
    have hh := congrArg (fun A : Plane →L[ℝ] Plane => A (vec2 1 0) 0) h
    simp [ContinuousLinearMap.comp_apply, field_fderiv_apply, vec2] at hh
    nlinarith [sq_nonneg (p 0)]
  · intro hp
    ext q i
    simp only [ContinuousLinearMap.comp_apply, zero_apply,
      field_fderiv_apply]
    fin_cases i <;> simp [hp, vec2]

lemma labels_compact : IsCompact labels := by
  apply isCompact_Icc.image
  have hc : Continuous (fun y : ℝ => y • vec2 0 1) :=
    continuous_id.smul continuous_const
  convert! hc using 1
  funext y
  ext i
  fin_cases i <;> simp [vec2]

lemma zero_mem_labels : (0 : Plane) ∈ labels := by
  refine ⟨0, by norm_num, ?_⟩
  ext i
  fin_cases i <;> rfl

lemma labels_volume_zero : volume labels = 0 := by
  let ell : Plane →L[ℝ] ℝ := EuclideanSpace.proj 0
  have hker : ((ell.ker : Submodule ℝ Plane) : Set Plane) ≠ univ := by
    intro h
    have hm : vec2 1 0 ∈ (ell.ker : Set Plane) := by rw [h]; trivial
    change (1 : ℝ) = 0 at hm
    norm_num at hm
  have hker' : ell.ker ≠ ⊤ := by
    intro h
    apply hker
    simp [h]
  apply measure_mono_null (t := (ell.ker : Set Plane)) ?_
    (Measure.addHaar_submodule volume ell.ker hker')
  rintro p ⟨y, hy, rfl⟩
  change (0 : ℝ) = 0
  rfl

lemma field_squareZero_on_labels :
    ∀ p ∈ labels, (fderiv ℝ field p).comp (fderiv ℝ field p) = 0 := by
  rintro p ⟨y, hy, rfl⟩
  exact (field_squareZero_iff _).mpr rfl

lemma no_squareZero_neighborhood :
    ¬ ∃ U : Set Plane, IsOpen U ∧ labels ⊆ U ∧
      ∀ p ∈ U, (fderiv ℝ field p).comp (fderiv ℝ field p) = 0 := by
  rintro ⟨U, hU, hDU, hnil⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU 0 (hDU zero_mem_labels)
  let p : Plane := vec2 (r/2) 0
  have hnorm : ‖p‖ = r/2 := by
    have hs := norm_plane_sq p
    simp only [p, vec2_apply_zero, vec2_apply_one, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero] at hs
    nlinarith [norm_nonneg p]
  have hp : p ∈ U := hball (by simp [Metric.mem_ball, dist_zero_right, hnorm]; linarith)
  have hz := (field_squareZero_iff p).mp (hnil p hp)
  change r/2 = 0 at hz
  linarith

lemma field_smoothNear : SmoothNear 1 labels field :=
  ⟨univ, isOpen_univ, subset_univ _, (field_contDiff.of_le (by norm_num)).contDiffOn⟩

theorem physical_cover {h eps : ℝ} (hh : 0 < h) (heps : 0 < eps) :
    HasFiniteCover (squareProjected h) (physicalRuled h labels field 1)
      (h * (∫ p in labels, physicalWeight h (field p)) + eps) :=
  nilpotent_physical_cover hh labels_compact field_smoothNear
    field_squareZero_on_labels heps

theorem physical_pair {h eps : ℝ} (hh : 0 < h) (heps : 0 < eps) (a : ℝ) :
    ∃ n : ℕ, ∃ C₁ C₂ : Fin n → Cylinder,
      (∀ i, (C₁ i).parallelogram ∧ (C₂ i).parallelogram ∧
        IsCompact (C₁ i).base ∧ IsCompact (C₂ i).base ∧
        Convex ℝ (C₁ i).base ∧ Convex ℝ (C₂ i).base) ∧
      physicalRuled h labels field 1 ⊆ familySet C₁ ∧
      secondPhysicalMap h a '' physicalRuled 1 labels field 1 ⊆ familySet C₂ ∧
      familyArea C₁ = familyArea C₂ ∧ familyArea C₁ + familyArea C₂ < eps :=
  null_domain_physical_pair labels_compact labels_volume_zero field_smoothNear
    field_squareZero_on_labels hh heps a

end RuledApproximation.NilpotentDomainExample

end

end OAI
