import OAI.GroupTheory.PolycyclicRecognition.Geometry.TemplateWeightRays
import OAI.GroupTheory.PolycyclicRecognition.Geometry.NormalizedWeightRays
import OAI.GroupTheory.PolycyclicRecognition.Algebra.TemplateVariationEquality
import OAI.GroupTheory.PolycyclicRecognition.Algebra.FiniteSignOrder

namespace OAI

/-! # Constant generic line signs from the actual template label action -/

noncomputable section

namespace PolycyclicRecognition.SupportDatum

open MeasureTheory Set Filter

/-- Duplicate generator rays are normalized and removed before counting
positive signs. Thus the constant-count step follows from the actual template
symmetry action, rather than being a new hypothesis on the profile. -/
theorem generic_profile_signs_constant
    {W I B : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] [Fintype I] [Fintype B] [Nonempty B]
    (D : PolycyclicRecognition.SupportDatum W I B)
    (hweights : ∀ i, D.weight i ≠ 0)
    (h q : ℝ → W) (hc : Continuous h) (w : W) (hw : ∀ i, D.weight i w ≠ 0)
    {T : ℝ} (hT : 0 ≤ T)
    (hq : ∀ i, IntervalIntegrable (fun t => D.weight i (q t)) volume 0 T)
    (hFTC : ∀ i t, t ∈ Icc 0 T →
      D.weight i (h t) = ∫ s in 0..t, D.weight i (q s))
    (label : ℝ → templateSymmetryGroup D)
    (hlabel : ∀ᵐ t ∂volume.restrict (Icc 0 T), q t = (label t).val w)
    (hlower : T * D.segmentSupport w ≤ D.templateSupport (h '' Icc 0 T)) :
    ∃ S : Finset I, ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      ∀ i, (0 < D.weight i (q t) ↔ i ∈ S) := by
  classical
  let α : I → W →L[ℝ] ℝ := fun i => (D.weight i).toContinuousLinearMap
  have hα (i : I) : α i ≠ 0 := by
    intro hi
    apply hweights i
    ext x
    exact congrArg (fun f : W →L[ℝ] ℝ => f x) hi
  let R := NormalizedWeightRays α
  let : Fintype R := Fintype.ofFinite _
  let β : R → W →ₗ[ℝ] ℝ := fun x => x.val.toLinearMap
  have hperm (A : templateSymmetryGroup D) : ∃ σ : R ≃ R, ∃ r : R → ℝ,
      (∀ x, 0 < r x) ∧ ∀ x, (β x).comp A.val.toLinearMap = r x • β (σ x) := by
    exact exists_normalizedWeightRays_permutation α hα A.val
      (fun i => templateSymmetry_weight_ray D A i (hweights i))
  have hgeneric (x : R) : β x w ≠ 0 := by
    obtain ⟨i, hi⟩ := x.property
    change x.val w ≠ 0
    rw [← hi]
    change ‖α i‖⁻¹ * α i w ≠ 0
    exact mul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr (hα i))) (hw i)
  have hnonzero (A : templateSymmetryGroup D) : ∀ x, β x (A.val w) ≠ 0 := by
    obtain ⟨σ, r, hr, heq⟩ := hperm A
    exact nonzero_weights_of_ray_permutation β A.val σ r hr heq w hgeneric
  have hcount (A : templateSymmetryGroup D) :
      (Finset.univ.filter (fun x => 0 < β x (A.val w))).card =
        (Finset.univ.filter (fun x => 0 < β x w)).card := by
    obtain ⟨σ, r, hr, heq⟩ := hperm A
    exact positive_weight_count_of_ray_permutation β A.val σ r hr heq w
  have hbound (b : B) : ∀ᵐ t ∂volume.restrict (Icc 0 T),
      D.basisSupport b (q t) ≤ D.segmentSupport w := by
    filter_upwards [hlabel] with t ht
    rw [ht]
    exact (D.basisSupport_le b _).trans_eq
      (templateSymmetry_mem_linearSupportSymmetry D (label t) w)
  obtain ⟨τ, _, _, hleft, hright⟩ :=
    D.exists_ordered_weight_signs h q hc hT hq hFTC hbound hlower
  have hrep (x : R) : ∃ i, x.val = normalizedWeight (α i) := by
    obtain ⟨i, hi⟩ := x.property
    exact ⟨i, hi.symm⟩
  choose rep hrep using hrep
  let θ : R → ℝ := fun x => τ (rep x)
  have hleftR (x : R) : ∀ᵐ t ∂volume.restrict (Ioc 0 (θ x)), 0 ≤ β x (q t) := by
    filter_upwards [hleft (rep x)] with t ht
    change 0 ≤ x.val (q t)
    rw [hrep x]
    exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) ht
  have hrightR (x : R) : ∀ᵐ t ∂volume.restrict (Ioc (θ x) T), β x (q t) ≤ 0 := by
    filter_upwards [hright (rep x)] with t ht
    change x.val (q t) ≤ 0
    rw [hrep x]
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr (norm_nonneg _)) ht
  have hlabel' : ∀ᵐ t ∂volume.restrict (Ioc 0 T), q t = (label t).val w :=
    hlabel.filter_mono (ae_mono (Measure.restrict_mono Ioc_subset_Icc_self le_rfl))
  have hnonzeroR (x : R) : ∀ᵐ t ∂volume.restrict (Ioc 0 T), β x (q t) ≠ 0 := by
    filter_upwards [hlabel'] with t ht
    rw [ht]
    exact hnonzero (label t) x
  have hcountR : ∀ᵐ t ∂volume.restrict (Ioc 0 T),
      (Finset.univ.filter (fun x => 0 < β x (q t))).card =
        (Finset.univ.filter (fun x => 0 < β x w)).card := by
    filter_upwards [hlabel'] with t ht
    rw [ht]
    exact hcount (label t)
  obtain ⟨S, hS⟩ := exists_constant_positive_signs (fun x t => β x (q t)) θ
    (Finset.univ.filter (fun x => 0 < β x w)).card hnonzeroR hleftR hrightR hcountR
  let ray (i : I) : R := ⟨normalizedWeight (α i), ⟨i, rfl⟩⟩
  refine ⟨Finset.univ.filter (fun i => ray i ∈ S), ?_⟩
  filter_upwards [hS] with t ht
  intro i
  have hi := ht (ray i)
  change 0 < normalizedWeight (α i) (q t) ↔ ray i ∈ S at hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change 0 < α i (q t) ↔ ray i ∈ S
  exact (normalizedWeight_pos_iff (α i) (hα i) (q t)).symm.trans hi

end PolycyclicRecognition.SupportDatum

end

end OAI
