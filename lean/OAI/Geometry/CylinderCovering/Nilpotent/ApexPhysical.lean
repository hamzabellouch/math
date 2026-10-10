import OAI.Geometry.CylinderCovering.Nilpotent.ApexPhysicalDefinitions
import OAI.Geometry.CylinderCovering.Nilpotent.ApexNet
import OAI.Geometry.CylinderCovering.Ruled.Projection

namespace OAI

open Set MeasureTheory RuledApproximation

noncomputable section
namespace CylinderCovering.NilpotentApexNet

lemma planeTile_mem_iff (k ρ : ℝ) (z : Plane) :
    z ∈ planeTile k ρ ↔ |z 0| ≤ radius k ρ ∧ |z 1| ≤ radius k ρ := by
  constructor
  · rintro ⟨q, hq, rfl⟩
    change ((-radius k ρ ≤ q.1 ∧ -radius k ρ ≤ q.2) ∧
      q.1 ≤ radius k ρ ∧ q.2 ≤ radius k ρ) at hq
    exact ⟨abs_le.mpr ⟨hq.1.1, hq.2.1⟩, abs_le.mpr ⟨hq.1.2, hq.2.2⟩⟩
  · intro hz
    refine ⟨(z 0, z 1), ?_, ?_⟩
    · exact ⟨⟨(abs_le.mp hz.1).1, (abs_le.mp hz.2).1⟩,
        (abs_le.mp hz.1).2, (abs_le.mp hz.2).2⟩
    · ext i
      fin_cases i <;> rfl

lemma planeTile_isSquare {k ρ : ℝ} (hk : 0 ≤ k) (hρ : 0 < ρ) :
    IsSquareTile (planeTile k ρ) := by
  have hr := radius_pos hk hρ
  refine ⟨0, LinearIsometryEquiv.refl ℝ Plane, 2 * radius k ρ, by positivity, ?_⟩
  ext z
  rw [planeTile_mem_iff]
  constructor
  · intro hz
    refine ⟨(2 * radius k ρ)⁻¹ • z, ?_, ?_⟩
    · intro i
      fin_cases i
      · change |(2 * radius k ρ)⁻¹ * z 0| ≤ 1 / 2
        rw [abs_mul, abs_inv, abs_of_pos (by positivity : 0 < 2 * radius k ρ)]
        apply (inv_mul_le_iff₀ (by positivity : 0 < 2 * radius k ρ)).2
        linarith [hz.1]
      · change |(2 * radius k ρ)⁻¹ * z 1| ≤ 1 / 2
        rw [abs_mul, abs_inv, abs_of_pos (by positivity : 0 < 2 * radius k ρ)]
        apply (inv_mul_le_iff₀ (by positivity : 0 < 2 * radius k ρ)).2
        linarith [hz.2]
    · simp only [LinearIsometryEquiv.coe_refl, id_eq, zero_add, smul_smul,
        mul_inv_cancel₀ (by positivity : 2 * radius k ρ ≠ 0), one_smul]
  · rintro ⟨x, hx, rfl⟩
    have h0 := hx 0
    have h1 := hx 1
    simp only [LinearIsometryEquiv.coe_refl, id_eq, zero_add]
    change |2 * radius k ρ * x 0| ≤ radius k ρ ∧
      |2 * radius k ρ * x 1| ≤ radius k ρ
    simp only [abs_mul, abs_of_pos hr, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    constructor <;> nlinarith [mul_le_mul_of_nonneg_left h0 (by positivity : 0 ≤ 2 * radius k ρ),
      mul_le_mul_of_nonneg_left h1 (by positivity : 0 ≤ 2 * radius k ρ)]

lemma planeTile_area (k ρ : ℝ) :
    volume.real (planeTile k ρ) = (volume (tile k ρ)).toReal := by
  have he : planeTile k ρ = pairPlaneEquiv '' tile k ρ := rfl
  rw [he, measureReal_def]
  congr 1
  have hi : pairPlaneEquiv '' tile k ρ = pairPlaneEquiv.symm ⁻¹' tile k ρ :=
    pairPlaneEquiv.toEquiv.image_eq_preimage_symm _
  rw [hi]
  exact (MeasurePreserving.symm pairPlaneEquiv pairPlane_measurePreserving).measure_preimage_equiv _

lemma planeVelocity_weight (h k σ p : ℝ) :
    physicalWeight h (planeVelocity k σ p) = weight h (velocity k σ p) := rfl

lemma auxiliary_apex_cover {k ρ σ : ℝ} (hk : 0 ≤ k) (hρ : 0 < ρ) (hσ : |σ| ≤ 1)
    {s p t : ℝ} (hs : |s| ≤ 1) (hp : |p| ≤ 1) (ht : 0 ≤ t) (htρ : t ≤ ρ) :
    ∃ j : Fin (meshCount ρ + 1),
      axial s (vec2 (p * t) t + s • planeVelocity k σ p) ∈
        auxiliaryCylinder (planeTile k ρ) (planeVelocity k σ (node ρ j)) := by
  obtain ⟨j, hj⟩ := exists_near_node hρ hp
  have hres := residual_bound hk hσ hp (node_bounds hρ (by omega)) hj hs ht htρ
  let q : ℝ × ℝ := (p * t, t) + s • velocity k σ p - s • velocity k σ (node ρ j)
  refine ⟨j, s, vec2 q.1 q.2, ⟨q, hres, rfl⟩, ?_⟩
  congr 1
  ext i
  fin_cases i <;> simp [q, planeVelocity, vec2, velocity]

theorem physicalApexNet : PhysicalApexNetStatement := by
  intro h k ρ σ hh hk hρ hρ1 hσ F
  have hsq := planeTile_isSquare hk hρ
  have hcompact := hsq.parallelogram.isCompact
  have hmeas := hcompact.measurableSet
  have hbounded := hcompact.isBounded
  have hex : ∀ j : Fin (meshCount ρ + 1), ∃ C : Cylinder,
      C.carrier = F '' (firstPhysicalMap h '' auxiliaryCylinder (planeTile k ρ)
        (planeVelocity k σ (node ρ j))) ∧
      C.axis = F.toRealLinearIsometryEquiv
        (‖vec3 1 (planeVelocity k σ (node ρ j) 0) (h * planeVelocity k σ (node ρ j) 1)‖⁻¹ •
          vec3 1 (planeVelocity k σ (node ρ j) 0) (h * planeVelocity k σ (node ρ j) 1)) ∧
      C.area = h * volume.real (planeTile k ρ) * physicalWeight h (planeVelocity k σ (node ρ j)) ∧
      MeasurableSet C.base ∧ Bornology.IsBounded C.base ∧ volume C.base < ⊤ ∧
      (IsOpen (planeTile k ρ) → IsOpen C.base) ∧
      (IsCompact (planeTile k ρ) → IsCompact C.base) ∧
      (IsParallelogram (planeTile k ρ) → C.parallelogram) := by
    intro j
    exact physicalProjection_proof h (planeTile k ρ) (planeVelocity k σ (node ρ j)) hh hbounded hmeas F
  choose C hcarrier haxis harea hmeasure hbound hfinite hopen hcomp hpara using hex
  refine ⟨C, ?_, ?_, ?_⟩
  · intro j
    have hp := hpara j hsq.parallelogram
    refine ⟨hp, hcomp j hcompact, hp.convex, hmeasure j, hfinite j, hcarrier j, haxis j, ?_⟩
    rw [harea, planeTile_area, planeVelocity_weight]
    unfold weightedArea
    ring
  · rintro z ⟨q, ⟨s, p, t, hs, hp, ht, htρ, rfl⟩, rfl⟩
    obtain ⟨j, hj⟩ := auxiliary_apex_cover hk hρ hσ hs hp ht htρ
    apply mem_iUnion.mpr
    refine ⟨j, ?_⟩
    rw [hcarrier]
    apply mem_image_of_mem
    refine ⟨axial s (vec2 (p * t) t + s • planeVelocity k σ p), hj, ?_⟩
    ext i
    fin_cases i <;> simp [firstPhysicalMap, axial, planeVelocity, vec3]
  · have hsum : familyArea C = h * ∑ j : Fin (meshCount ρ + 1), weightedArea h k ρ σ j := by
      unfold familyArea
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [harea, planeTile_area, planeVelocity_weight]
      unfold weightedArea
      ring
    rw [hsum]
    exact mul_le_mul_of_nonneg_left (apex_cost h hk hρ hρ1) hh.le

theorem physicalApex_hasFiniteCover {h k ρ σ : ℝ} (hh : 0 < h) (hk : 0 ≤ k)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hσ : |σ| ≤ 1) (F : Space ≃ᵢ Space) :
    HasFiniteCover Cylinder.parallelogram (F '' physicalApexSweep h k ρ σ)
      (h * (16 * (1 + k / 2) ^ 2 * ρ)) := by
  obtain ⟨C, hC, hcover, hcost⟩ := physicalApexNet h k ρ σ hh hk hρ hρ1 hσ F
  exact ⟨meshCount ρ + 1, C, fun j => (hC j).1, hcover, hcost⟩

theorem fullApexNet : FullApexNetStatement :=
  ⟨auxiliaryApexNet, physicalApexNet⟩

end CylinderCovering.NilpotentApexNet

end

end OAI
