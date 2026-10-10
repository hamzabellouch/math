import OAI.Geometry.CylinderCovering.Nilpotent.IntegralSpecialization
import OAI.Geometry.CylinderCovering.Nilpotent.ApexBridge
import OAI.Geometry.CylinderCovering.Convexity.TetrahedronIdentification

namespace OAI

noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace CylinderCovering.Nilpotent
open RuledApproximation

lemma complete_signed_cover {k σ ρ ε : ℝ} (hk : 0 ≤ k)
    (hσ : |σ| ≤ 1) (hsq : (σ*k)^2 = k^2)
    (hρ : 0 < ρ) (hρhalf : ρ ≤ 1/2) (hε : 0 < ε)
    (hbudget : 32*(1+k/2)^2*ρ ≤ ε) :
    HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap (Real.sqrt 2) '' signedSweep (σ*k) k)
      (Real.sqrt 2*(I k+ε)) := by
  have hh : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  exact complete_signed_cover_of_estimates (σ*k) k (I k) hh hρ hε
    (truncatedLabels_weight_integral_le hk hsq hρ hρhalf)
    (NilpotentApexNet.signed_apex_cover_budget hh hk hρ (by linarith) hσ hbudget)

theorem finite_counterexample_at_parameter {k : ℝ}
    (hk : 0 < k) (hksmall : k < 1/1920) :
    ∃ n : ℕ, ∃ C : Fin n → Cylinder,
      (∀ i, (C i).parallelogram ∧ IsCompact (C i).base ∧ Convex ℝ (C i).base) ∧
      tetrahedron ⊆ familySet C ∧
      familyArea C < (1/2)*minimumShadowArea tetrahedron := by
  obtain ⟨ε,ρ,hε,hslack,hρ,hρhalf,hcollar⟩ :=
    exists_padding_and_collar hk (integral_lt_quarter hk hksmall)
  have hbudget : 32*(1+k/2)^2*ρ ≤ ε := by nlinarith
  have hpos : HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap (Real.sqrt 2) '' signedSweep k k)
      (Real.sqrt 2*(I k+ε)) := by
    simpa using complete_signed_cover (σ := 1) hk.le (by norm_num)
      (by ring) hρ hρhalf.le hε hbudget
  have hneg : HasFiniteCover Cylinder.parallelogram
      (firstPhysicalMap (Real.sqrt 2) '' signedSweep (-k) k)
      (Real.sqrt 2*(I k+ε)) := by
    simpa using complete_signed_cover (σ := -1) hk.le (by norm_num)
      (by ring) hρ hρhalf.le hε hbudget
  obtain ⟨n,C,hC,hcover,hcost⟩ := finite_counterexample_of_signed_covers hk
    (by linarith) hslack hpos hneg
  refine ⟨n,C,fun i => ⟨hC i,(hC i).isCompact,(hC i).convex⟩,hcover,?_⟩
  rw [ruled_tetrahedron_minimum_shadow]
  linarith

theorem finite_counterexample :
    ∃ n : ℕ, ∃ C : Fin n → Cylinder,
      (∀ i, (C i).parallelogram ∧ IsCompact (C i).base ∧ Convex ℝ (C i).base) ∧
      tetrahedron ⊆ familySet C ∧
      familyArea C < (1/2)*minimumShadowArea tetrahedron := by
  exact finite_counterexample_at_parameter (k := 1/3840) (by norm_num) (by norm_num)

lemma relativeCost_le_normalized_area {n : ℕ} (C : Fin n → Cylinder) :
    relativeCost tetrahedron C ≤ familyArea C / Real.sqrt 2 := by
  unfold relativeCost familyArea
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  apply div_le_div_of_nonneg_left
  · exact ENNReal.toReal_nonneg
  · exact Real.sqrt_pos.mpr (by norm_num)
  · exact ruled_tetrahedron_shadow_lower (C i).unit_axis

theorem normalized_finite_counterexample :
    ∃ n : ℕ, ∃ C : Fin n → Cylinder,
      (∀ i, (C i).parallelogram ∧ IsCompact (C i).base ∧ Convex ℝ (C i).base) ∧
      tetrahedron ⊆ familySet C ∧
      familyArea C < minimumShadowArea tetrahedron / 2 ∧
      relativeCost tetrahedron C < 1/2 := by
  obtain ⟨n,C,hC,hcover,hcost⟩ := finite_counterexample
  have hroot : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨n,C,hC,hcover,by linarith,?_⟩
  apply lt_of_le_of_lt (relativeCost_le_normalized_area C)
  apply (div_lt_iff₀ hroot).2
  rwa [ruled_tetrahedron_minimum_shadow] at hcost

end CylinderCovering.Nilpotent

end

end OAI
