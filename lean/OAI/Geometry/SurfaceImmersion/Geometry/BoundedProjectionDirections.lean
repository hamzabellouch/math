import OAI.Geometry.SurfaceImmersion.Geometry.ProjectionDirections

namespace OAI

/-! Compact direction parameters for kernels of maps on a surface tangent plane. -/
noncomputable section
open Set
open scoped ContDiff Topology
namespace ClosedSurfaceR4.FiniteOrderSmoothing
open JetPolynomial (Base)

lemma exists_bounded_tangentRay {v : Base} (hv : v ≠ 0) :
    ∃ (b : Bool) (t c : ℝ), t ∈ Icc (-1 : ℝ) 1 ∧ c ≠ 0 ∧
      v = c • tangentRay b t := by
  by_cases h : |v 1| ≤ |v 0|
  · have h0 : v 0 ≠ 0 := by
      intro h0
      have h1 : v 1 = 0 := abs_nonpos_iff.mp (by simpa only [h0,abs_zero] using h)
      apply hv
      ext i
      fin_cases i <;> simp [h0,h1]
    have ht : |v 1 / v 0| ≤ 1 := by
      rw [abs_div]
      exact (div_le_one (abs_pos.mpr h0)).mpr h
    refine ⟨false,v 1 / v 0,v 0,abs_le.mp ht,h0,?_⟩
    ext i
    fin_cases i
    · change v 0 = v 0 * 1
      rw [mul_one]
    · change v 1 = v 0 * (v 1 / v 0)
      field_simp
  · have h1 : v 1 ≠ 0 := by
      intro h1
      apply h
      simpa only [h1,abs_zero] using abs_nonneg (v 0)
    have ht : |v 0 / v 1| ≤ 1 := by
      rw [abs_div]
      exact (div_le_one (abs_pos.mpr h1)).mpr (le_of_lt (lt_of_not_ge h))
    refine ⟨true,v 0 / v 1,v 1,abs_le.mp ht,h1,?_⟩
    ext i
    fin_cases i
    · change v 0 = v 1 * (v 0 / v 1)
      field_simp
    · change v 1 = v 1 * 1
      rw [mul_one]

lemma exists_bounded_tangentRay_in_kernel {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : Base →L[ℝ] V) (hL : ¬ Function.Injective L) :
    ∃ (b : Bool) (t : ℝ), t ∈ Icc (-1 : ℝ) 1 ∧ L (tangentRay b t) = 0 := by
  change ¬ (∀ u v : Base, L u = L v → u = v) at hL
  push Not at hL
  obtain ⟨u,v,he,hne⟩ := hL
  have hv : u-v ≠ 0 := sub_ne_zero.mpr hne
  have hz : L (u-v) = 0 := by rw [map_sub,he,sub_self]
  obtain ⟨b,t,c,ht,hc,hec⟩ := exists_bounded_tangentRay hv
  refine ⟨b,t,ht,?_⟩
  rw [hec,map_smul] at hz
  exact (smul_eq_zero.mp hz).resolve_left hc

end ClosedSurfaceR4.FiniteOrderSmoothing

end

end OAI
