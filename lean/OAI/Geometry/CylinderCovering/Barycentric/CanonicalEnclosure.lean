import OAI.Geometry.CylinderCovering.Barycentric.EnclosureDefinitions
import OAI.Geometry.CylinderCovering.Barycentric.SectorFinite
import OAI.Geometry.CylinderCovering.Barycentric.Cost

namespace OAI

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace RadialCoordinates.BarycentricSector
open CylinderCovering.RadialRiemann

theorem canonical_cap_continuous (k : ℝ) : Continuous (cap k) := by
  unfold cap capPolynomial angular
  fun_prop

theorem canonical_cap_nonnegative (k t : ℝ) : 0 ≤ cap k t := by
  unfold cap capPolynomial
  positivity

theorem canonical_cap_bound (k : ℝ) {t : ℝ} (ht : t ∈ Icc (0:ℝ) 1) :
    cap k t ≤ canonicalCapBound k := by
  have h := (capPolynomial_angular_bounds ht).2
  unfold cap canonicalCapBound
  nlinarith [mul_le_mul_of_nonneg_left h (sq_nonneg k)]

theorem canonical_capMax_bounds (k : ℝ) {N : ℕ} (i : Fin N) :
    0 ≤ capMax (cap k) 0 1 N i ∧
      capMax (cap k) 0 1 N i ≤ canonicalCapBound k := by
  obtain ⟨t, ht, heq⟩ := exists_capMax_tag (by norm_num : (0:ℝ)<1)
    (canonical_cap_continuous k).continuousOn i
  rw [← heq]
  exact ⟨canonical_cap_nonnegative k t,
    canonical_cap_bound k (cell_subset (by norm_num : (0:ℝ)<1) i ht)⟩

theorem intercepts_isCompact (k c l r : ℝ) : IsCompact (intercepts k c l r) := by
  let f : (ℝ × ℝ) × ℝ → Plane := fun z =>
    z.1.2 • ray z.1.1 + (k*z.2) • (velocity z.1.1-velocity c)
  have heq : intercepts k c l r = f ''
      (AngularCaps.radialParameterSet l r (cap k) ×ˢ Icc (-1:ℝ) 1) := by
    ext z
    constructor
    · rintro ⟨t, ht, S, hS, p, hp, rfl⟩
      exact ⟨((t,S),p), ⟨⟨ht,hS⟩,hp⟩, rfl⟩
    · rintro ⟨⟨⟨t,S⟩,p⟩, ⟨⟨ht,hS⟩,hp⟩, rfl⟩
      exact ⟨t, ht, S, hS, p, hp, rfl⟩
  rw [heq]
  apply ((AngularCaps.isCompact_radialParameterSet
    (canonical_cap_continuous k).continuousOn (fun t _ => canonical_cap_nonnegative k t)).prod
      isCompact_Icc).image
  dsimp [f]
  unfold ray velocity
  fun_prop

theorem canonical_intercepts_subset_neighborhood {k : ℝ} (hk : 0 ≤ k)
    {N : ℕ} (i : Fin N) {c : ℝ} (hc : c ∈ cell 0 1 N i) :
    intercepts k c (point 0 1 N i) (point 0 1 N (i+1)) ⊆
      neighborhood (point 0 1 N i) (point 0 1 N (i+1)) k (capMax (cap k) 0 1 N i) := by
  rintro z ⟨t, ht, S, hS, p, hp, rfl⟩
  apply frozen_intercept_mem_cthickening hk (abs_le.mpr hp) hc ht hS.1
  exact hS.2.trans (le_capMax (by norm_num : (0:ℝ)<1)
    (canonical_cap_continuous k).continuousOn ht)

theorem canonical_equal_cell_area_bound {N : ℕ} (hN : 0 < N) {k : ℝ} (hk : 0 ≤ k)
    (tag : Fin N → ℝ) (htag : IsTagged 0 1 N tag)
    (W : Fin N → ℝ) (hW0 : ∀ i, 0 ≤ W i) (hW1 : ∀ i, W i ≤ 1) :
    (∑ i : Fin N, W i * volume.real
      (intercepts k (tag i) (point 0 1 N i) (point 0 1 N (i+1)))) ≤
    (∑ i : Fin N, W i*((1/(N:ℝ))*(capMax (cap k) 0 1 N i)^2/2)) +
      (18*k*canonicalCapBound k+162*k^2)/(N:ℝ) := by
  exact equal_cell_intercepted_area_bound hN hk (capMax (cap k) 0 1 N)
    (fun i => (canonical_capMax_bounds k i).1)
    (fun i => (canonical_capMax_bounds k i).2) _
    (fun i => canonical_intercepts_subset_neighborhood hk i (htag i)) W hW0 hW1

end RadialCoordinates.BarycentricSector

end

end OAI
