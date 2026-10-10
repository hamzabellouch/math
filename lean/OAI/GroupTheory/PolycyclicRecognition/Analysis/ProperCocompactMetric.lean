import OAI.GroupTheory.PolycyclicRecognition.Analysis.LinearMetricChains
import Mathlib.Topology.Maps.Proper.Basic

namespace OAI

/-!
# Metric comparison through a proper cocompact homomorphism

Properness bounds preimages of target balls. A coarse section and explicit
linear metric chains then give the lower quasi-isometry inequality. Together
with the continuous-homomorphism upper bound this is the metric part of the
Milnor--Švarc comparison, proved here without a recognition hypothesis.
-/

noncomputable section

namespace PolycyclicRecognition

open Metric Set

variable {G H : Type*} [Group G] [Group H] [MetricSpace G] [MetricSpace H]
  [IsIsometricSMul G G] [IsIsometricSMul H H]

/-- A proper homomorphism has uniformly bounded preimages of bounded
group differences. Compactness of the kernel is included in this argument. -/
theorem properHom_bounded_preimage_steps [ProperSpace H]
    (f : G →* H) (hproper : IsProperMap f) (R : ℝ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ x y, dist (f x) (f y) ≤ R → dist x y ≤ D := by
  have hcompact := hproper.isCompact_preimage (isCompact_closedBall (1 : H) R)
  obtain ⟨D, hD⟩ := hcompact.bddAbove_image (continuous_const.dist continuous_id).continuousOn
  refine ⟨max D 0, le_max_right _ _, fun x y hxy => ?_⟩
  have hmem : x⁻¹ * y ∈ f ⁻¹' closedBall (1 : H) R := by
    change dist (f (x⁻¹ * y)) 1 ≤ R
    rw [map_mul, map_inv, dist_comm, dist_one_groupDifference]
    exact hxy
  have hb : dist (1 : G) (x⁻¹ * y) ≤ D := hD (mem_image_of_mem _ hmem)
  rw [dist_one_groupDifference] at hb
  exact hb.trans (le_max_left _ _)

omit [MetricSpace G] [IsIsometricSMul G G] in
/-- Cocompactness, expressed as a compact cover of right image cosets,
gives the metric coarse-surjectivity radius. -/
theorem compact_image_cover_coarsely_surjective (f : G →* H)
    (K : Set H) (hK : IsCompact K)
    (hcover : ∀ h : H, ∃ (g : G) (k : H), k ∈ K ∧ f g * k = h) :
    ∃ E : ℝ, 0 ≤ E ∧ ∀ h : H, ∃ g : G, dist h (f g) ≤ E := by
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (1 : H)
  refine ⟨max R 0, le_max_right _ _, fun h => ?_⟩
  obtain ⟨g, k, hk, rfl⟩ := hcover h
  refine ⟨g, ?_⟩
  have hkR : dist k 1 ≤ R := hR hk
  calc
    dist (f g * k) (f g) = dist k 1 := by simpa only [mul_one] using dist_mul_left (f g) k 1
    _ ≤ max R 0 := hkR.trans (le_max_left _ _)

/-- The lower quasi-isometry inequality is a consequence of properness,
coarse surjectivity, and target chains. No injectivity is required. -/
theorem properHom_coarse_lower [ProperSpace H] (C : LinearMetricChains H)
    (f : G →* H) (hproper : IsProperMap f) {E : ℝ}
    (hsurj : ∀ h, ∃ g, dist h (f g) ≤ E) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      ∀ x y, dist x y ≤ A * dist (f x) (f y) + B := by
  choose r hr using hsurj
  obtain ⟨D, hD, hpre⟩ := properHom_bounded_preimage_steps f hproper (E + C.step + E)
  obtain ⟨L, hL, herror⟩ := properHom_bounded_preimage_steps f hproper E
  have hstep : ∀ x y : H, dist x y ≤ C.step → dist (r x) (r y) ≤ D := by
    intro x y hxy
    apply hpre
    calc
      dist (f (r x)) (f (r y)) ≤
          dist (f (r x)) x + dist x y + dist y (f (r y)) := dist_triangle4 _ _ _ _
      _ ≤ E + C.step + E := by
        exact add_le_add (add_le_add ((dist_comm (f (r x)) x).trans_le (hr x)) hxy) (hr y)
  have hrbound := C.coarseLipschitz r hD hstep
  have herr (x : G) : dist x (r (f x)) ≤ L := herror x (r (f x)) (hr (f x))
  refine ⟨D * C.slope, D * C.error + (L + L),
    mul_nonneg hD C.slope_nonneg,
    add_nonneg (mul_nonneg hD C.error_nonneg) (add_nonneg hL hL), fun x y => ?_⟩
  calc
    dist x y ≤ dist x (r (f x)) + dist (r (f x)) (r (f y)) + dist (r (f y)) y :=
      dist_triangle4 _ _ _ _
    _ ≤ L + ((D * C.slope) * dist (f x) (f y) + D * C.error) + L := by
      exact add_le_add (add_le_add (herr x) (hrbound (f x) (f y)))
        ((dist_comm (r (f y)) y).trans_le (herr y))
    _ = (D * C.slope) * dist (f x) (f y) + (D * C.error + (L + L)) := by ring

/-- A continuous proper homomorphism with compact image-coset cover is a
metric quasi-isometry when both metrics have the stated linear chains. -/
theorem proper_cocompact_hom_quasiIsometry [ProperSpace G] [ProperSpace H]
    (CG : LinearMetricChains G) (CH : LinearMetricChains H)
    (f : G →* H) (hf : Continuous f) (hproper : IsProperMap f)
    (K : Set H) (hK : IsCompact K)
    (hcover : ∀ h : H, ∃ (g : G) (k : H), k ∈ K ∧ f g * k = h) :
    ∃ A B A' B' E : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ A' ∧ 0 ≤ B' ∧ 0 ≤ E ∧
      (∀ x y, dist (f x) (f y) ≤ A * dist x y + B) ∧
      (∀ x y, dist x y ≤ A' * dist (f x) (f y) + B') ∧
      (∀ h, ∃ g, dist h (f g) ≤ E) := by
  obtain ⟨E, hE, hsurj⟩ := compact_image_cover_coarsely_surjective f K hK hcover
  obtain ⟨A, B, hA, hB, hupper⟩ := continuousHom_coarseLipschitz CG f hf
  obtain ⟨A', B', hA', hB', hlower⟩ := properHom_coarse_lower CH f hproper hsurj
  exact ⟨A, B, A', B', E, hA, hB, hA', hB', hE, hupper, hlower, hsurj⟩

end PolycyclicRecognition

end

end OAI
