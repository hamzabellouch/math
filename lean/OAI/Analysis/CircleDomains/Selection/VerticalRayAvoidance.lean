import OAI.Analysis.CircleDomains.Topology.HalfPlaneRay

namespace OAI

/-! The common angular strip bound makes all sufficiently far translates
miss each vertical segment to the real boundary. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

private theorem vertical_im_nonneg (x y : ℝ) (hy : 0 ≤ y) (t : PathTime) :
    0 ≤ ((x : ℂ) + ((t : ℝ) * y : ℝ) * Complex.I).im := by
  simpa using mul_nonneg t.property.1 hy

def verticalCayleyPath (x y : ℝ) (hy : 0 ≤ y) : C(PathTime, ℂ) :=
  ⟨fun t => halfPlaneDisk ((x : ℂ) + ((t : ℝ) * y : ℝ) * Complex.I),
    continuousOn_halfPlaneDisk.comp_continuous
      (continuous_const.add ((Complex.continuous_ofReal.comp
        (continuous_subtype_val.mul_const y)).mul continuous_const))
      (vertical_im_nonneg x y hy)⟩

theorem verticalCayleyPath_norm_le (x y : ℝ) (hy : 0 ≤ y) (t : PathTime) :
    ‖verticalCayleyPath x y hy t‖ ≤ 1 := halfPlaneDisk_norm_le (vertical_im_nonneg x y hy t)

@[simp] theorem verticalCayleyPath_zero (x y : ℝ) (hy : 0 ≤ y) :
    verticalCayleyPath x y hy 0 = halfPlaneDisk x := by simp [verticalCayleyPath]

@[simp] theorem verticalCayleyPath_one (x y : ℝ) (hy : 0 ≤ y) :
    verticalCayleyPath x y hy 1 = halfPlaneDisk ((x : ℂ) + (y : ℂ) * Complex.I) := by
  simp [verticalCayleyPath]

theorem verticalCayleyPath_common_strip_bound
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (Y : ℝ) :
    ∃ M : ℝ, ∀ x y : ℝ, ∀ hy : 0 ≤ y, y ≤ Y → ∀ γ : K, ∀ k : ℤ,
      ¬ Disjoint (range (verticalCayleyPath x y hy))
        (range (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut) →
      |x - (k : ℝ)| ≤ M := by
  obtain ⟨M, hM⟩ := compact_disk_rays_angle_bound_on_strip K hK hKS Y
  refine ⟨M, ?_⟩
  intro x y hy hyY γ k hh
  obtain ⟨z, ⟨s, hs⟩, ⟨t, ht⟩⟩ := Set.not_disjoint_iff.mp hh
  have he : verticalCayleyPath x y hy s =
      (translatedHalfPlaneRay γ.val (hKS γ.property) k).compactify t := hs.trans ht.symm
  have hnonneg := vertical_im_nonneg x y hy s
  have htop : t < ⊤ := by
    by_contra hn
    have het : t = ⊤ := top_le_iff.mp (not_lt.mp hn)
    rw [het, HalfPlaneRay.compactify_top] at he
    exact halfPlaneDisk_ne_one hnonneg he
  rw [HalfPlaneRay.compactify, dite_eq_left htop] at he
  have hc := halfPlaneDisk_injOn hnonneg
    ((translatedHalfPlaneRay γ.val (hKS γ.property) k).nonneg ⟨t, htop⟩) he
  have hdep : diskRayDepth γ.val ⟨t, htop⟩ = (s : ℝ) * y := by
    have hi := congrArg Complex.im hc
    simpa only [verticalCayleyPath, ContinuousMap.coe_mk, translatedHalfPlaneRay,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add,
      Complex.intCast_im, diskRayComplex_im] using hi.symm
  have hdle : diskRayDepth γ.val ⟨t, htop⟩ ≤ y := by
    rw [hdep]
    exact mul_le_of_le_one_left hy s.property.2
  have hre : x = diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨t, htop⟩ + (k : ℝ) := by
    have hr := congrArg Complex.re hc
    simpa [verticalCayleyPath, translatedHalfPlaneRay, diskRayComplex] using hr
  have hb := hM γ ⟨t, htop⟩ (hdle.trans hyY)
  have hsub : x - (k : ℝ) =
      diskRayAngle γ.val (hKS γ.property).1 (hKS γ.property).2.2.1 ⟨t, htop⟩ := by linarith
  rwa [hsub]

theorem verticalCayleyPath_ray_intersection_strip_bound
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (x y Y : ℝ) (hy : 0 ≤ y) (hyY : y ≤ Y) :
    ∃ M : ℝ, ∀ γ : K, ∀ k : ℤ,
      ¬ Disjoint (range (verticalCayleyPath x y hy))
        (range (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut) →
      |x - (k : ℝ)| ≤ M := by
  obtain ⟨M, hM⟩ := verticalCayleyPath_common_strip_bound K hK hKS Y
  exact ⟨M, hM x y hy hyY⟩

theorem verticalCayleyPath_ray_intersection_bound
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (x y : ℝ) (hy : 0 ≤ y) :
    ∃ M : ℝ, ∀ γ : K, ∀ k : ℤ,
      ¬ Disjoint (range (verticalCayleyPath x y hy))
        (range (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut) →
      |x - (k : ℝ)| ≤ M :=
  verticalCayleyPath_ray_intersection_strip_bound K hK hKS x y y hy le_rfl

theorem far_translates_miss_verticalCayleyPath
    (K : Set C(PathTime, ℂ)) (hK : IsCompact K) (hKS : K ⊆ diskTerminalArcSet)
    (x y : ℝ) (hy : 0 ≤ y) :
    ∃ M : ℝ, ∀ γ : K, ∀ k : ℤ, M < |x - (k : ℝ)| →
      Disjoint (range (verticalCayleyPath x y hy))
        (range (translatedHalfPlaneRay γ.val (hKS γ.property) k).crosscut) := by
  obtain ⟨M, hM⟩ := verticalCayleyPath_ray_intersection_bound K hK hKS x y hy
  refine ⟨M, ?_⟩
  intro γ k hk
  by_contra hh
  exact (not_le_of_gt hk) (hM γ k hh)

end CircleDomainRigidity

end

end OAI
