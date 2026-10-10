import OAI.Analysis.CircleDomains.Topology.PhysicalCollarCoordinates

namespace OAI

/-! Punctured disk collars for a continuous physical coordinate, including
coordinates pulled back through the component quotient. Boundary avoidance
suffices: compactness supplies one common inward width. -/

open Set Function Filter
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem exists_punctured_physical_collar
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) (F : C(Sphere, ℂ))
    (hbound : ∀ z ∈ closure (jordanInterior H), ‖F (z : Sphere)‖ ≤ 1)
    (hboundary : ∀ z ∈ frontier (jordanInterior H), F (z : Sphere) ≠ 0) :
    ∃ η > 0, η ≤ C.width ∧
      ContinuousOn (fun p : ℝ × ℝ => F (C.curve |p.1| p.2 : Sphere))
        (Ioo (-η) η ×ˢ univ) ∧
      (∀ p ∈ Ioo (-η) η ×ˢ (univ : Set ℝ), F (C.curve |p.1| p.2 : Sphere) ≠ 0) ∧
      (∀ p ∈ Ioo (-η) η ×ˢ (univ : Set ℝ), ‖F (C.curve |p.1| p.2 : Sphere)‖ ≤ 1) := by
  let O : Set ℂ := {z | F (z : Sphere) ≠ 0}
  have hO : IsOpen O := isOpen_compl_singleton.preimage (F.continuous.comp OnePoint.continuous_coe)
  obtain ⟨η, hη, hηw, hnear⟩ := C.eventually_in_boundary_neighborhood hO hboundary
  have habs {ρ : ℝ} (hρ : ρ ∈ Ioo (-η) η) : |ρ| ∈ Icc 0 C.width :=
    ⟨abs_nonneg _, (abs_lt.mpr hρ).le.trans hηw⟩
  refine ⟨η, hη, hηw, ?_, ?_, ?_⟩
  · apply (F.continuous.comp OnePoint.continuous_coe).comp_continuousOn
    apply C.folded_continuous.mono
    intro p hp
    exact ⟨⟨lt_of_le_of_lt (neg_le_neg hηw) hp.1.1, hp.1.2.trans_le hηw⟩, hp.2⟩
  · intro p hp
    have hi : |p.1| ∈ Icc (0 : ℝ) η := ⟨abs_nonneg _, (abs_lt.mpr hp.1).le⟩
    have hγ := C.parametrization |p.1| (habs hp.1)
    have he : C.curve |p.1| (Int.fract p.2) = C.curve |p.1| p.2 := by
      simpa only [Int.fract, mul_one] using hγ.periodic.sub_int_mul_eq (x := p.2) ⌊p.2⌋
    have hh := hnear |p.1| hi (Int.fract p.2) ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
    change F (C.curve |p.1| (Int.fract p.2) : Sphere) ≠ 0 at hh
    rwa [he] at hh
  · intro p hp
    exact hbound _ (C.curve_mem_original_closure (habs hp.1) p.2)

end CircleDomainRigidity

end

end OAI
