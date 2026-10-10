import OAI.Analysis.CircleDomains.Rigidity.InwardMaskSelection
import OAI.Analysis.CircleDomains.Topology.BoundedJordanExtension
import OAI.Analysis.CircleDomains.Topology.BoundaryCollarLift

namespace OAI

/-! The centered Jordan coordinate on the constructed inward collar is a
jointly continuous punctured-disk family. Compact retention keeps the
singularity strictly on the inside of every small collar. -/

open Set Function Filter Metric
open scoped Topology

noncomputable section
namespace CircleDomainRigidity

 theorem PositiveJordanParametrization.mem_frontier
    {H : ℂ ≃ₜ ℂ} {γ : ℝ → ℂ} (hγ : PositiveJordanParametrization H γ) (t : ℝ) :
    γ t ∈ frontier (jordanInterior H) := by
  have he : γ (Int.fract t) = γ t := by
    simpa only [Int.fract, mul_one] using hγ.periodic.sub_int_mul_eq (x := t) ⌊t⌋
  rw [← he]
  exact hγ.boundary ▸ mem_image_of_mem γ
    (show Int.fract t ∈ Icc (0 : ℝ) 1 from ⟨Int.fract_nonneg t, (Int.fract_lt_one t).le⟩)

 theorem RegularJordanInwardCollar.curve_mem_original_closure
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) {ρ : ℝ}
    (hρ : ρ ∈ Icc 0 C.width) (t : ℝ) : C.curve ρ t ∈ closure (jordanInterior H) := by
  have hm := frontier_subset_closure ((C.parametrization ρ hρ).mem_frontier t)
  by_cases hz : ρ = 0
  · subst ρ
    simpa only [C.disk_zero] using hm
  · exact subset_closure (C.inward ρ ⟨lt_of_le_of_ne hρ.1 (Ne.symm hz), hρ.2⟩ hm)

 theorem exists_centered_punctured_collar_family
    {H : ℂ ≃ₜ ℂ} (C : RegularJordanInwardCollar H) {b : ℂ} (hb : b ∈ jordanInterior H)
    (F : C(Sphere, ℂ))
    (hF : EqOn F (centeredJordanCoordinate H (b : Sphere))
      (closure (((↑) : ℂ → Sphere) '' jordanInterior H))) :
    ∃ η > 0, η ≤ C.width ∧
      ContinuousOn (fun p : ℝ × ℝ => F (C.curve |p.1| p.2 : Sphere))
        (Ioo (-η) η ×ˢ univ) ∧
      (∀ p ∈ Ioo (-η) η ×ˢ (univ : Set ℝ), F (C.curve |p.1| p.2 : Sphere) ≠ 0) ∧
      (∀ p ∈ Ioo (-η) η ×ˢ (univ : Set ℝ), ‖F (C.curve |p.1| p.2 : Sphere)‖ ≤ 1) ∧
      ∀ ρ ∈ Ioo (-η) η, F (C.curve |ρ| 1 : Sphere) = F (C.curve |ρ| 0 : Sphere) := by
  have hbs : (b : Sphere) ∈ ((↑) : ℂ → Sphere) '' jordanInterior H := ⟨b, hb, rfl⟩
  obtain ⟨η, hη, hηw, hretain⟩ := C.retains_compact {b} isCompact_singleton
    (singleton_subset_iff.mpr hb)
  have habs {ρ : ℝ} (hρ : ρ ∈ Ioo (-η) η) : |ρ| ∈ Icc 0 C.width :=
    ⟨abs_nonneg _, (abs_lt.mpr hρ).le.trans hηw⟩
  have hbinner {ρ : ℝ} (hρ : ρ ∈ Ioo (-η) η) : b ∈ jordanInterior (C.disk |ρ|) := by
    by_cases hz : ρ = 0
    · simpa only [hz, abs_zero, C.disk_zero] using hb
    · exact hretain |ρ| ⟨abs_pos.mpr hz, (abs_lt.mpr hρ).le⟩ (mem_singleton b)
  have hcl {ρ : ℝ} (hρ : ρ ∈ Ioo (-η) η) (t : ℝ) :
      (C.curve |ρ| t : Sphere) ∈ closure (((↑) : ℂ → Sphere) '' jordanInterior H) := by
    rw [closure_sphere_image_jordanInterior]
    exact ⟨_, C.curve_mem_original_closure (habs hρ) t, rfl⟩
  have hnonzero {ρ : ℝ} (hρ : ρ ∈ Ioo (-η) η) (t : ℝ) :
      F (C.curve |ρ| t : Sphere) ≠ 0 := by
    intro hz
    have he : centeredJordanCoordinate H (b : Sphere) (C.curve |ρ| t : Sphere) =
        centeredJordanCoordinate H (b : Sphere) (b : Sphere) := by
      rw [← hF (hcl hρ t), hz, centeredJordanCoordinate_self]
    have heq := centeredJordanCoordinate_injOn H hbs (hcl hρ t) (subset_closure hbs) he
    have hc : C.curve |ρ| t = b := OnePoint.coe_injective heq
    have hf := (C.parametrization |ρ| (habs hρ)).mem_frontier t
    rw [(jordanInterior_isOpen (C.disk |ρ|)).frontier_eq] at hf
    exact hf.2 (hc.symm ▸ hbinner hρ)
  refine ⟨η, hη, hηw, ?_, ?_, ?_, ?_⟩
  · apply (F.continuous.comp OnePoint.continuous_coe).comp_continuousOn
    apply C.folded_continuous.mono
    intro p hp
    exact ⟨⟨lt_of_le_of_lt (neg_le_neg hηw) hp.1.1, hp.1.2.trans_le hηw⟩, hp.2⟩
  · intro p hp
    exact hnonzero hp.1 p.2
  · intro p hp
    rw [hF (hcl hp.1 p.2)]
    exact centeredJordanCoordinate_norm_le H hbs (hcl hp.1 p.2)
  · intro ρ hρ
    exact congrArg (fun z : ℂ => F (z : Sphere)) (C.parametrization |ρ| (habs hρ)).periodic.eq

end CircleDomainRigidity

end

end OAI
