import Mathlib
import OAI.Analysis.Conductivity.Branching.PhysicalBlockEnergySum

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set MeasureTheory Filter Topology

lemma sourceCollarTime_pos_iff_domain (y : Fin 3 → ℝ) :
    0<sourceCollarTime y ↔ WithLp.toLp 2 y∈sourceDomain := by
  change 0<sourceCollarTime y ↔ sourceHole<sourceRadial y ∧ sourceRadial y<1 ∧ |y 2|<1
  rw [←not_le,sourceCollarTime_le_iff]
  simp only [sub_zero,mul_zero,add_zero,not_or,not_le]
  tauto

lemma sourceDomain_closure_time (y : Fin 3 → ℝ) :
    WithLp.toLp 2 y∈closure sourceDomain ↔ 0≤ sourceCollarTime y := by
  have hcoord : Continuous (fun x : R3 => (fun i : Fin 3 => x i)) :=
    continuous_pi (fun i => (EuclideanSpace.proj i).continuous)
  have hclosed : IsClosed {x : R3 | 0≤ sourceCollarTime (fun i => x i)} :=
    isClosed_le continuous_const (locallyLipschitz_sourceCollarTime.continuous.comp hcoord)
  constructor
  · intro hy
    exact closure_minimal (fun x hx => ((sourceCollarTime_pos_iff_domain _).mpr hx).le) hclosed hy
  · intro hy
    by_cases hp : 0<sourceCollarTime y
    · exact subset_closure ((sourceCollarTime_pos_iff_domain y).mp hp)
    · have he : sourceCollarTime y=0 := le_antisymm (le_of_not_gt hp) hy
      let g : ℝ → R3 := fun t => WithLp.toLp 2 (sourceAngularCollar t (sourcePhysicalAngles y))
      have hg : Continuous g := (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp
        (continuous_uncurry_sourceAngularCollar.comp (continuous_id.prodMk continuous_const))
      have hz : (0:ℝ)∈closure (Ioo 0 centralThickness) := by
        rw [closure_Ioo (show (0:ℝ)≠centralThickness by norm_num [centralThickness])]
        exact ⟨le_rfl,by norm_num [centralThickness]⟩
      have hin : g '' Ioo 0 centralThickness ⊆ sourceDomain := by
        rintro _ ⟨t,ht,rfl⟩
        apply (sourceCollarTime_pos_iff_domain _).mp
        rw [sourceAngular_time (show t∈Icc (-(1:ℝ)/100) (1/100) from
          ⟨by linarith [ht.1],ht.2.le.trans (by norm_num [centralThickness])⟩)]
        exact ht.1
      have hmem := closure_mono hin (image_closure_subset_closure_image hg ⟨0,hz,rfl⟩)
      have hright := sourcePhysicalCoordinates_right
        (show sourceCollarTime y∈Icc (-(1:ℝ)/100) (1/100) by rw [he]; norm_num)
      rw [he] at hright
      simpa only [g,hright] using hmem

theorem physicalBlockRegion_sourceDomain (y : Fin 3 → ℝ) :
    y∈physicalBlockRegion ↔ WithLp.toLp 2 y∈closure sourceDomain ∧
      ∀ k : Fin 2,WithLp.toLp 2 ((sourceChildHomeomorph (actualChildSign k)).symm y)∉sourceDomain := by
  rw [physicalBlockRegion_time_iff,sourceDomain_closure_time]
  simp only [←sourceCollarTime_pos_iff_domain,not_lt]

end ScalarConductivity

end
end

end OAI
