import OAI.Analysis.CircleDomains.Topology.UniformSelectedCollar

namespace OAI

/-! The uniform selected-circle collar in radial coordinates. -/
open Set Function Filter Metric Complex
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_radial_circle_point {c y:ℂ} {r:ℝ} (hr:0<r) (hy:r<‖y-c‖) :
    ∃w∈sphere c r,dist y w=‖y-c‖-r := by
  let v := NormedSpace.normalize (y-c)
  let w := c+r • v
  have hne : y-c≠0 := norm_pos_iff.mp (hr.trans hy)
  have hv : ‖v‖=1 := NormedSpace.norm_normalize hne
  have hw : w∈sphere c r := by
    apply mem_sphere_iff_norm.mpr
    dsimp [w]
    rw [add_sub_cancel_left,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr,hv,mul_one]
  refine ⟨w,hw,?_⟩
  have he : y-w=(‖y-c‖-r) • v := by
    calc
      y-w=(y-c)-r • v := by dsimp [w];abel
      _=‖y-c‖ • v-r • v := by rw [NormedSpace.norm_smul_normalize]
      _=(‖y-c‖-r) • v := (sub_smul _ _ _).symm
  rw [dist_eq_norm,he,norm_smul,Real.norm_eq_abs,abs_of_pos (sub_pos.mpr hy),hv,mul_one]

namespace FiniteJordanConfiguration
variable {m:ℕ} {C:FiniteJordanConfiguration (Fin (m+1))} {i:Fin (m+1)}

lemma PhaseCollar.uniform_selected_annulus (P:PhaseCollar C i) :
    ∃ε:ℝ,0<ε ∧ ∀n y,
      selectedRadius C (cyclicSchedule m) (visitTime n i)<
        ‖y-selectedCenter C (cyclicSchedule m) (visitTime n i)‖ →
      ‖y-selectedCenter C (cyclicSchedule m) (visitTime n i)‖<
        selectedRadius C (cyclicSchedule m) (visitTime n i)+ε →
      y∈(iterate C (cyclicSchedule m) (visitTime n i+1)).planeRegion := by
  obtain ⟨ε,hε,hcollar⟩ := P.uniform_selected_collar
  refine ⟨ε,hε,?_⟩
  intro n y hinner houter
  apply hcollar n y hinner
  obtain ⟨w,hw,he⟩ := exists_radial_circle_point
    (selectedRadius_pos C (cyclicSchedule m) (visitTime n i)) hinner
  exact ⟨w,hw,by rw [he];linarith⟩

lemma selectedCircles_common_collar {m:ℕ} (C:FiniteJordanConfiguration (Fin (m+1)))
    (ha:∀i,IsAnalyticJordanCap (C.hole i)) :
    ∃ε:ℝ,0<ε ∧ ∀n (i:Fin (m+1)) y,
      selectedRadius C (cyclicSchedule m) (visitTime n i)<
        ‖y-selectedCenter C (cyclicSchedule m) (visitTime n i)‖ →
      ‖y-selectedCenter C (cyclicSchedule m) (visitTime n i)‖<
        selectedRadius C (cyclicSchedule m) (visitTime n i)+ε →
      y∈(iterate C (cyclicSchedule m) (visitTime n i+1)).planeRegion := by
  classical
  have hex (i:Fin (m+1)) : ∃ε:ℝ,0<ε ∧ ∀n y,
      selectedRadius C (cyclicSchedule m) (visitTime n i)<
        ‖y-selectedCenter C (cyclicSchedule m) (visitTime n i)‖ →
      ‖y-selectedCenter C (cyclicSchedule m) (visitTime n i)‖<
        selectedRadius C (cyclicSchedule m) (visitTime n i)+ε →
      y∈(iterate C (cyclicSchedule m) (visitTime n i+1)).planeRegion := by
    obtain ⟨P⟩ := phaseCollar_nonempty C ha i
    exact P.uniform_selected_annulus
  choose ε hε hcollar using hex
  let S : Finset ℝ := Finset.univ.image ε
  have hS : S.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  refine ⟨S.min' hS,?_,?_⟩
  · exact (Finset.lt_min'_iff _ _).mpr (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact hε i)
  · intro n i y hinner houter
    apply hcollar i n y hinner
    have hle : S.min' hS≤ε i := Finset.min'_le _ _
      (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
    linarith

end FiniteJordanConfiguration
end CircleDomainRigidity

end

end OAI
