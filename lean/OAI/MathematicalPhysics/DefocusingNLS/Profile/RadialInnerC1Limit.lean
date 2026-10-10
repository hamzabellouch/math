import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerShootingLimit

namespace OAI

/-! Full inner C¹ convergence for the actual shooting family, including its flat core. -/

open Set Filter
namespace DefocusingNLS

theorem radialShootingInner_C1_limit (s : ℕ → ℕ) (hs : StrictMono s)
    (w : ℕ → RadialShootingDisk) (w₀ : RadialShootingDisk)
    (hw : Tendsto w atTop (nhds w₀)) :
    ∃ A D : ℝ → ℝ, Continuous A ∧ Continuous D ∧
      TendstoUniformlyOn (fun i => radialShootingInnerAmplitude (s i) (w i)) A
        atTop (Icc 0 innerBoundaryRadius) ∧
      TendstoUniformlyOn (fun i => deriv (radialShootingInnerAmplitude (s i) (w i))) D
        atTop (Icc 0 innerBoundaryRadius) ∧
      EqOn A (fun _ => 1) (Icc 0 (radialShootingR w₀)) ∧ D (radialShootingR w₀)=0 ∧
      EqOn A (fun r => ‖(radialFreeInnerJet w₀ r).1‖)
        (Icc (radialShootingR w₀) innerBoundaryRadius) := by
  have hsn : Tendsto (fun i => s i+radialInnerShootingThreshold) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_add_right _ _) hs.tendsto_atTop
  have hp : Tendsto (fun i => (radialShootingInnerData (s i) (w i)).p) atTop atTop := by
    simp only [radialShootingInnerData_p]
    exact tendsto_atTop_mono (fun i => by omega) hs.tendsto_atTop
  have hc : Tendsto (fun i => (radialShootingInnerData (s i) (w i)).c) atTop (nhds 6) := by
    simp only [radialShootingInnerData_c]
    have ht := ((tendsto_one_div_atTop_nhds_zero_nat :
      Tendsto (fun n : ℕ => 1/(n : ℝ)) atTop (nhds 0)).comp hsn).const_sub 6
    simpa only [Function.comp_def,sub_zero] using ht
  have hbc : Continuous radialShootingB := by unfold radialShootingB; fun_prop
  have hb : Tendsto (fun i => (radialShootingInnerData (s i) (w i)).b) atTop
      (nhds (radialShootingB w₀)) := by
    simpa only [radialShootingInnerData_b] using! hbc.continuousAt.tendsto.comp hw
  have hlo : Tendsto (fun i => (radialShootingInnerData (s i) (w i)).lo) atTop
      (nhds ‖(radialFreeInnerJet w₀ innerBoundaryRadius).1‖) := by
    simpa only [radialShootingInnerData_lo] using!
      continuous_radialFreeInner_boundary.fst.norm.continuousAt.tendsto.comp hw
  obtain ⟨hb₀,hR₀,hu,hlu,hwidth,_hshell⟩ := radialShooting_geometry w₀
  obtain ⟨hJ,hFI,hGI,hbound,hlo₀,hhi₀⟩ := radialFreeInnerJet_spec w₀
  apply radial_coupled_C1_core_convergence innerBoundaryRadius (radialShootingR w₀)
    (radialShootingB w₀) innerBoundaryRadius_lower hu hR₀ hlu hwidth hb₀
    (fun r => (radialFreeInnerJet w₀ r).1) (fun r => (radialFreeInnerJet w₀ r).2)
    hJ.fst hJ.snd hFI hGI (fun r _ => hbound r) (by linarith)
    (fun i => radialShootingInnerData (s i) (w i)) (fun i => radialShootingInnerData_R (s i) (w i))
    (fun i => radialShootingInnerAmplitude (s i) (w i))
    (fun i => by simpa only [radialShootingInnerData_R] using
      radialShootingInnerAmplitude_spec (s i) (w i)) hp hc hb hlo

end DefocusingNLS

end OAI
