import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerShootingLimit
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexCoreConvergence

namespace OAI

/-! Full complex C1 convergence of the actual inner shooting profiles. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radialShootingInner_complex_C1_limit (s : ℕ → ℕ) (hs : StrictMono s)
    (w : ℕ → RadialShootingDisk) (w₀ : RadialShootingDisk)
    (hw : Tendsto w atTop (𝓝 w₀)) :
    TendstoUniformlyOn (fun i => radialShootingInnerComplex (s i) (w i))
      (fun r => if r ≤ radialShootingR w₀ then 1 else (radialFreeInnerJet w₀ r).1)
      atTop (Icc 0 innerBoundaryRadius) ∧
    TendstoUniformlyOn (fun i => deriv (radialShootingInnerComplex (s i) (w i)))
      (fun r => if r ≤ radialShootingR w₀ then 0 else (radialFreeInnerJet w₀ r).2)
      atTop (Icc 0 innerBoundaryRadius) := by
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
  obtain ⟨hb₀,hR₀,hu,hlu,hwidth,hshell⟩ := radialShooting_geometry w₀
  have hslt : radialShootingR w₀ < innerBoundaryRadius := by linarith [hshell.1]
  obtain ⟨hJ,hFI,hGI,hbound,_⟩ := radialFreeInnerJet_spec w₀
  have hconv := radial_coupled_complex_C1_convergence innerBoundaryRadius (radialShootingR w₀)
    (radialShootingB w₀) innerBoundaryRadius_lower hu hR₀ hslt hwidth hb₀
    (fun r => (radialFreeInnerJet w₀ r).1) (fun r => (radialFreeInnerJet w₀ r).2)
    hJ.fst hJ.snd hFI hGI (fun r _ => hbound r)
    (fun i => radialShootingInnerData (s i) (w i)) (fun i => radialShootingInnerData_R (s i) (w i))
    (fun i => radialShootingInnerAmplitude (s i) (w i))
    (fun i => by simpa only [radialShootingInnerData_R] using
      radialShootingInnerAmplitude_spec (s i) (w i)) hp hc hb hlo
  simpa only [radialShootingInnerComplex] using hconv

end DefocusingNLS

end OAI
