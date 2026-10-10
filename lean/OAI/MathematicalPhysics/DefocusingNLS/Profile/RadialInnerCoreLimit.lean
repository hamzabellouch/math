import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerDerivative
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

namespace OAI

/-! The exact core level tends to one; every limit of the actual inner profiles is flat there. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_inner_core_lower (P : RadialInnerData) (H : ℝ → ℝ)
    (hH : RadialInnerOutputSpec P.p P.R P.lo P.c P.b H H) :
    ∀ r ∈ Icc 0 P.R, r ≤ P.R-7/10000 → P.m ≤ H r := by
  have hV : ∀ r ∈ Ioo 0 P.R, radialAmplitudePotential P.c P.b H r ∈ Icc (3/10 : ℝ) (1/2) := by
    intro r hr
    exact radialAmplitudePotential_bounds P.c P.b P.R P.hc P.hb P.hR2 H hH.1.continuous
      (fun t ht => ⟨P.lo_lower.trans (hH.2.2.2.2.1 t ht).1.1,(hH.2.2.2.2.1 t ht).1.2⟩)
      r ⟨hr.1.le,hr.2.le⟩
  exact radial_scalar_core_lower P.p (by have := P.hp; omega) P.R P.m P.lo
    P.hR P.hR2 P.hm P.hm1 P.hmp P.hlo H (radialAmplitudePotential P.c P.b H)
    hH.1 hH.2.1 hH.2.2.2.1.deriv hH.2.2.1
    (fun r hr => by have h := (hH.2.2.2.2.1 r hr).1.1; linarith [P.lo_lower]) hV hH.2.2.2.2.2

theorem RadialInnerData.coreLevel_eq (P : RadialInnerData) :
    P.m=(1/5 : ℝ)^((P.p-1 : ℕ) : ℝ)⁻¹ := by
  rw [← P.hmp]
  exact (Real.pow_rpow_inv_natCast (by linarith [P.hm]) (by have := P.hp; omega)).symm

theorem radial_core_level_tendsto (P : ℕ → RadialInnerData)
    (hp : Tendsto (fun n => (P n).p) atTop atTop) :
    Tendsto (fun n => (P n).m) atTop (𝓝 1) := by
  have hN : Tendsto (fun n => (P n).p-1) atTop atTop := (tendsto_sub_atTop_nat 1).comp hp
  have hR : Tendsto (fun n => (((P n).p-1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hN
  have h := (Real.continuous_const_rpow (by norm_num : (1/5 : ℝ) ≠ 0)).tendsto 0 |>.comp
    (tendsto_inv_atTop_zero.comp hR)
  change Tendsto (fun n => (1/5 : ℝ)^(((P n).p-1 : ℕ) : ℝ)⁻¹) atTop
    (𝓝 ((1/5 : ℝ)^(0 : ℝ))) at h
  simpa only [← RadialInnerData.coreLevel_eq,Real.rpow_zero] using h

theorem radial_inner_limit_plateau (R : ℝ) (P : ℕ → RadialInnerData)
    (hR : ∀ n, (P n).R=R) (H : ℕ → ℝ → ℝ)
    (hH : ∀ n, RadialInnerOutputSpec (P n).p R (P n).lo (P n).c (P n).b (H n) (H n))
    (hp : Tendsto (fun n => (P n).p) atTop atTop) (A : ℝ → ℝ)
    (hT : ∀ r ∈ Icc 0 R, Tendsto (fun n => H n r) atTop (𝓝 (A r))) :
    EqOn A (fun _ => 1) (Icc 0 (R-7/10000)) := by
  intro r hr
  have hrR : r ∈ Icc 0 R := ⟨hr.1,by linarith [hr.2]⟩
  have hlo : ∀ n, (P n).m ≤ H n r := by
    intro n
    have hs : RadialInnerOutputSpec (P n).p (P n).R (P n).lo (P n).c (P n).b (H n) (H n) := by
      simpa only [hR n] using hH n
    apply radial_inner_core_lower (P n) (H n) hs
    · simpa only [hR n] using hrR
    · simpa only [hR n] using hr.2
  have hhi : ∀ n, H n r ≤ 1 := fun n => ((hH n).2.2.2.2.1 r hrR).1.2
  have ht : Tendsto (fun n => H n r) atTop (𝓝 1) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le (radial_core_level_tendsto P hp)
      tendsto_const_nhds hlo hhi
  exact tendsto_nhds_unique (hT r hrR) ht

end DefocusingNLS

end OAI
