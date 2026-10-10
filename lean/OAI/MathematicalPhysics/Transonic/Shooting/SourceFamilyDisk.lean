import OAI.MathematicalPhysics.Transonic.Shooting.FuchsianFamily
import OAI.MathematicalPhysics.Transonic.Shooting.SourceFamilyC1

namespace OAI

section
noncomputable section

namespace SepticProfile.SourceFamily
open Set Filter Metric Fuchsian
open scoped Topology

/-- The nonresonant sonic remainder is constructed continuously on the entire
closed shooting chart, with one positive complex radius. -/
theorem exists_continuous_remainder_disk (J : FamilyJet) :
    ∃ r : ℝ, 0<r ∧ ∃ f : Parameter → analyticDisk, Continuous f ∧
      (∀ a, f a ∈ realDisk) ∧
      (∀ a, extend (f a : DiskMap) 0=0) ∧
      ∀ a z, z ∈ ball (0:ℂ) 1 →
        denominator J a ((r:ℂ)*z,extend (f a:DiskMap) z) ≠ 0 ∧
        z*deriv (extend (f a:DiskMap)) z+((76-rho a:ℝ):ℂ)*extend (f a:DiskMap) z=
          (r:ℂ)*z*H J a ((r:ℂ)*z,extend (f a:DiskMap) z) := by
  obtain ⟨R,hR,K,M,hM,hden,hdiff,hK,hcont,hM0⟩ := uniform_bounds J
  let B : ℝ := M+(K:ℝ)*R
  have hB : 0≤B := by dsimp [B];positivity
  let r : ℝ := min (R/(B+1)) (min R (1/(2*((K:ℝ)+1))))
  have hr : 0<r := by dsimp [r];positivity
  have hrR : r≤R := (min_le_right _ _).trans (min_le_left _ _)
  have hrB' : r*(B+1)≤R :=
    (le_div_iff₀ (by linarith : 0<B+1)).mp (min_le_left _ _)
  have hrB : r*B≤R := by nlinarith
  have hrK' : r*(2*((K:ℝ)+1))≤1 :=
    (le_div_iff₀ (by positivity : 0<2*((K:ℝ)+1))).mp
      ((min_le_right _ _).trans (min_le_right _ _))
  have hrK : r*(K:ℝ)≤1/2 := by nlinarith
  let Hd : Parameter → analyticDisk → analyticDisk := fun a =>
    nonlinearDisk hr.le hrR (H J a) (hdiff a)
  have hc : Continuous (fun a => 76-rho a) := continuous_const.sub rho.continuous
  have hc1 (a : Parameter) : 1≤76-rho a := le_of_lt (lt_trans (by norm_num) (indicial_shift a))
  have hbound (a : Parameter) (f : analyticDisk) (hf : ‖f‖≤R) : ‖Hd a f‖≤B := by
    exact (norm_nonlinearDisk_le hr.le hrR hR.le (H J a) (hdiff a) (hK a) f hf).trans
      (by dsimp [B];linarith [hM0 a])
  have hreal (a : Parameter) (v : ℂ × ℂ) (hx : v.1.im=0) (hy : v.2.im=0) :
      (H J a v).im=0 := by
    rw [H_sourceH]
    exact SourceSonic.sourceH_real _ _ _ _ _ _ _ _ _ _ hx hy
  obtain ⟨f,hfc,hfb,hf0,hode⟩ := exists_continuous_fuchsian_disk (fun a => 76-rho a) hc hc1
    hr.le hR.le hrB hrK Hd hbound
    (fun a f g hf hg => nonlinearDisk_lip hr.le hrR (H J a) (hdiff a) (hK a) f g hf hg)
    (fun f hf => continuous_nonlinearDisk_family hr.le hrR (H J) hdiff hcont f hf)
    realDisk realDisk_closed realDisk_zero (by
      intro a f hf hfR
      apply realDisk_real_smul _ r
      apply realDisk_inverse _ (le_trans (by norm_num) (hc1 a))
      intro z hz
      change ((nonlinearDisk hr.le hrR (H J a) (hdiff a) f : DiskMap) z).im=0
      rw [nonlinearDisk_apply hr.le hrR (H J a) (hdiff a) f hfR]
      exact hreal a _ (by simp [hz]) (hf z hz))
  refine ⟨r,hr,f,hfc,fun a => (hfb a).1,hf0,?_⟩
  intro a z hz
  refine ⟨?_,?_⟩
  · apply hden
    have hi := inputBound hr.le hrR (f a) (hfb a).2 ⟨z,ball_subset_closedBall hz⟩
    change ((r:ℂ)*z,extend (f a:DiskMap) (↑(⟨z,ball_subset_closedBall hz⟩:Disk))) ∈ _
    rw [extend_coe]
    exact hi
  have he : extend (Hd a (f a):DiskMap) z=H J a ((r:ℂ)*z,extend (f a:DiskMap) z) := by
    have he := nonlinearDisk_apply hr.le hrR (H J a) (hdiff a) (f a) (hfb a).2
      ⟨z,ball_subset_closedBall hz⟩
    rw [← extend_coe,← extend_coe] at he
    exact he
  rw [← he]
  exact hode a z hz

end SepticProfile.SourceFamily

end
end

end OAI
