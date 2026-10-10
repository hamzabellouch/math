import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialInnerCompactness
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

namespace OAI

/-! Genuine coupled inner profiles have C¹ convergent subsequences on the fixed inner ball. -/

open Set Filter Topology
namespace DefocusingNLS

theorem radial_coupled_C1_subsequence (R : ℝ) (P : ℕ → RadialInnerData)
    (hR : ∀ n, (P n).R=R) (H : ℕ → ℝ → ℝ)
    (hH : ∀ n, RadialInnerOutputSpec (P n).p R (P n).lo (P n).c (P n).b (H n) (H n)) :
    ∃ A D : ℝ → ℝ, Continuous A ∧ Continuous D ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformlyOn (fun n => H (φ n)) A atTop (Icc 0 R) ∧
      TendstoUniformlyOn (fun n => deriv (H (φ n))) D atTop (Icc 0 R) ∧
      (∀ r ∈ Ioo 0 R, HasDerivAt A (D r) r) ∧ D 0=0 := by
  have hSpec : ∀ n, RadialInnerOutputSpec (P n).p (P n).R (P n).lo (P n).c (P n).b (H n) (H n) := by
    intro n
    simpa only [hR n] using hH n
  have hR1 : 1 ≤ R := by simpa only [hR 0] using (P 0).hR
  have hR2 : R^2 ≤ 11 := by simpa only [hR 0] using (P 0).hR2
  have hDC : ∀ n, ContinuousOn (deriv (H n)) (Icc 0 R) := by
    intro n
    simpa only [hR n] using (radial_inner_integral_and_continuity (P n) (H n) (hSpec n)).2
  have hB : ∀ n r, r ∈ Icc 0 R → ‖H n r‖ ≤ 1 ∧ ‖deriv (H n) r‖ ≤ r/24 := by
    intro n r hr
    have hrP : r ∈ Icc 0 (P n).R := by simpa only [hR n] using hr
    have hb := ((hH n).2.2.2.2.1 r hr).1
    have hn : 0 ≤ H n r := by linarith [hb.1,(P n).lo_lower]
    exact ⟨by simpa only [Real.norm_eq_abs,abs_of_nonneg hn] using hb.2,
      (radial_inner_derivative_bounds (P n) (H n) (hSpec n)).1 r hrP⟩
  have hL : ∀ n, LipschitzOnWith 1 (deriv (H n)) (Icc 0 R) := by
    intro n
    simpa only [hR n] using radial_inner_derivative_lipschitz (P n) (H n) (hSpec n)
  obtain ⟨J,φ,hφ,hT⟩ := radial_inner_jet_subsequence R hR1 hR2 H (fun n => (hH n).1) hDC hB hL
  let cR : ℝ → Icc (0 : ℝ) R := fun r => ⟨radialClamp R r,radialClamp_mem R r (by linarith)⟩
  have hcR : Continuous cR := (continuous_radialClamp R).subtype_mk _
  let A : ℝ → ℝ := fun r => (J (cR r)).1
  let D : ℝ → ℝ := fun r => (J (cR r)).2
  have hTA : TendstoUniformlyOn (fun n => H (φ n)) A atTop (Icc 0 R) := by
    have h := (uniformContinuous_fst.comp_tendstoUniformly (hT.comp cR)).tendstoUniformlyOn (s := Icc 0 R)
    apply h.congr
    filter_upwards [] with n r hr
    change H (φ n) (radialClamp R r)=H (φ n) r
    rw [radialClamp_eq R r hr]
  have hTD : TendstoUniformlyOn (fun n => deriv (H (φ n))) D atTop (Icc 0 R) := by
    have h := (uniformContinuous_snd.comp_tendstoUniformly (hT.comp cR)).tendstoUniformlyOn (s := Icc 0 R)
    apply h.congr
    filter_upwards [] with n r hr
    change deriv (H (φ n)) (radialClamp R r)=deriv (H (φ n)) r
    rw [radialClamp_eq R r hr]
  refine ⟨A,D,(J.continuous.comp hcR).fst,(J.continuous.comp hcR).snd,φ,hφ,hTA,hTD,?_,?_⟩
  · intro r hr
    exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hTD.mono Ioo_subset_Icc_self)
      (Eventually.of_forall (fun n r _ => ((hH (φ n)).1 r).hasDerivAt))
      (fun r hr => hTA.tendsto_at ⟨hr.1.le,hr.2.le⟩) hr
  · have h := hTD.tendsto_at (show (0 : ℝ) ∈ Icc 0 R from ⟨le_rfl,by linarith⟩)
    have hz : (fun n => deriv (H (φ n)) 0)=(fun _ : ℕ => (0 : ℝ)) := by
      funext n
      exact (hH (φ n)).2.2.2.1.deriv
    rw [hz] at h
    exact (tendsto_nhds_unique h tendsto_const_nhds)

end DefocusingNLS

end OAI
