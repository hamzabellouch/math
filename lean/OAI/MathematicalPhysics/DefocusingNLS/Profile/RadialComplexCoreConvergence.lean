import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialComplexBoundaryConvergence

namespace OAI

/-! The actual inner profiles converge in C1 to one on the core and the free IVP on the tail. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_coupled_complex_C1_convergence (R l b : ℝ)
    (hRlow : (3+7/10000 : ℝ) ≤ R) (hRu : R ≤ (10/3 : ℝ))
    (hl : (3 : ℝ) ≤ l) (hlR : l < R) (hlwidth : R-l ≤ (1/1000 : ℝ))
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (F G : ℝ → ℂ) (hFc : Continuous F) (hGc : Continuous G)
    (hFI : ∀ r ∈ Icc l R, F r=1+∫ t in l..r, G t)
    (hGI : ∀ r ∈ Icc l R, G r=∫ t in l..r,
      -radialFreeCoefficient t*G t-(b : ℂ)*F t)
    (hB : ∀ r ∈ Icc l R, ‖F r‖ ≤ 2 ∧ ‖G r‖ ≤ 2)
    (P : ℕ → RadialInnerData) (hR : ∀ n, (P n).R=R) (H : ℕ → ℝ → ℝ)
    (hH : ∀ n, RadialInnerOutputSpec (P n).p R (P n).lo (P n).c (P n).b (H n) (H n))
    (hp : Tendsto (fun n => (P n).p) atTop atTop)
    (hcT : Tendsto (fun n => (P n).c) atTop (𝓝 6))
    (hbT : Tendsto (fun n => (P n).b) atTop (𝓝 b))
    (hloT : Tendsto (fun n => (P n).lo) atTop (𝓝 ‖F R‖)) :
    TendstoUniformlyOn
      (fun n => radialPolar (H n) (radialPhase (P n).c (radialClampedAmplitude R (H n))))
      (fun r => if r ≤ l then 1 else F r) atTop (Icc 0 R) ∧
    TendstoUniformlyOn
      (fun n => deriv (radialPolar (H n) (radialPhase (P n).c (radialClampedAmplitude R (H n)))))
      (fun r => if r ≤ l then 0 else G r) atTop (Icc 0 R) := by
  have hsub := radial_free_modulus_lt_one b l R hb hl hRu hlR.le hlwidth F G hFc hGc hFI hGI hB
  obtain ⟨A,D,hA,hD,hTA,hTD,hcore,hDl,htail⟩ := radial_coupled_C1_core_convergence R l b hRlow hRu
    hl hlR.le hlwidth hb F G hFc hGc hFI hGI hB (hsub R ⟨hlR,le_rfl⟩) P hR H hH hp hcT hbT hloT
  have hAI : ∀ r ∈ Icc 0 R, A r ∈ Icc (999/1000 : ℝ) 1 := by
    intro r hr
    exact ⟨ge_of_tendsto' (hTA.tendsto_at hr) (fun n =>
      (P n).lo_lower.trans ((hH n).2.2.2.2.1 r hr).1.1),
      le_of_tendsto' (hTA.tendsto_at hr) (fun n => ((hH n).2.2.2.2.1 r hr).1.2)⟩
  have hAD : ∀ r ∈ Ioo 0 R, HasDerivAt A (D r) r := by
    intro r hr
    exact hasDerivAt_of_tendstoUniformlyOn isOpen_Ioo (hTD.mono Ioo_subset_Icc_self)
      (Eventually.of_forall (fun n t _ => ((hH n).1 t).hasDerivAt))
      (fun t ht => hTA.tendsto_at ⟨ht.1.le,ht.2.le⟩) hr
  have hfree := radial_inner_limit_free_equation R P hR H hH hp 6 b (by norm_num) hcT hbT
    A D hA hD hAI hTA hTD
  have hDE : ∀ r ∈ Ioo l R, HasDerivAt D (-11/r*D r-radialAmplitudePotential 6 b A r*A r) r := by
    intro r hr
    apply (hfree r ⟨by linarith [hr.1],hr.2⟩ _).2
    rw [htail ⟨hr.1.le,hr.2.le⟩]
    exact hsub r ⟨hr.1,hr.2.le⟩
  have hid := radial_core_polar_identification R l b hl hlR hRu hlwidth hb A D hA hD
    (fun r hr => lt_of_lt_of_le (by norm_num) (hAI r hr).1) hcore hDl
    (fun r hr => hAD r ⟨by linarith [hr.1],hr.2⟩) hDE F G hFc hGc hFI hGI
  have hconv := radial_reconstruction_C1_convergence R (by linarith)
    (fun n => (P n).c) 6 (fun n => (P n).hc) hcT H A D (fun n => (hH n).1) hA hD
    (fun n r hr => ⟨(P n).lo_lower.trans ((hH n).2.2.2.2.1 r hr).1.1,
      ((hH n).2.2.2.2.1 r hr).1.2⟩) hTA hTD
  have hDzero := radial_plateau_derivative_zero l (by linarith) A D hD hcore
    (fun r hr => hAD r ⟨hr.1,hr.2.trans hlR⟩)
  constructor
  · apply hconv.1.congr_right
    intro r hr
    dsimp only
    by_cases hrl : r ≤ l
    · have hr' : r ∈ Icc 0 l := ⟨hr.1,hrl⟩
      simp only [hrl,ite_true]
      dsimp [radialPolar]
      rw [hcore hr',radial_phase_zero_on_plateau R l (by linarith) hlR.le A hcore r hr']
      simp
    · simp only [hrl,ite_false]
      exact hid.1 ⟨(not_le.mp hrl).le,hr.2⟩
  · apply hconv.2.congr_right
    intro r hr
    dsimp only
    by_cases hrl : r ≤ l
    · have hr' : r ∈ Icc 0 l := ⟨hr.1,hrl⟩
      simp only [hrl,ite_true]
      dsimp [radialPolarSlope,radialPhaseSpeed]
      rw [hDzero hr',radial_velocity_on_plateau l A hcore r hr']
      simp
    · simp only [hrl,ite_false]
      exact hid.2 ⟨(not_le.mp hrl).le,hr.2⟩

end DefocusingNLS

end OAI
