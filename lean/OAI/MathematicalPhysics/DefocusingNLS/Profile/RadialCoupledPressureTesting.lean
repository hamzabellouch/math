import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureLocalTesting
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialPressureStepConvergence

namespace OAI

/-! C1 test convergence of the actual nonlinear inner pressure. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_coupled_pressure_test_convergence (R l b : ℝ)
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
    (hloT : Tendsto (fun n => (P n).lo) atTop (𝓝 ‖F R‖))
    (φ φ₁ : ℝ → ℝ) (hφ : Continuous φ) (hφ₁ : Continuous φ₁)
    (hφD : ∀ r ∈ Ioo 0 R, HasDerivAt φ (φ₁ r) r) :
    Tendsto (fun n => ∫ t in (0 : ℝ)..R, (H n t)^((P n).p-1)*φ t*t^11) atTop
      (𝓝 (b*∫ t in (0 : ℝ)..l, φ t*t^11)) := by
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
  have hT := radial_coupled_pressure_step_primitive R l b hRlow hRu hl hlR hlwidth hb
    F G hFc hGc hFI hGI hB P hR H hH hp hcT hbT hloT
  apply radial_pressure_local_test_convergence R l b (by linarith) hlR.le
    (fun n => (P n).p) (fun n => by have hn := (P n).hp; omega) H
    (fun n => (hH n).1.continuous) _ _ A D hA hD _ hAD hcore hTA hT φ φ₁ hφ hφ₁ hφD
  · intro n r hr
    exact (le_of_lt (show (0 : ℝ) < (999/1000 : ℝ) by norm_num)).trans
      ((P n).lo_lower.trans ((hH n).2.2.2.2.1 r hr).1.1)
  · intro n r hr
    exact ((hH n).2.2.2.2.1 r hr).2.trans (by norm_num)
  · intro r hr
    exact ne_of_gt (lt_of_lt_of_le (by norm_num) (hAI r hr).1)

end DefocusingNLS

end OAI
