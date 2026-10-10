import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoreShape
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialCoreRadius
import OAI.MathematicalPhysics.DefocusingNLS.Profile.RadialFreeUniqueness

namespace OAI

/-! The actual large-power inner profiles converge along subsequences to the prescribed free tail. -/

open Set Filter Topology MeasureTheory
namespace DefocusingNLS

theorem radial_coupled_identified_subsequence (R l b : ℝ)
    (hRlow : (3+7/10000 : ℝ) ≤ R) (hRu : R ≤ (10/3 : ℝ))
    (hl : (3 : ℝ) ≤ l) (hlR : l ≤ R) (hlwidth : R-l ≤ (1/1000 : ℝ))
    (hb : b ∈ Icc (334/1000 : ℝ) (335/1000))
    (F G : ℝ → ℂ) (hFc : Continuous F) (hGc : Continuous G)
    (hFI : ∀ r ∈ Icc l R, F r=1+∫ t in l..r, G t)
    (hGI : ∀ r ∈ Icc l R, G r=∫ t in l..r,
      -radialFreeCoefficient t*G t-(b : ℂ)*F t)
    (hB : ∀ r ∈ Icc l R, ‖F r‖ ≤ 2 ∧ ‖G r‖ ≤ 2) (hmod1 : ‖F R‖ < 1)
    (P : ℕ → RadialInnerData) (hR : ∀ n, (P n).R=R) (H : ℕ → ℝ → ℝ)
    (hH : ∀ n, RadialInnerOutputSpec (P n).p R (P n).lo (P n).c (P n).b (H n) (H n))
    (hp : Tendsto (fun n => (P n).p) atTop atTop)
    (hcT : Tendsto (fun n => (P n).c) atTop (𝓝 6))
    (hbT : Tendsto (fun n => (P n).b) atTop (𝓝 b))
    (hloT : Tendsto (fun n => (P n).lo) atTop (𝓝 ‖F R‖)) :
    ∃ A D : ℝ → ℝ, Continuous A ∧ Continuous D ∧ ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformlyOn (fun n => H (φ n)) A atTop (Icc 0 R) ∧
      TendstoUniformlyOn (fun n => deriv (H (φ n))) D atTop (Icc 0 R) ∧
      EqOn A (fun _ => 1) (Icc 0 l) ∧ D l=0 ∧
      EqOn A (fun r => ‖F r‖) (Icc l R) := by
  obtain ⟨A,D,hA,hD,φ,hφ,hTA,hTD,hAR,ρ,hρ,hcore,hDρ,hsub,hanti,hfree⟩ :=
    radial_coupled_core_shape R P hR H hH hp 6 b ‖F R‖ (by norm_num) hb hcT hbT hloT hmod1
  have hρ0 : (3 : ℝ) ≤ ρ := by linarith [hρ.1]
  have hρwidth : R-ρ ≤ (1/1000 : ℝ) := by linarith [hρ.1]
  have hAP : ∀ r ∈ Icc 0 R, 0 < A r := by
    intro r hr
    have hlow : (999/1000 : ℝ) ≤ A r := ge_of_tendsto' (hTA.tendsto_at hr) (fun n =>
      (P (φ n)).lo_lower.trans ((hH (φ n)).2.2.2.2.1 r hr).1.1)
    linarith
  have heq : ρ=l := radial_core_radius_identification R ρ l b hρ0 hl hρ.2 hlR hRu hρwidth
    hlwidth hb A D hA hD hAP hcore hDρ (fun r hr => (hfree r hr).1)
    (fun r hr => (hfree r hr).2) F G hFc hGc hFI hGI hB hAR
  subst ρ
  obtain ⟨F₀,G₀,hF₀c,hG₀c,hF₀I,hG₀I,_,hF₀norm⟩ := radial_core_free_integral R l b hρ0 hρ.2
    hRu hρwidth hb A D hA hD hAP hcore hDρ
    (fun r hr => (hfree r hr).1) (fun r hr => (hfree r hr).2)
  have hX₀ := radial_free_components_state b l R (by linarith) F₀ G₀ hF₀c hG₀c 1 0
    hF₀I (by simpa only [zero_add] using hG₀I)
  have hX := radial_free_components_state b l R (by linarith) F G hFc hGc 1 0
    hFI (by simpa only [zero_add] using hGI)
  have huniq := radial_free_integral_unique b l R hb hl hRu hlR hlwidth
    (fun r => (F₀ r,G₀ r)) (fun r => (F r,G r)) (hF₀c.prodMk hG₀c) (hFc.prodMk hGc) hX₀ hX
  refine ⟨A,D,hA,hD,φ,hφ,hTA,hTD,hcore,hDρ,?_⟩
  intro r hr
  have hpoint : F₀ r=F r := congrArg Prod.fst (huniq hr)
  exact (hF₀norm r hr).symm.trans (congrArg norm hpoint)

end DefocusingNLS

end OAI
