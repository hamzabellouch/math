import Mathlib
import OAI.Analysis.Crouzeix.HomologicalCauchy
import OAI.Analysis.Crouzeix.Riemann

namespace OAI

/-! Univalent. -/

noncomputable section

open Set Filter Metric Topology Function

namespace CrouzeixHilbert.Conformal

theorem deriv_ne_zero_of_injOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hi : InjOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
  obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp hU a ha
  let r := R / 3
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : 2 * r < R := by dsimp [r]; linarith
  have hK : closedBall a (2 * r) ⊆ U := (closedBall_subset_ball hrR).trans hsub
  have hball : ball a r ⊆ U := (ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))).trans hK
  let δ : ℕ → ℝ := fun n => r / (n + 1)
  have hδ : ∀ n, 0 < δ n := fun n => div_pos hr (by positivity)
  have hδle : ∀ n, δ n ≤ r := fun n => div_le_self hr.le (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
  have hδ0 : Tendsto δ atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
        Tendsto (fun n : ℕ => r * (1 / ((n : ℝ) + 1))) atTop (𝓝 (r * 0)))
  have hshift : ∀ n z, z ∈ ball a r → z + (δ n : ℂ) ∈ closedBall a (2 * r) := by
    intro n z hz
    have hd : dist (z + (δ n : ℂ)) a ≤ dist z a + δ n := by
      calc
        _ = ‖z - a + (δ n : ℂ)‖ := by rw [dist_eq_norm]; congr 1; ring
        _ ≤ ‖z - a‖ + ‖(δ n : ℂ)‖ := norm_add_le _ _
        _ = dist z a + δ n := by rw [← dist_eq_norm, Complex.norm_real, Real.norm_of_nonneg (hδ n).le]
    exact hd.trans (by have := hδle n; have := mem_ball.mp hz; linarith)
  have hzK : ∀ z ∈ ball a r, z ∈ closedBall a (2 * r) := fun z hz =>
    (mem_closedBall.mpr <| (mem_ball.mp hz).le.trans (by linarith))
  let F : ℕ → ℂ → ℂ := fun n z => (f (z + (δ n : ℂ)) - f z) / (δ n : ℂ)
  have hFd : ∀ n, DifferentiableOn ℂ (F n) (ball a r) := by
    intro n z hz
    have hd₁ : DifferentiableAt ℂ (fun v => f (v + (δ n : ℂ))) z :=
      ((hf _ (hK (hshift n z hz))).differentiableAt
        (hU.mem_nhds (hK (hshift n z hz)))).comp z (differentiableAt_id.add_const _)
    have hd₂ := (hf z (hball hz)).differentiableAt (hU.mem_nhds (hball hz))
    exact ((hd₁.sub hd₂).div_const _).differentiableWithinAt
  have hFn : ∀ n z, z ∈ ball a r → F n z ≠ 0 := by
    intro n z hz he
    have hen : f (z + (δ n : ℂ)) = f z := sub_eq_zero.mp
      ((div_eq_zero_iff).mp he |>.resolve_right (by exact_mod_cast (hδ n).ne'))
    have hinj := hi (hK (hshift n z hz)) (hball hz) hen
    have hzero : (δ n : ℂ) = 0 := add_left_cancel (hinj.trans (add_zero z).symm)
    exact (hδ n).ne' (Complex.ofReal_eq_zero.mp hzero)
  have hFeq : ∀ n z, F n z = dslope f z (z + (δ n : ℂ)) := by
    intro n z
    have hn : z + (δ n : ℂ) ≠ z := by
      simpa using (show (δ n : ℂ) ≠ 0 by exact_mod_cast (hδ n).ne')
    rw [dslope_of_ne f hn]
    simp only [slope, add_sub_cancel_left, smul_eq_mul, div_eq_mul_inv, vsub_eq_sub, F]
    ring
  have huc := ((isCompact_closedBall a (2 * r)).prod (isCompact_closedBall a (2 * r)))
      |>.uniformContinuousOn_of_continuous
      ((continuousOn_dslope_pair hU hf).mono (prod_mono hK hK))
  have hlim : TendstoUniformlyOn F (deriv f) atTop (ball a r) := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨η, hη, hmod⟩ := Metric.uniformContinuousOn_iff.mp huc ε hε
    filter_upwards [hδ0.eventually (gt_mem_nhds hη)] with n hn
    intro z hz
    have hp : dist (z, z) (z, z + (δ n : ℂ)) < η := by
      rw [dist_prod_same_left, dist_self_add_right, Complex.norm_real, Real.norm_of_nonneg (hδ n).le]
      exact hn
    simpa only [dslope_same, ← hFeq] using
      hmod (z,z) ⟨hzK z hz, hzK z hz⟩ (z, z + (δ n : ℂ)) ⟨hzK z hz, hshift n z hz⟩ hp
  rcases zero_or_ne_of_tendstoLocallyUniformlyOn isOpen_ball (convex_ball a r).isPreconnected
      hlim.tendstoLocallyUniformlyOn hFd hFn with he | hn
  · have hc : ∀ z ∈ ball a r, fderivWithin ℂ f (ball a r) z = 0 := by
      intro z hz
      rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hz)
        ((hf z (hball hz)).differentiableAt (hU.mem_nhds (hball hz)))]
      apply ContinuousLinearMap.ext
      intro v
      simp only [fderiv_eq_smul_deriv, he hz, Pi.zero_apply, smul_zero,
        zero_apply]
    have hb : a + (r / 2 : ℝ) ∈ ball a r := by
      rw [mem_ball, dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
      linarith
    have heq := (convex_ball a r).is_const_of_fderivWithin_eq_zero (hf.mono hball) hc
      (mem_ball_self hr) hb
    have hbad := hi ha (hball hb) heq
    have hz : ((r / 2 : ℝ) : ℂ) = 0 := by linear_combination -hbad
    have : r / 2 = 0 := Complex.ofReal_eq_zero.mp hz
    linarith
  · exact hn a (mem_ball_self hr)

theorem hasStrictDerivAt_invFunOn {U V : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f U) (hbij : BijOn f U V) {w : ℂ} (hw : w ∈ V) :
    HasStrictDerivAt (invFunOn f U) (deriv f (invFunOn f U w))⁻¹ w := by
  obtain ⟨z, hz, rfl⟩ := hbij.surjOn hw
  have hinv := hbij.invOn_invFunOn
  have he : ∀ᶠ v in 𝓝 z, invFunOn f U (f v) = v := by
    filter_upwards [hU.mem_nhds hz] with v hv
    exact hinv.1 hv
  rw [hinv.1 hz]
  exact ((hf.analyticOnNhd hU z hz).hasStrictDerivAt).to_local_left_inverse
    (deriv_ne_zero_of_injOn hU hf hbij.injOn hz) he

theorem riemann_biholomorphic_bounded {U : Set ℂ} (hU : IsOpen U)
    (hb : Bornology.IsBounded U) (hc : IsSimplyConnected U) {a : ℂ} (ha : a ∈ U) :
    ∃ f g : ℂ → ℂ,
      DifferentiableOn ℂ f U ∧ DifferentiableOn ℂ g (ball 0 1) ∧
      BijOn f U (ball 0 1) ∧ BijOn g (ball 0 1) U ∧
      InvOn g f U (ball 0 1) ∧ f a = 0 ∧
      (∀ z ∈ U, deriv f z ≠ 0) ∧ (∀ w ∈ ball 0 1, deriv g w ≠ 0) := by
  obtain ⟨f, hf, _, hbij⟩ := riemann_mapping_bounded hU hb hc ha
  let g := invFunOn f U
  have hd : DifferentiableOn ℂ g (ball 0 1) := fun w hw =>
    (hasStrictDerivAt_invFunOn hU hf.holomorphic hbij hw).hasDerivAt.differentiableAt.differentiableWithinAt
  have hinv : InvOn g f U (ball 0 1) := hbij.invOn_invFunOn
  have hg : BijOn g (ball 0 1) U := hbij.symm hinv.symm
  exact ⟨f, g, hf.holomorphic, hd, hbij, hg, hinv, hf.normalized,
    fun z hz => deriv_ne_zero_of_injOn hU hf.holomorphic hf.injective hz,
    fun w hw => deriv_ne_zero_of_injOn isOpen_ball hd hg.injOn hw⟩

end CrouzeixHilbert.Conformal

end

end OAI
