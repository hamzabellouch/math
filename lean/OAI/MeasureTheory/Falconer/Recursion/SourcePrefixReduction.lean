import OAI.MeasureTheory.Falconer.Recursion.PrefixBandAssembly
import OAI.MeasureTheory.Falconer.Angular.AngularUniformAbsorption

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff

theorem prefix_band_power_absorption {R eps E T C F D H : ℝ}
    (hR : 1 ≤ R) (heps : 0 < eps) (hC : C ≤ R^(eps/2))
    (hF : 0 ≤ F) (hD : 0 ≤ D) (hH : 0 ≤ H) :
    C*(F+D+R^(E+eps/2)*H+R^(-T)) ≤
      R^eps*(F+D+R^E*H+R^(-T)) := by
  have hRp : 0 < R := by linarith
  have hhalf : 1 ≤ R^(eps/2) := Real.one_le_rpow hR (by positivity)
  have he : R^eps = R^(eps/2)*R^(eps/2) := by
    rw [← Real.rpow_add hRp]
    congr 1
    ring
  apply (mul_le_mul_of_nonneg_right hC (by positivity)).trans
  rw [Real.rpow_add hRp,he]
  nlinarith [mul_nonneg (show 0 ≤ R^(eps/2)-1 by linarith)
    (show 0 ≤ R^(eps/2)*(F+D+R^(-T)) by positivity)]

theorem source_positive_distance_prefix {lam sig kap eps T : ℝ}
    (hlam : 0 ≤ lam) (hsig : 0 < sig) (hkap : 0 < kap)
    (hgap : sig < kap/1000) (heps : 0 < eps) (hT : 0 < T)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ K N₀ : ℕ, ∀ d : PositiveDistanceData,
    d.lam = lam → d.sig = sig → d.q = sourcePolicyBlock d.N kap →
    d.J = sourceSmoothingLevels sig kap → N₀ ≤ d.N → d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 →
    d.X.length = d.a → d.Y.length = d.a →
    100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center →
    dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ)) →
    ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    d.a+100*d.q < d.t → d.t ≤ d.N → d.i+1 ≤ d.J →
    let A := fun m : ℕ => d.mass m-(m:ℝ)/d.N
    let p := policyDepth A d.N d.q d.a d.t
    2*p ≤ d.a+d.t →
    d.coincidence.toReal ≤ ((2:ℝ)^d.N)^eps *
      (((2:ℝ)^d.N)^(12*lam)+d.prefixLowMaximum+
      ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)) *
        d.prefixSuccessorSupremum K p Ψ + ((2:ℝ)^d.N)^(-T)) := by
  obtain ⟨C,hC,K,N₁,h₁⟩ := PositiveDistanceData.uniform_prefix_band hsig
    (by linarith : 10*sig < kap) hlam hT.le (half_pos heps)
    (sourceSmoothingLevels_pos hsig hkap) hΨ hpos hs hone
  obtain ⟨N₂,h₂⟩ := fixed_linear_subpower C hC.le (half_pos heps)
  refine ⟨K,max N₁ N₂,?_⟩
  intro d hdLam hdSig hdq hdJ hN hQ hcarry hX hY hlo hsep B δ hprof hw ht hi A p hpref
  have hq : 0 < d.q := by
    rw [hdq]
    exact sourcePolicyBlock_pos (by omega : 0 < d.N) hkap
  have hblock : kap*d.N ≤ (d.q:ℝ) := by rw [hdq]; exact source_policy_block_lower _ _
  have hband := h₁ d hdSig hdLam hdJ ((le_max_left _ _).trans hN) hQ hcarry B δ hprof
    hq hblock hw ht (by omega) hX hY hlo hsep hpref
  let := hprof.probability
  obtain ⟨W,hW,hWb⟩ := continuous_supported_bump_bound hΨ.continuous hs
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hsup0 := (d.prefixSuccessorSupremum_majorizes (by rw [hQ]; norm_num) K p Ψ hW
    (fun x => (le_abs_self _).trans (hWb x)) hsupport).1
  exact hband.trans (prefix_band_power_absorption (one_le_pow₀ (by norm_num)) heps
    (h₂ d.N ((le_max_right _ _).trans hN)) (by positivity) d.prefixLowMaximum_nonneg hsup0)

end PlanarFalconer

end OAI
