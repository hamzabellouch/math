import OAI.MeasureTheory.Falconer.Shells.PrefixHighShell
import OAI.MeasureTheory.Falconer.Recursion.PrefixLowMaximum
import OAI.MeasureTheory.Falconer.Fourier.FourierBandBound
import OAI.MeasureTheory.Falconer.Fourier.WeightedDistanceLowFrequency

namespace OAI

namespace PlanarFalconer
open Set MeasureTheory
open scoped ContDiff
namespace PositiveDistanceData

theorem uniform_prefix_band {sig kap lam T eps : ℝ}
    (hsig : 0 < sig) (hgap : 10*sig < kap) (hlam : 0 ≤ lam)
    (hT : 0 ≤ T) (heps : 0 < eps) {J : ℕ} (hJ : 0 < J)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ C : ℝ, 0 < C ∧ ∃ K N₀ : ℕ, ∀ d : PositiveDistanceData,
    d.sig = sig → d.lam = lam → d.J = J → N₀ ≤ d.N → d.Q.side = 1 → d.ρ d.Q.carrierᶜ = 0 →
    ∀ B : ℕ, ∀ δ : ℝ, RegularizedProfileData d.Q d.ρ d.N B δ d.lam d.mass →
    0 < d.q → kap*d.N ≤ (d.q:ℝ) → d.a+100*d.q < d.t → d.t ≤ d.N → d.i < d.J →
    d.X.length = d.a → d.Y.length = d.a →
    100*(2:ℝ)^(-(d.a:ℝ)) ≤ dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center →
    dist (d.Q.descendant d.X).center (d.Q.descendant d.Y).center ≤ 2000*(2:ℝ)^(-(d.a:ℝ)) →
    let A := fun m : ℕ => d.mass m-(m:ℝ)/d.N
    let p := policyDepth A d.N d.q d.a d.t
    2*p ≤ d.a+d.t →
    d.coincidence.toReal ≤ C*(1+2*(d.N:ℝ)) *
      (((2:ℝ)^d.N)^(12*lam)+d.prefixLowMaximum+
      ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eps) *
        d.prefixSuccessorSupremum K p Ψ + ((2:ℝ)^d.N)^(-T)) := by
  classical
  obtain ⟨C₀,hC₀,hfourier⟩ := actual_weighted_distance_equation20
  obtain ⟨K,N₁,hhigh⟩ := uniform_prefix_high_shell hsig hgap hlam hT heps hJ hΨ hpos hs hone
  obtain ⟨N₂,hlow⟩ := uniform_actual_distance_low_band hsig hJ
  let c := 32*binKernelConstant.toReal
  have hc : 0 ≤ c := by dsimp [c]; positivity
  refine ⟨C₀*(2+c),by positivity,K,max N₁ N₂,?_⟩
  intro d hdSig hdLam hdJ hN hQ hcarry B δ hprof hq hblock hw ht hi hX hY hlo hsep A p hpref
  let := hprof.probability
  have hQpos : 0 < d.Q.side := by rw [hQ]; norm_num
  have hsep' := d.stronglySeparated_of_unit hQ hX hY hlo hsep
  let := d.weightedDistance_isFinite hQpos hsep'
  obtain ⟨W,hW,hWb⟩ := continuous_supported_bump_bound hΨ.continuous hs
  have hsupport : ∀ x, 4 < x → Ψ x = 0 := by
    intro x hx
    by_contra hn
    exact (not_lt_of_ge hx.le) (hs x hn).2
  have hsup0 := (d.prefixSuccessorSupremum_majorizes hQpos K p Ψ hW
    (fun x => (le_abs_self _).trans (hWb x)) hsupport).1
  let F := ((2:ℝ)^d.N)^(12*lam)
  let G := ((2:ℝ)^d.N)^(-2*(A p-A d.a)+height A d.a p+4000*(lam+sig)+eps)*d.prefixSuccessorSupremum K p Ψ
  let Z := ((2:ℝ)^d.N)^(-T)
  let S := F+d.prefixLowMaximum+G+Z
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hG : 0 ≤ G := mul_nonneg (by positivity) hsup0
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hD := d.prefixLowMaximum_nonneg
  have hS : 0 ≤ S := by dsimp [S]; positivity
  have hFS : F ≤ S := by dsimp [S]; linarith
  have hDS : d.prefixLowMaximum ≤ S := by dsimp [S]; linarith
  have hGS : G+Z ≤ S := by dsimp [S]; linarith
  have hseed := d.weightedDistance_low_frequency hprof hQpos hsep' (by omega) hX hY
  rw [hdLam] at hseed
  have hbase : (2:ℝ)^(-(d.a:ℝ))*(∫ r in Icc (-((2:ℝ)^d.a)) ((2:ℝ)^d.a),
      ‖charFun d.weightedDistance r‖^2) ≤ (2+c)*S :=
    hseed.trans (by change 2*F ≤ _; nlinarith [mul_nonneg hc hS])
  have hshell : ∀ v ∈ Finset.Ioc d.a d.t,
      (2:ℝ)^(-(d.a:ℝ))*(∫ r in Icc ((2:ℝ)^((v:ℝ)-1)) ((2:ℝ)^v),
        ‖charFun d.weightedDistance r‖^2) ≤ (2+c)*S := by
    intro v hv
    by_cases hvl : (v:ℝ) ≤ (d.t:ℝ)-d.sig*d.N
    · have hb := hlow d ((le_max_right _ _).trans hN) hdSig hdJ hQ hsep' hcarry hq ht v
        (Finset.mem_Ioc.mp hv).2
      have hm := (d.prefixLowMaximum_majorizes hv hvl).2
      have hsmall := mul_le_mul_of_nonneg_left (fourier_shell_le_band d.weightedDistance v)
        (by positivity : 0 ≤ (2:ℝ)^(-(d.a:ℝ)))
      exact (hsmall.trans hb).trans (by change c*_ ≤ _; nlinarith [mul_le_mul_of_nonneg_left hm hc,mul_le_mul_of_nonneg_left hDS hc])
    · have hb := hhigh d hdSig hdLam hdJ ((le_max_left _ _).trans hN) hQ B δ hprof hq hblock
        hw ht hi hX hY hlo hsep hpref v hv (by simpa only [hdSig] using lt_of_not_ge hvl)
      have hsmall := mul_le_mul_of_nonneg_left (fourier_shell_le_expanded d.weightedDistance v)
        (by positivity : 0 ≤ (2:ℝ)^(-(d.a:ℝ)))
      exact (hsmall.trans hb).trans (by change G+Z ≤ _; nlinarith [mul_nonneg hc hS])
  have hband := finite_fourier_band_bound d.weightedDistance (by omega : d.a ≤ d.t) ht
    (mul_nonneg (by positivity) hS) hbase hshell
  have hf := hfourier d hQpos hsep' hcarry
  have hb := mul_le_mul_of_nonneg_left hband hC₀.le
  apply hf.trans
  convert hb using 1 <;> (try dsimp only [S,F,G,Z]) <;> ring

end PositiveDistanceData

end PlanarFalconer

end OAI
