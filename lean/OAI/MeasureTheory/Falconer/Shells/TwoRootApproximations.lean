import OAI.MeasureTheory.Falconer.Shells.TwoRootShellDecay
import OAI.MeasureTheory.Falconer.Shells.TwoRootRestoration
import OAI.MeasureTheory.Falconer.Shells.RestorationPowerRate

namespace OAI

namespace PlanarFalconer
open Set Metric MeasureTheory
open scoped ContDiff ENNReal

theorem dyadic_negative_power (e : ℝ) (N : ℕ) :
    ((2:ℝ)^N)^(-e) = (2:ℝ)^(-e*(N:ℝ)) := by
  rw [← Real.rpow_natCast,← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2)]
  congr 1
  ring

theorem hasShellApproximations_of_eventual (τ : FiniteMeasure ℝ)
    {eta gamma Ctv Cshell : ℝ} (heta : 0 < eta) (hgamma : 0 < gamma)
    (hCtv : 0 < Ctv) (hCshell : 0 < Cshell) (N₀ : ℕ)
    (h : ∀ N ≥ N₀, ∃ σ : FiniteMeasure ℝ,
      variationDistance τ σ ≤ ENNReal.ofReal (Ctv*(2:ℝ)^(-eta*(N:ℝ))) ∧
        shellEnergy σ N ≤ Cshell*(2:ℝ)^(-gamma*(N:ℝ))) :
    HasShellApproximations τ := by
  classical
  let σ : ℕ → FiniteMeasure ℝ := fun N => if hn : N₀ ≤ N then Classical.choose (h N hn) else 0
  refine ⟨σ,eta,gamma,Ctv,Cshell,heta,hgamma,hCtv,hCshell,N₀,?_⟩
  intro N hN
  dsimp only [σ]
  rw [dite_eq_left hN]
  exact Classical.choose_spec (h N hN)

theorem two_root_has_shell_approximations (Q : Fin 2 → DyadicSquare)
    (hQ : ∀ l, (Q l).side = 1)
    (hlo : 100 ≤ dist (Q 0).center (Q 1).center) (hhi : dist (Q 0).center (Q 1).center ≤ 2000)
    (μ ν : ProbabilityMeasure Plane) (hμQ : (μ:Measure Plane) (Q 0).carrierᶜ = 0)
    (hνQ : (ν:Measure Plane) (Q 1).carrierᶜ = 0)
    {δ β lam sig kap C₀ C₁ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hβ : β = δ/10)
    (hlam : 0 < lam) (hlamδ : lam < δ/1000) (hsig : 0 < sig)
    (hkap : 0 < kap) (hkapβ : 1000000*kap < β) (hgap : sig < kap/1000)
    (hratio : 10000000*(lam+sig)/kap < β/100)
    (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hball₀ : ∀ x : Plane, ∀ r > 0, (μ:Measure Plane) (ball x r) ≤ ENNReal.ofReal (C₀*r^(1+δ)))
    (hball₁ : ∀ x : Plane, ∀ r > 0, (ν:Measure Plane) (ball x r) ≤ ENNReal.ofReal (C₁*r^(1+δ)))
    {p q : ℝ} (hpq : p.HolderConjugate q) {K : ENNReal} (hK : K ≠ ⊤)
    (hμrad : ∀ᵐ x ∂(μ:Measure Plane), sourceDensityNorm p ((ν:Measure Plane).map (sourceRadialUnit x)) ≤ K)
    (hνrad : ∀ᵐ y ∂(ν:Measure Plane), sourceDensityNorm p ((μ:Measure Plane).map (sourceRadialUnit y)) ≤ K)
    {Ψ : ℝ → ℝ} (hΨ : ContDiff ℝ ∞ Ψ) (hpos : ∀ x, 0 ≤ Ψ x)
    (hs : ∀ x, Ψ x ≠ 0 → x ∈ Ioo (1/4:ℝ) 4)
    (hone : ∀ x ∈ Icc (1/2:ℝ) 2, 1 ≤ Ψ x) :
    ∃ hτ : IsFiniteMeasure (weightedDistance ((μ:Measure Plane).prod ν)),
      HasShellApproximations ⟨weightedDistance ((μ:Measure Plane).prod ν),hτ⟩ := by
  have hQ₀ : 0 < (Q 0).side := by rw [hQ 0]; norm_num
  have hQ₁ : 0 < (Q 1).side := by rw [hQ 1]; norm_num
  have hsep : ∀ᵐ z ∂(μ:Measure Plane).prod (ν:Measure Plane), 90 ≤ dist z.1 z.2 := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hμQ,
      Measure.quasiMeasurePreserving_snd.ae hνQ] with z hx hy
    exact (separated_unit_roots_distance Q hQ hlo hhi z.1 z.2 hx hy).1
  let := weightedProductInput_finite (μ:Measure Plane) (ν:Measure Plane) (by norm_num : (0:ℝ) < 90) hsep
  let τ : FiniteMeasure ℝ := ⟨weightedDistance ((μ:Measure Plane).prod ν),inferInstance⟩
  refine ⟨inferInstance,?_⟩
  change HasShellApproximations τ
  obtain ⟨H₀,N₀,hH₀,_,hf₀⟩ := actual_class_family (Q 0) (hQ 0) (μ:Measure Plane) hμQ hC₀ hlam hsig hball₀
  obtain ⟨H₁,N₁,hH₁,_,hf₁⟩ := actual_class_family (Q 1) (hQ 1) (ν:Measure Plane) hνQ hC₁ hlam hsig hball₁
  obtain ⟨NS,hNS,hshell⟩ := uniform_two_root_shell_decay hδ hδ1 hβ hlam hlamδ hsig
    hkap hkapβ hgap hratio hΨ hpos hs hone
  obtain ⟨eta,heta,NR,hrate⟩ := restoration_power_rate H₀ H₁ hlam hsig hpq
  let D := ENNReal.ofReal ((90:ℝ)^(-1/2:ℝ))*(4+2*K)
  have hD : D ≠ ⊤ := by dsimp only [D]; finiteness
  have hDbound : D ≤ ENNReal.ofReal (D.toReal+1) := by
    calc
      D = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
      _ ≤ ENNReal.ofReal (D.toReal+1) := ENNReal.ofReal_le_ofReal (by linarith)
  apply hasShellApproximations_of_eventual τ heta (show 0 < β/2 by rw [hβ]; positivity)
    (show 0 < D.toReal+1 by positivity) (by norm_num : (0:ℝ) < 2)
    (max (max NS NR) (max (max N₀ N₁) (max H₀ H₁)))
  intro N hN
  obtain ⟨m₀,hm₀⟩ := hf₀ N (by omega)
  obtain ⟨m₁,hm₁⟩ := hf₁ N (by omega)
  have hfinite := restoredTwoRootCandidate_finite (Q 0) (Q 1) hQ₀ hQ₁ (μ:Measure Plane) (ν:Measure Plane)
    m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β
  let := hfinite.1
  let := hfinite.2
  let σ : FiniteMeasure ℝ := ⟨restoredTwoRootCandidate (Q 0) (Q 1) μ ν m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β,inferInstance⟩
  refine ⟨σ,?_,?_⟩
  · have hweight : ∀ᵐ z ∂(μ:Measure Plane).prod (ν:Measure Plane), distanceWeight z ≤
        ENNReal.ofReal ((90:ℝ)^(-1/2:ℝ)) := by
      filter_upwards [hsep] with z hz
      exact ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos (by norm_num) hz (by norm_num))
    have hremoved := two_root_restored_removed_mass_bound (Q 0) (Q 1) hQ₀ hQ₁ μ ν m₀ m₁
      (by omega : 0 < N) δ lam sig hkap β hm₀ hm₁ hpq hK hμrad hνrad hweight
    have hrate' := hrate N (by omega) (ENNReal.ofReal ((90:ℝ)^(-1/2:ℝ))) K
    change ((weightedDistance ((μ:Measure Plane).prod ν)).toSignedMeasure -
      (restoredTwoRootCandidate (Q 0) (Q 1) μ ν m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β).toSignedMeasure).totalVariation univ ≤ _
    rw [restoredTwoRootCandidate_totalVariation (Q 0) (Q 1) hQ₀ hQ₁]
    apply (hremoved.trans hrate').trans
    change D*ENNReal.ofReal (((2:ℝ)^N)^(-eta)) ≤ _
    rw [dyadic_negative_power,ENNReal.ofReal_mul (show 0 ≤ D.toReal+1 by positivity)]
    exact mul_le_mul_left hDbound _
  · have hb := hshell N (by omega) Q hQ hlo hhi (μ:Measure Plane) (ν:Measure Plane)
      H₀ H₁ hH₀ hH₁ (by omega) (by omega) m₀ m₁ hm₀ hm₁
    change shellEnergy (restoredTwoRootCandidate (Q 0) (Q 1) μ ν m₀ m₁ N (N/H₀) (N/H₁) lam sig kap β) N ≤ _
    convert hb using 1
    congr 1
    simpa only [neg_div] using (dyadic_negative_power (β/2) N).symm

end PlanarFalconer

end OAI
