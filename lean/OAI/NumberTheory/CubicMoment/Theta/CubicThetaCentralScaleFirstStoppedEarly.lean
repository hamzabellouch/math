import OAI.NumberTheory.CubicMoment.Estimates.ScaleFirstStoppedEarly
import OAI.NumberTheory.CubicMoment.Theta.CubicThetaCentralStoppedOrdinaryLowSaving

namespace OAI

/-! Ordinary cancellation for every actual early stopped dyad. All length,
weight and support conditions are derived from its original finite sum. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment


theorem distinguishedStoppedDyad_early_bound_actual (i : ℕ)
    (hpnt : PrimaryPrimePNT) (hSW : KummerPrimeSiegelWalfisz)
    {C ξ ρ ε : ℝ} (hMV : MontgomeryVaughanBound C) (hC : 0 ≤ C)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (hGamma : ∀ σ : ℝ, 0 < σ → σ < 1/10000 →
      AngularGammaQuotientStripBound (metaplecticAngularShift 0) (-σ-1/6))
    (hξ : 0 < ξ) (hξz : ξ ≤ 2/5) (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2)
    (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε) (hgap : ξ+ε < 1/100)
    (k Ct : ℕ) :
    ∃ (G : ℕ) (K : ℝ), 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ H : ℝ, 0 < H → ∀ h : ℕ,
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h →
      2*(Real.log X)^G ≤ min (X^ξ)
        (geometricBinLower ρ (Real.exp primeProductWeights.radius*X) h) →
      ∀ (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
        (q : ℕ × ℕ × ℕ) (j r : ℕ), 1 ≤ q.2.1 → q.1 < h →
      ‖distinguishedStoppedDyad i ρ ξ Ct H X h true d q j r‖ ≤
        K*X^(5/6:ℝ)/(Real.log X)^k := by
  obtain ⟨G,K,hK,hbound⟩ := ordinary_stopped_low_kernel_bound_actual i hpnt hSW hMV hC
    hHuxley  hGamma hξ hξz hρ hρ₂ k Ct
  refine ⟨G,K,hK,?_⟩
  filter_upwards [hbound,eventually_distinguishedStoppedDyad_geometry hρ hρ₂ hε hsmall hgap,
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 9/25)).eventually_ge_atTop 2,
    eventually_gt_atTop (1:ℝ)] with X hb hg hZ hX
  intro H hH h hh hrough d q j r hk hjh
  have hXp : 0 < X := zero_lt_one.trans hX
  have hlog : 0 < Real.log X := Real.log_pos hX
  by_cases hz : distinguishedStoppedDyad i ρ ξ Ct H X h true d q j r = 0
  · rw [hz,norm_zero]
    positivity
  obtain ⟨hBlo,hBhi,hBX,hABlo,hABhi,hj⟩ := hg i Ct H h true d q j r hk hz
  have hXF : X ≤ Real.exp primeProductWeights.radius*X :=
    le_mul_of_one_le_left hXp.le (Real.one_le_exp primeProductWeights.radius_nonneg)
  have he : geometricBinLower ρ (Real.exp primeProductWeights.radius*X) h =
      geometricBinLower ρ X
        (h-(geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X)) := by
    simpa only [Nat.sub_add_cancel hh] using
      geometricBinLower_shift hρ hXp hXF
        (h-(geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X))
  rw [distinguishedStoppedDyad_to_row i hρ hρ₂ hX.le Ct H h true d q j r hk
    (by simpa only [Bool.true_eq,ite_true] using hZ) hBX hj hh]
  have hP (n : Eisenstein) (hn : n ∈ stoppedNormDyad (distinguishedStoppedSide X) j) :
      primary n ∧ Squarefree n ∧ stoppedNormDyadLength j/2 ≤ norm n ∧
        norm n ≤ 2*(stoppedNormDyadLength j/2) := by
    have hs := distinguishedStoppedSide_spec (Finset.mem_filter.mp hn).1
    have hh := stoppedNormDyad_outer_bounds hn hs.1
    exact ⟨hs.1,hs.2.1,hh.1,by nlinarith [hh.2]⟩
  have hresult := hb _ d (stoppedNormDyadLength j/2) (stoppedNormDyadLength r) H
    hABlo hABhi hBlo hBhi hH
    (q.1-(geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X))
    q.2.1 (h-(geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X))
    (X^(9/25:ℝ)) (X^(9/25:ℝ)) true (by omega)
    (by simpa only [he] using hrough)
    (centralPrimaryFactors X) (centralPrimaryFactors X)
    (stoppedNormDyad (distinguishedStoppedSide X) j)
    (stoppingRemainingTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X)) q.1 q.2.2)
    (fun n hn => (mem_primaryElementBall.mp hn).1) hP
  simpa only [distinguishedStoppedAlpha,distinguishedShiftedSideTest,Bool.true_eq,ite_true]
    using hresult

end CubicFirstMoment

end

end OAI
