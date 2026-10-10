import OAI.NumberTheory.CubicMoment.Angular.AngularScaleFirstStoppedTransport
import OAI.NumberTheory.CubicMoment.Estimates.SparseLowKernel

namespace OAI

/-! The literal late scale-first stopped dyad has a power saving. The
actual coefficient, failed-prefix condition and product cutoff are first
transported exactly, then the proved sparse low-height estimate applies. -/
noncomputable section
open Filter
open scoped BigOperators
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem angular_distinguishedStoppedLate_bound (ℓ : ℤ) (i : ℕ) (hpnt : PrimaryPrimePNT)
    {C ξ ρ ε : ℝ} (hC : 0 < C) (hξ : 0 < ξ)
    (hρ : 1 < ρ) (hρ₂ : ρ ≤ 2) (hε : 0 ≤ ε) (hsmall : ρ ≤ (2:ℝ)^ε)
    (hgap : ξ+ε < 1/100) (Ct : ℕ) :
    ∃ τ K : ℝ, 0 < τ ∧ 0 < K ∧ ∀ᶠ X : ℝ in atTop,
      ∀ (H : ℝ), 0 < H → ∀ h : ℕ,
      geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X ≤ h →
      ρ*geometricBinLower ρ (Real.exp primeProductWeights.radius*X) h ≤ (Real.log X)^C →
      ∀ (d : Fin i → Fin (normPartitionCount (Real.exp primeProductWeights.radius*X)))
        (q : ℕ × ℕ × ℕ) (j k : ℕ), 1 ≤ q.2.1 →
      ‖angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h false d q j k‖ ≤
        K*(1+Real.log X)^Ct*X^(5/6-τ) := by
  have hξz : ξ ≤ 2/5 := by linarith
  obtain ⟨τ,K,hτ,hK,hsparse⟩ := ordinary_sparse_low_kernel (ι := Fin i)
    hpnt hC hξ hξz (show (1:ℝ) ≤ 32 by norm_num) Ct
  obtain ⟨V,_hV,hweights⟩ := distinguishedStoppingWeights_uniform
  refine ⟨τ,K,hτ,hK,?_⟩
  filter_upwards [hsparse,eventually_angular_distinguishedStoppedDyad_geometry ℓ hρ hρ₂ hε hsmall hgap,
    eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop (by norm_num : (0:ℝ) < 38/100)).eventually_ge_atTop 2,
    eventually_const_mul_rpow_le (by norm_num : (39/100:ℝ) < 1) (8*Real.exp 1)]
    with X hsparse hgeom hX hZ hlong
  intro H hH h hh hboundary d q j k hk
  have hL : 0 ≤ 1+Real.log X := by linarith [Real.log_nonneg hX]
  by_cases hn : angular_distinguishedStoppedDyad ℓ i ρ ξ Ct H X h false d q j k = 0
  · rw [hn,norm_zero]
    positivity
  obtain ⟨hBlo,hBhi,hBX,hprodlo,hprodhi,hq⟩ := hgeom i Ct H h false d q j k hk hn
  let A := stoppedNormDyadLength j/2
  let B := stoppedNormDyadLength k
  let Δ := geometricBinCount ρ (Real.exp primeProductWeights.radius*X)-geometricBinCount ρ X
  have hAp : 0 < A := by dsimp [A]; positivity [stoppedNormDyadLength_pos j]
  have hBp : 0 < B := stoppedNormDyadLength_pos k
  have hXp : 0 < X := zero_lt_one.trans_le hX
  have hXF : X ≤ Real.exp primeProductWeights.radius*X :=
    le_mul_of_one_le_left hXp.le (Real.one_le_exp primeProductWeights.radius_nonneg)
  have h2A : Real.exp 1 ≤ 2*A := by
    have hbb : 8*Real.exp 1*B ≤ X := by
      have he := mul_le_mul_of_nonneg_left hBhi (by positivity : 0 ≤ 8*Real.exp 1)
      exact he.trans (by simpa only [Real.rpow_one] using hlong)
    have hm : Real.exp 1*B ≤ (2*A)*B := by
      change X/16 ≤ A*B at hprodlo
      nlinarith
    apply (mul_le_mul_iff_right₀ hBp).mp
    simpa only [mul_comm] using hm
  have hB35 : X^(35/100:ℝ) ≤ B := by
    norm_num only [show (35/100:ℝ) = 7/20 by norm_num]
    exact hBlo
  have hB40 : B ≤ X^(40/100:ℝ) := hBhi.trans
    (Real.rpow_le_rpow_of_exponent_le hX (by norm_num))
  have hAB : 2*A ≤ 32*X/B := by
    apply (le_div_iff₀ hBp).mpr
    change A*B ≤ 16*X at hprodhi
    nlinarith
  have hbnd : ρ*geometricBinLower ρ X (h-Δ) ≤ (Real.log X)^C := by
    have he := geometricBinLower_shift hρ hXp hXF (h-Δ)
    rw [Nat.sub_add_cancel hh] at he
    simpa only [he] using hboundary
  have hP (a : Eisenstein) (ha : a ∈ stoppedNormDyad (distinguishedStoppedSide X) j) :
      primary a ∧ Squarefree a ∧ A ≤ norm a ∧ norm a ≤ 2*A := by
    have hp := distinguishedStoppedSide_spec (Finset.mem_filter.mp ha).1
    have hr := stoppedNormDyad_outer_bounds ha hp.1
    exact ⟨hp.1,hp.2.1,hr.1,by dsimp [A]; nlinarith [hr.2]⟩
  have hQ (b : Eisenstein) (hb : b ∈ stoppedIntervalSupport (Fin i) X (B/2) B 1) :
      primary b ∧ Squarefree b ∧ B/2 ≤ norm b ∧ norm b ≤ B := by
    have hp := stoppedIntervalSupport_spec X (B/2) B 1 hb
    exact ⟨hp.1,hp.2.1,(Finset.mem_filter.mp hb).2.2.2.1.le,hp.2.2⟩
  have he := hsparse A B ρ H ℓ hAp h2A hB35 hB40 hAB hρ hρ₂ hH
    (q.1-Δ) q.2.1 (h-Δ) hbnd
    (fun _ : Fin i => primeCutoff X) (fun a p => distinguishedStoppingWeights d a (norm p))
    (orderedConvolutionSupport (fun _ : Fin i => primeCutoff X)) (primaryElementBall X)
    (centralPrimaryFactors X) (centralPrimaryFactors X)
    (stoppedNormDyad (distinguishedStoppedSide X) j)
    (stoppedIntervalSupport (Fin i) X (B/2) B 1)
    (stoppingRemainingTest (geometricPrimeBin ρ (Real.exp primeProductWeights.radius*X))
      q.1 q.2.2)
    (fun _ _ hp => (mem_primeCutoff.mp hp).1)
    (fun a p _ => (hweights i _ d).1 a (norm p))
    (fun _ hr => orderedPrimarySupport_primary _
      (fun _ _ hp => (mem_primeCutoff.mp hp).1.1) hr)
    (fun _ hd => mem_primaryElementBall.mp hd)
    (fun _ he => (mem_primaryElementBall.mp he).1) hP hQ
  rw [angular_distinguishedStoppedDyad_to_row ℓ i hρ hρ₂ hX Ct H h false d q j k hk
    (by simpa only [Bool.false_eq_true,ite_false] using hZ) hBX hq hh]
  simpa only [B,Δ,distinguishedStoppedAlpha,stoppedRowCoefficient,distinguishedShiftedSideTest,
    show (36/100:ℝ) = 9/25 by norm_num,
    Bool.false_eq_true,ite_false,normTwist,zero_mul,Complex.ofReal_zero,Complex.exp_zero,mul_one]
    using he

end CubicFirstMoment

end

end OAI
