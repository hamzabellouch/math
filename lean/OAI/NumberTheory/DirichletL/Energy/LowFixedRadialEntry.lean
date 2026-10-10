import OAI.NumberTheory.DirichletL.Energy.FixedRadialReduction
import OAI.NumberTheory.DirichletL.Energy.ZeroComparison
import OAI.NumberTheory.DirichletL.Energy.PhysicalEntry

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyLowFixedRadialEntry
open HeckeFamily ConcretePrimeRowBridge QuadraticInitialBound
open CenteredMomentCommonRadialData CenteredMomentEnergyZeroComparison
open CenteredMomentEnergyFixedRadialReduction CenteredMomentEnergyOriginalSource
open CenteredMomentFirstSourceReduction CenteredMomentSourceInputTailUniform
open CenteredMomentSourceRow CenteredMomentSecondHeightFamily
open CenteredMomentOriginalCommonHarmonic CenteredMomentSourceMass
open CenteredMomentEnergyState CenteredMomentEnergyPhysicalEntry
open CenteredMomentRadialEligibleEnergy CenteredMomentInductionEnergy
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

omit [DecidableEq ι] in
lemma zero_control (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)(W₁ W₂:𝓢(ℝ,ℂ)):
    plainControl (zeroInput s hz₁ hz₂) W₁ W₂=plainControl s W₁ W₂:=rfl

theorem original_low_reduction (bΦ:ℝ)(hbΦ:0<bΦ)
    (hi:ι→ℝ)(a b B ε ξ saving:ℝ)
    (hhi:∀i,0≤hi i)(ha:0<a)(hb:0≤b)(hB:0≤B)(hε:0<ε)(hξ:0<ξ):
    ∃Ψ:𝓢(ℝ,ℂ),Function.support (Ψ:ℝ→ℂ)⊆Set.Icc (-1) (bΦ+1) ∧
      (∀x,0≤(Ψ x).re) ∧∃Sdiag Stail:Finset (ℕ×ℕ),∃Cdiag Ctail:ℝ,
      0<Cdiag ∧0<Ctail ∧∀ᶠ Z:ℝ in atTop,1<Z ∧
      ∀(s:Input ι)(W₁ W₂:𝓢(ℝ,ℂ)),∀he₁:s.W₁=W₁,∀he₂:s.W₂=W₂,
      ∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,
      (∀i,s.hi i≤hi i) →∀(R:Ideal O)(r:Radial),
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
      CenteredMomentAmplificationChildInput.volume s≤Z^B → r.scale⁻¹≤Z^B →
      let hz₁:s.W₁ 0=0:=by rw [he₁];exact CenteredMomentDetectorPlainSource.support_zero W₁ a b ha hs₁;
      let hz₂:s.W₂ 0=0:=by rw [he₂];exact CenteredMomentDetectorPlainSource.support_zero W₂ a b ha hs₂;
      energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots s.toData.coefficient
        s.P s.X₁ s.X₂ r.keep r.profile r.scale≤
      2*diagonalControl r.profile*(
        physicalMass (zeroInput s hz₁ hz₂) R 1 fixedBadMask 1 Ψ r.scale Z ξ/
          CenteredMomentAmplificationChildInput.volume s+
        Cdiag*(plainControl s W₁ W₂)^2*Sdiag.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^ε+
        Ctail*(plainControl s W₁ W₂)^2*Stail.sup (schwartzSeminormFamily ℝ ℝ ℂ) Ψ*r.scale*Z^(-saving)):=by
  obtain ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,hred⟩:=actual_original_reduction
    bΦ hbΦ hi a b B ε ξ saving hhi ha hb hB hε hξ
  refine ⟨Ψ,hsΨ,hnΨ,Sdiag,Stail,Cdiag,Ctail,hCd,hCt,?_⟩
  filter_upwards [hred] with Z hz
  refine ⟨hz.1,?_⟩
  intro s W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  dsimp only
  let hz₁:s.W₁ 0=0:=by rw [he₁];exact CenteredMomentDetectorPlainSource.support_zero W₁ a b ha hs₁
  let hz₂:s.W₂ 0=0:=by rw [he₂];exact CenteredMomentDetectorPlainSource.support_zero W₂ a b ha hs₂
  have hh:=hz.2 (zeroInput s hz₁ hz₂) W₁ W₂ he₁ he₂ hs₁ hs₂ hsi R r hr hV hK
  change energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots s.toData.coefficient
    s.P s.X₁ s.X₂ r.keep r.profile r.scale≤_+2*energy s.η (fixedBadMask*idealGenerator R) 1 s.t
    s.W₁ s.W₂ s.slots s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
    r.keep r.profile r.scale at hh
  rw [comparison_energy_zero s hz₁ hz₂ R r,mul_zero,add_zero,zeroInput_volume,zero_control] at hh
  exact hh

omit [DecidableEq ι] in
theorem zero_comparison_product_cap (b B ε:ℝ)(_hB:0≤B)(hε:0<ε):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      s.b₁≤b →s.X₁*s.X₂≤Z^B →
      (zeroInput s hz₁ hz₂).Y₁≤1 ∧
      (zeroInput s hz₁ hz₂).Y₂≤Z^(B+ε):=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro s hz₁ hz₂ hb hprod
  refine ⟨smallScale_le_one _,?_⟩
  change s.X₁*s.X₂/smallScale s.b₁≤_
  have hconst:2*max 1 s.b₁≤Z^ε:=
    (mul_le_mul_of_nonneg_left (max_le_max_left 1 hb) (by norm_num)).trans hc
  unfold smallScale
  rw [div_div_eq_mul_div,div_one]
  calc
    _≤Z^B*Z^ε:=mul_le_mul hprod hconst (by positivity)
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le
    _=Z^(B+ε):=(Real.rpow_add (zero_lt_one.trans hZ) _ _).symm

omit [DecidableEq ι] in
theorem zero_comparison_first_log (b ε:ℝ)(hε:0<ε):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      s.b₁≤b → -ε≤Real.logb Z (zeroInput s hz₁ hz₂).Y₁ ∧
        Real.logb Z (zeroInput s hz₁ hz₂).Y₁≤0:=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro s hz₁ hz₂ hb
  change -ε≤Real.logb Z (smallScale s.b₁) ∧ Real.logb Z (smallScale s.b₁)≤0
  have hconst:2*max 1 s.b₁≤Z^ε:=
    (mul_le_mul_of_nonneg_left (max_le_max_left 1 hb) (by norm_num)).trans hc
  have hlower:Z^(-ε)≤smallScale s.b₁:=by
    rw [Real.rpow_neg (zero_lt_one.trans hZ).le]
    simpa only [smallScale,one_div] using one_div_le_one_div_of_le (by positivity) hconst
  refine ⟨?_,?_⟩
  · have hh:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) hlower
    simpa only [Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hh
  · have hh:=Real.logb_le_logb_of_le hZ (smallScale_pos s.b₁) (smallScale_le_one s.b₁)
    simpa only [Real.logb_one] using hh

end SevenEighths.CenteredMomentEnergyLowFixedRadialEntry

end

end OAI
