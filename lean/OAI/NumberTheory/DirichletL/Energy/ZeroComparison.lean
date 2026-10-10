import OAI.NumberTheory.DirichletL.Energy.OriginalSource
import OAI.NumberTheory.DirichletL.Moments.RetainedProfile

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentEnergyZeroComparison
open HeckeFamily CenteredMomentCommonRadialData CenteredMomentEnergyOriginalSource
open CenteredMomentRadialEligibleEnergy CenteredMomentInductionEnergy
open CenteredMomentRetainedProfile CenteredMomentRetainedEnergy
open CenteredMomentHeckeExpansion CenteredMomentOriginalCommonHarmonic
open CenteredMomentAmplificationChildInput CenteredMomentSourceRow
open CanonicalQuadraticSieve ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
open CenteredMomentSourceProfileMass CenteredMomentHeckeHeight CenteredMomentSourceMass
local notation "O" => HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]
local instance : DecidableEq (ι⊕Fin 2):=energyOriginalSourceDecidableSum

def smallScale (b:ℝ):ℝ:=1/(2*max 1 b)

lemma smallScale_pos (b:ℝ):0<smallScale b:=by unfold smallScale;positivity

lemma smallScale_le_one (b:ℝ):smallScale b≤1:=by
  unfold smallScale
  apply (div_le_iff₀ (by positivity:0<(2:ℝ)*max 1 b)).mpr
  linarith [le_max_left (1:ℝ) b]

lemma smallScale_strict (b:ℝ):smallScale b*b<1:=by
  have hm:0<max 1 b:=zero_lt_one.trans_le (le_max_left _ _)
  unfold smallScale
  have hb:=le_max_right (1:ℝ) b
  rw [div_mul_eq_mul_div,one_mul]
  exact (div_lt_iff₀ (mul_pos (by norm_num) hm)).mpr (by linarith)

def zeroData (s:Input ι):CenteredMomentEligibleEnergy.Data ι := { s.toData with
  Y₁ := smallScale s.b₁
  Y₂ := s.X₁*s.X₂/smallScale s.b₁
  Y₁_pos := smallScale_pos _
  Y₂_pos := div_pos (mul_pos s.X₁_pos s.X₂_pos) (smallScale_pos _)
  same_product := by field_simp [ne_of_gt (smallScale_pos s.b₁)] }

def zeroInput (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0):Input ι :=
  completeInput (zeroData s) hz₁ hz₂ s.ν_bound s.W_bound s.lower s.upper
    s.lower_pos s.lower_le s.upper_ge

omit [DecidableEq ι] in
@[simp] lemma zeroInput_volume (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0):
    volume (zeroInput s hz₁ hz₂)=volume s:=rfl

omit [DecidableEq ι] in
lemma comparison_row_zero (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (R:Ideal O)(z:O):
    positiveSlotRow s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.t (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂=0:=by
  unfold positiveSlotRow
  change _*(rowTwistedSum s.η (fixedBadMask*idealGenerator R) 1 z s.W₁ s.t (smallScale s.b₁)*_*_)=0
  rw [strict_subunit_rowTwistedSum_zero s.η (fixedBadMask*idealGenerator R) 1 z
    s.W₁ s.b₁ s.t (smallScale s.b₁) (smallScale_pos _) s.support₁ (smallScale_strict _)]
  simp only [zero_mul,mul_zero]

omit [DecidableEq ι] in
lemma comparison_energy_zero (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (R:Ideal O)(r:Radial):
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
      r.keep r.profile r.scale=0:=by
  unfold CenteredMomentInductionEnergy.energy
  simp only [comparison_row_zero s hz₁ hz₂ R, norm_zero, zero_pow (by decide : (2:ℕ)≠0),
    zero_mul, ite_self, tsum_zero]

theorem actual_zero_comparison_entry (s:Input ι)(hz₁:s.W₁ 0=0)(hz₂:s.W₂ 0=0)
    (R:Ideal O)(r:Radial):
    CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots
      s.toData.coefficient s.P s.X₁ s.X₂ r.keep r.profile r.scale≤
    2*‖finiteHeckeEnergy s.η fixedBadMask 1 s.t
      (finiteColumns (Fintype.piFinset (zeroInput s hz₁ hz₂).pools))
      (coefficient (zeroInput s hz₁ hz₂) R 1) r.profile r.scale‖/volume s:=by
  have hh:=positive_energy_comparison (zeroInput s hz₁ hz₂) R r
  change _≤_+2*CenteredMomentInductionEnergy.energy s.η (fixedBadMask*idealGenerator R) 1 s.t s.W₁ s.W₂ s.slots
    s.toData.coefficient s.P (zeroInput s hz₁ hz₂).Y₁ (zeroInput s hz₁ hz₂).Y₂
    r.keep r.profile r.scale at hh
  rw [comparison_energy_zero s hz₁ hz₂ R r,mul_zero,add_zero] at hh
  exact hh

omit [DecidableEq ι] in
theorem zero_comparison_scale_caps (b L ε:ℝ)(hL:0≤L)(hε:0<ε):
    ∀ᶠ Z:ℝ in atTop,1<Z ∧ ∀s:Input ι,∀hz₁:s.W₁ 0=0,∀hz₂:s.W₂ 0=0,
      s.b₁≤b → s.X₁≤Z^L → s.X₂≤Z^L →
      (zeroInput s hz₁ hz₂).Y₁≤Z^(2*L+ε) ∧
      (zeroInput s hz₁ hz₂).Y₂≤Z^(2*L+ε):=by
  filter_upwards [(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (2*max 1 b),
    eventually_gt_atTop (1:ℝ)] with Z hc hZ
  refine ⟨hZ,?_⟩
  intro s hz₁ hz₂ hb hX₁ hX₂
  have hZ0:0<Z:=zero_lt_one.trans hZ
  refine ⟨(smallScale_le_one _).trans (Real.one_le_rpow hZ.le (by positivity)),?_⟩
  change s.X₁*s.X₂/smallScale s.b₁≤_
  have hp:s.X₁*s.X₂≤Z^(2*L):=by
    have hh:=mul_le_mul hX₁ hX₂ s.X₂_pos.le (Real.rpow_pos_of_pos hZ0 L).le
    rw [←Real.rpow_add hZ0] at hh
    simpa only [two_mul] using hh
  have hconst:2*max 1 s.b₁≤Z^ε:=(mul_le_mul_of_nonneg_left (max_le_max_left 1 hb) (by norm_num)).trans hc
  unfold smallScale
  rw [div_div_eq_mul_div,div_one]
  calc
    s.X₁*s.X₂*(2*max 1 s.b₁)≤Z^(2*L)*Z^ε:=
      mul_le_mul hp hconst (by positivity) (Real.rpow_pos_of_pos hZ0 _).le
    _=Z^(2*L+ε):=(Real.rpow_add hZ0 _ _).symm

end SevenEighths.CenteredMomentEnergyZeroComparison

end

end OAI
