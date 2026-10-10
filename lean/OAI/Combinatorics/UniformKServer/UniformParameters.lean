import Mathlib
import OAI.Combinatorics.UniformKServer.ActualEditFinance
import OAI.Combinatorics.UniformKServer.AnchorFinance

namespace OAI

noncomputable section

/-! The source's freely chosen small constants are fixed once and for all.
The parent construction has one absolute squared-log coefficient. -/
namespace UniformKServer.PartitionTree
open Finset
open scoped Classical
variable {X : Type} [Fintype X] [MetricSpace X]

def fixedPilot : TierPilot.Parameters where
  sigma := 1/1000000
  gammaH := 1/1000
  gammaL := 1/100000000
  deltaH := 1/10000
  sigma_pos := by norm_num
  sigma_small := by norm_num
  sigma_gamma := by norm_num
  gammaH_small := by norm_num
  gammaL_pos := by norm_num
  gammaL_small := by norm_num
  deltaH_pos := by norm_num
  deltaH_small := by norm_num

def fixedExponent : ℝ := max 1 (TierInsertion.lifetimeExponent fixedPilot)
def fixedShift : ℝ := 1/(10:ℝ)^20

def fixedConfig (R : ℝ) (hR : 0<R) (base : X) : ActualPartitions.Config X where
  P := fixedPilot
  C := fixedExponent
  C_one := le_max_left _ _
  C_large := le_max_right _ _
  R := R
  R_pos := hR
  q := fixedShift
  q_pos := by norm_num [fixedShift]
  q_small := by norm_num [fixedShift]
  shiftH := by norm_num [fixedShift,fixedPilot]
  shiftL := by norm_num [fixedShift,fixedPilot]
  base := base

def metricRadius : ℝ := 1+∑ x : X,∑ y : X,dist x y

theorem metricRadius_pos : 0 < metricRadius (X:=X) := by
  have hh : 0≤∑ x : X,∑ y : X,dist x y := sum_nonneg fun x _=>sum_nonneg fun y _=>dist_nonneg
  unfold metricRadius
  linarith

theorem metricRadius_bounds (x y : X) : dist x y≤40*metricRadius (X:=X) := by
  have h₁ := single_le_sum (fun y _=>show 0≤dist x y from dist_nonneg) (mem_univ y)
  have h₂ : (∑ y : X,dist x y)≤∑ x : X,∑ y : X,dist x y := single_le_sum (fun x _=>sum_nonneg (fun y _=>show 0≤dist x y from dist_nonneg)) (mem_univ x)
  have hn : 0≤∑ x : X,∑ y : X,dist x y := sum_nonneg fun x _=>sum_nonneg fun y _=>dist_nonneg
  unfold metricRadius
  linarith

theorem terminal_scale (A : ActualPartitions.Config X) :
    ∃ J : ℕ,0<J ∧ ∀ x y : X,x≠y → 20*radius A J<dist x y := by
  have ht : Filter.Tendsto (fun J : ℕ=>20*radius A J) Filter.atTop (nhds 0) := by
    have hh := (tendsto_const_nhds (x:=20*A.R)).mul
      (tendsto_pow_atTop_nhds_zero_of_lt_one A.q_pos.le (by linarith [A.q_small]))
    simpa only [mul_zero,radius,mul_assoc] using hh
  have he (x y : X) : ∀ᶠ J : ℕ in Filter.atTop,x≠y → 20*radius A J<dist x y := by
    by_cases h : x=y
    · exact Filter.Eventually.of_forall (fun _ hn=>(hn h).elim)
    · exact (ht.eventually (gt_mem_nhds (dist_pos.mpr h))).mono (fun _ hh _=>hh)
  have hh : ∀ᶠ J : ℕ in Filter.atTop,∀ x y : X,x≠y → 20*radius A J<dist x y :=
    Filter.eventually_all.mpr (fun x=>Filter.eventually_all.mpr (he x))
  obtain ⟨J,hJ,h⟩ := ((Filter.eventually_gt_atTop 0).and hh).exists
  exact ⟨J,hJ,h⟩

omit [Fintype X] [MetricSpace X]

def allocationScalar (A : ActualPartitions.Config X) : ℝ :=
  (8*(10:ℝ)^63/A.q)*(A.editBound+separationRate A)

def driftScalar : ℝ := (6/5)*132*(2+7/Real.log 2)

def rawRate (A : ActualPartitions.Config X) : ℝ :=
  (15840+160*(12/5)*(1+1/22))*allocationScalar A+
    160*(289*((6/5)*132)*(A.editBound+separationRate A)+driftScalar/3)

theorem editBound_nonneg (A : ActualPartitions.Config X) : 0≤A.editBound := by
  unfold ActualPartitions.Config.editBound
  exact add_nonneg (mul_nonneg (by norm_num) (PilotFamily.rateBound_nonneg A.P)) A.editRate_nonneg

theorem allocationScalar_nonneg (A : ActualPartitions.Config X) : 0≤allocationScalar A := by
  unfold allocationScalar
  exact mul_nonneg (div_nonneg (by positivity) A.q_pos.le)
    (add_nonneg (editBound_nonneg A) (separationRate_nonneg A))

theorem driftScalar_pos : 0<driftScalar := by
  have hh : 0<Real.log 2 := Real.log_pos (by norm_num)
  unfold driftScalar
  positivity

theorem rawRate_nonneg (A : ActualPartitions.Config X) : 0≤rawRate A := by
  have h₁ := allocationScalar_nonneg A
  have h₂ := editBound_nonneg A
  have h₃ := separationRate_nonneg A
  have h₄ := driftScalar_pos
  unfold rawRate
  positivity

theorem rate_quadratic (A : ActualPartitions.Config X) (k : ℕ) :
    15840*allocationRate A k+anchorRate A k≤rawRate A*(EpochAlpha.ell k)^2 := by
  have hℓ := EpochAlpha.ell_one k
  have hr := add_nonneg (editBound_nonneg A) (separationRate_nonneg A)
  let b := ((6/5:ℝ)*132)*(A.editBound+separationRate A)
  have hb : 0≤b := mul_nonneg (by norm_num) hr
  have hs : 0≤driftScalar/3 := div_nonneg driftScalar_pos.le (by norm_num)
  have he : KeySizeTracker.ell (k+1)=EpochAlpha.ell k := rfl
  have hd : driftLog k=driftScalar*(EpochAlpha.ell k-1) := by
    unfold driftLog driftScalar EpochAlpha.ell
    ring
  have ha : allocationRate A k=allocationScalar A*(EpochAlpha.ell k)^2 := by
    unfold allocationRate allocationScalar EpochAlpha.ell
    ring
  have hn : (EpochAlpha.ell k-1)≤(EpochAlpha.ell k)^2 := by nlinarith
  have hlog := mul_le_mul_of_nonneg_left hn hs
  have hlin : (1+288*EpochAlpha.ell k)*EpochAlpha.ell k≤289*(EpochAlpha.ell k)^2 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hlin hb
  rw [ha]
  unfold anchorRate rawRate
  rw [he,ha,hd]
  dsimp only [b] at hmul
  dsimp only [EpochAlpha.ell] at hℓ hn hlin hlog hmul ⊢
  nlinarith only [hlog,hmul]

def logFactor : ℝ := 1+1/Real.log 2

theorem ell_log (k : ℕ) (hk : 1≤k) : EpochAlpha.ell k≤logFactor*Real.log (k+1) := by
  have h₂ : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hk' : (2:ℝ)≤k+1 := by exact_mod_cast (show 2≤k+1 by omega)
  have hl := Real.log_le_log (by norm_num : (0:ℝ)<2) hk'
  have hh : 1≤Real.log (k+1)/Real.log 2 := (le_div_iff₀ h₂).mpr (by simpa using hl)
  unfold EpochAlpha.ell logFactor
  simp only [div_eq_mul_inv] at hh ⊢
  nlinarith only [hh]

theorem rate_logSquared (A : ActualPartitions.Config X) (k : ℕ) (hk : 1≤k) :
    15840*allocationRate A k+anchorRate A k≤
      (rawRate A*logFactor^2)*(Real.log (k+1))^2 := by
  have he := ell_log k hk
  have hℓ := EpochAlpha.ell_one k
  have hsq : (EpochAlpha.ell k)^2≤(logFactor*Real.log (k+1))^2 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left hsq (rawRate_nonneg A)
  calc
    _≤rawRate A*(EpochAlpha.ell k)^2 := rate_quadratic A k
    _≤rawRate A*(logFactor*Real.log (k+1))^2 := hh
    _=_ := by ring

/-- This coefficient contains only the fixed numerical parameters, never an
instance size, aspect ratio, tree height, hidden law, or horizon. -/
def absoluteRate : ℝ := rawRate (fixedConfig (X:=PUnit) 1 (by norm_num) PUnit.unit)*logFactor^2

theorem rawRate_fixed (R : ℝ) (hR : 0<R) (base : X) :
    rawRate (fixedConfig R hR base)=rawRate (fixedConfig (X:=PUnit) 1 (by norm_num) PUnit.unit) := rfl

theorem fixed_rate (R : ℝ) (hR : 0<R) (base : X) (k : ℕ) (hk : 1≤k) :
    15840*allocationRate (fixedConfig R hR base) k+anchorRate (fixedConfig R hR base) k≤
      absoluteRate*(Real.log (k+1))^2 := by
  simpa only [rawRate_fixed,absoluteRate] using rate_logSquared (fixedConfig R hR base) k hk

theorem absoluteRate_nonneg : 0≤absoluteRate :=
  mul_nonneg (rawRate_nonneg _) (sq_nonneg _)

end UniformKServer.PartitionTree

end

end OAI
