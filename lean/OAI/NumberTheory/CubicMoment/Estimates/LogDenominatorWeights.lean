import OAI.NumberTheory.CubicMoment.Estimates.SmoothLogDenominator
import OAI.NumberTheory.CubicMoment.Estimates.CompactParameterWeights
import OAI.NumberTheory.CubicMoment.Estimates.UniformWeightCoordinates

namespace OAI

/-! Uniform weights for the literal factor Λ(a)/log(Na). -/
noncomputable section
open Set Filter
open scoped ContDiff Topology BigOperators
namespace CubicFirstMoment

def logWeightParameters (c : ℝ) : Set (ℝ × ℝ) := Icc c 1 ×ˢ Icc 0 1

lemma logWeightParameters_compact (c : ℝ) : IsCompact (logWeightParameters c) :=
  isCompact_Icc.prod isCompact_Icc

def logDenominatorWeight_uniform {c : ℝ} (hc : 0 < c)
    (w : ℝ → ℂ) (hw : HasCompactSupport w) (hpos : tsupport w ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ w) :
    UniformLogWeights (fun p : logWeightParameters c => logDenominatorWeight c w p) := by
  apply uniformLogWeights_compactParameter (logWeightParameters c)
    (logWeightParameters_compact c) (logDenominatorWeight c w) w hw hpos hsm
    (logDenominatorWeight_joint_smooth hc hsm)
  intro p hp x hx
  exact (mul_ne_zero_iff.mp hx).2

def coordinateLogDenominatorWeights {ι : Type*} [Fintype ι]
    {c : ℝ} (hc : 0 < c) (w : ι → ℝ → ℂ)
    (hw : ∀ i, HasCompactSupport (w i)) (hpos : ∀ i, tsupport (w i) ⊆ Ioi 0)
    (hsm : ∀ i, ContDiff ℝ ∞ (w i)) :
    UniformLogWeights (fun z : (ι → logWeightParameters c) × ι =>
      logDenominatorWeight c (w z.2) (z.1 z.2)) := by
  let L : (ι → logWeightParameters c) → ι → ℝ → ℂ :=
    fun p i x => logDenominatorWeight c (w i) (p i) x
  have hL (i : ι) : UniformLogWeights (fun p : ι → logWeightParameters c => L p i) :=
    UniformLogWeights.reindex
      (logDenominatorWeight_uniform hc (w i) (hw i) (hpos i) (hsm i))
      (fun p : ι → logWeightParameters c => p i)
  exact @UniformLogWeights.finiteCoordinates (ι → logWeightParameters c) ι _ L hL

lemma logWeightParameters_mem {c Y X : ℝ} (_hc : 0 < c) (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y)
    (hlo : Y^c ≤ X) (hhi : X ≤ Y) :
    (Real.log X/Real.log Y,1/Real.log Y) ∈ logWeightParameters c := by
  have hlogY : 0 < Real.log Y := by linarith
  have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
  refine ⟨⟨?_,?_⟩,⟨by positivity,?_⟩⟩
  · apply (le_div_iff₀ hlogY).mpr
    have h := Real.log_le_log (Real.rpow_pos_of_pos hY0 c) hlo
    rw [Real.log_rpow hY0] at h
    nlinarith
  · exact (div_le_one hlogY).mpr (Real.log_le_log hX hhi)
  · exact (one_div_le_one_div_of_le (by norm_num) hY).trans_eq (by norm_num)

/-- On the support range the smooth extension is precisely the factor
log(Y)/log(Xx), with no approximation. -/
lemma logDenominatorWeight_scale {c Y X x : ℝ} (hc : 0 < c)
    (hY0 : 0 < Y) (hY : 1 ≤ Real.log Y) (hlo : Y^c ≤ X) (hhi : X ≤ Y) (hx : 1 ≤ x)
    (w : ℝ → ℂ) :
    logDenominatorWeight c w (Real.log X/Real.log Y,1/Real.log Y) x =
      (Real.log Y:ℂ)*w x/(Real.log (X*x):ℂ) := by
  have hp := logWeightParameters_mem hc hY0 hY hlo hhi
  have hlogY : Real.log Y ≠ 0 := ne_of_gt (by linarith)
  have hX : 0 < X := (Real.rpow_pos_of_pos hY0 c).trans_le hlo
  have hx0 : 0 < x := by linarith
  rw [logDenominatorWeight_eq hc w hp.1.1 hp.2.1 hx,Real.log_mul hX.ne' hx0.ne']
  push_cast
  have hCY : (Real.log Y:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogY
  field_simp

end CubicFirstMoment

end

end OAI
