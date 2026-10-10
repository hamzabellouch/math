import Mathlib
import OAI.Probability.SKBarriers.Coverage.ThermodynamicLimit

namespace OAI

section

section
noncomputable section
open scoped BigOperators
open MeasureTheory ProbabilityTheory Filter Set
namespace SK.Analytic
open scoped Topology

def finiteRateConstant (β : ℝ) : ℝ :=
  (β^2/4)*(60+6*(3/β^2)+2*(3/β^2)^2)

theorem finiteRateConstant_pos {β : ℝ} (hβ : 0 < β) : 0 < finiteRateConstant β := by
  unfold finiteRateConstant
  positivity

theorem finiteComparisonError_rate {β r : ℝ} (hβ : 0 < β) (hr : 2 ≤ r)
    {N k : ℕ} (hN : (N:ℝ) = r^12) (hk0 : r ≤ (k:ℝ)) (hk1 : (k:ℝ) ≤ 2*r) :
    (k:ℝ)/Real.sqrt ((N:ℝ)*(β^2*(1/(β^2*r^4)))) ≤ 1 ∧
    finiteComparisonError β k (1/(β^2*r^4)) N ≤
      finiteRateConstant β*(1/Real.sqrt r) := by
  have hr0 : 0 < r := by linarith
  have hr1 : 1 ≤ r := by linarith
  have hb : β ≠ 0 := hβ.ne'
  have hrn : r ≠ 0 := hr0.ne'
  have hs : Real.sqrt ((N:ℝ)*(β^2*(1/(β^2*r^4)))) = r^4 := by
    rw [hN]
    have he : r^12*(β^2*(1/(β^2*r^4))) = (r^4)^2 := by field_simp
    rw [he,Real.sqrt_sq (by positivity)]
  have hr3 : 1 ≤ r^3 := one_le_pow₀ hr1
  have hr38 : (8:ℝ) ≤ r^3 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) hr 3]
  have hrs : 1 ≤ Real.sqrt r := by simpa using Real.sqrt_le_sqrt hr1
  have hspos : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hsr : Real.sqrt r ≤ r := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hr0.le,by nlinarith⟩
  have hrr3 : r ≤ r^3 := le_self_pow₀ hr1 (by decide)
  have hq : 1/r^3 ≤ 1/Real.sqrt r := one_div_le_one_div_of_le hspos (hsr.trans hrr3)
  have hrho : 1/Real.sqrt r ≤ 1 := (div_le_one hspos).mpr hrs
  have HR : (k:ℝ)/r^4 ≤ 2/r^3 := by
    calc
      _ ≤ (2*r)/r^4 := div_le_div_of_nonneg_right hk1 (by positivity)
      _ = _ := by field_simp
  have HRsmall : (k:ℝ)/r^4 ≤ 1 := HR.trans ((div_le_one (by positivity)).mpr (by linarith))
  have HRmesh : (k:ℝ)/r^4 ≤ 2*(1/Real.sqrt r) := by
    apply HR.trans
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hq (by norm_num : (0:ℝ) ≤ 2)
  have HM : 1/Real.sqrt (k:ℝ) ≤ 1/Real.sqrt r :=
    one_div_le_one_div_of_le hspos (Real.sqrt_le_sqrt hk0)
  let d : ℝ := 3/β^2
  let δ : ℝ := ((k+1:ℕ):ℝ)*(1/(β^2*r^4))
  have hd : 0 < d := by dsimp [d]; positivity
  have hδ0 : 0 ≤ δ := by dsimp [δ]; positivity
  have hδ : δ ≤ d*(1/Real.sqrt r) := by
    have HK : ((k+1:ℕ):ℝ) ≤ 3*r := by push_cast; linarith
    calc
      _ ≤ (3*r)*(1/(β^2*r^4)) := mul_le_mul_of_nonneg_right HK (by positivity)
      _ = d*(1/r^3) := by dsimp [d]; field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hq hd.le
  have hδd : δ ≤ d := hδ.trans (mul_le_of_le_one_right hd.le hrho)
  have HP : δ*(1+δ) ≤ (d*(1/Real.sqrt r))*(1+d) :=
    mul_le_mul hδ (by linarith) (by positivity) (by positivity)
  refine ⟨by simpa only [hs] using HRsmall,?_⟩
  rw [finiteComparisonError,hs]
  change (β^2/4)*(20*((k:ℝ)/r^4+1/Real.sqrt (k:ℝ))+2*δ*(1+δ)+4*δ) ≤ _
  calc
    _ ≤ (β^2/4)*(20*(2*(1/Real.sqrt r)+1/Real.sqrt r)+
      2*((d*(1/Real.sqrt r))*(1+d))+4*(d*(1/Real.sqrt r))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        nlinarith [HRmesh,HM,hδ,HP]
    _ = finiteRateConstant β*(1/Real.sqrt r) := by dsimp [finiteRateConstant,d]; ring
end SK.Analytic

end
end

end

end OAI
