import Mathlib
import OAI.Analysis.HardSphere.Geometry.GridActivePenalty

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open scoped BigOperators ComplexConjugate
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators
open MeasureTheory ProbabilityTheory Real Complex
open scoped ENNReal ComplexConjugate
open ProbabilityTheory
open MeasureTheory Filter Set
open scoped ENNReal Topology
open MeasureTheory Set
open scoped ENNReal
open MeasureTheory Filter Set
open scoped ENNReal Topology BigOperators
open Set Function MeasureTheory
open scoped ENNReal
namespace HardSphere
open SphericalCoordinates
open scoped BigOperators

lemma near_grid_scale {s L : ℝ} (hs : 0<s) (hL : 10*s≤L) :
    ∃ j : ℕ, 0<j ∧ ∃ l : ℝ, 0<l ∧ L=(j:ℝ)*l ∧ 4*s<l ∧ l≤10*s := by
  let j := ⌊L/(5*s)⌋₊
  have h5 : 0<5*s := by positivity
  have hy : 2≤L/(5*s) := (le_div_iff₀ h5).mpr (by linarith)
  have hj : 0<j := Nat.floor_pos.mpr (by linarith)
  have hjr : 0<(j:ℝ) := by exact_mod_cast hj
  have hfloor := Nat.floor_le (le_trans (by norm_num : (0:ℝ)≤2) hy)
  have hfloor' := Nat.lt_floor_add_one (L/(5*s))
  change (j:ℝ)≤L/(5*s) at hfloor
  change L/(5*s)<(j:ℝ)+1 at hfloor'
  have hlow : 5*s≤L/(j:ℝ) := by
    rw [le_div_iff₀ hjr]
    have hh := (le_div_iff₀ h5).mp hfloor
    nlinarith
  have hupp : L/(j:ℝ)≤10*s := by
    rw [div_le_iff₀ hjr]
    have hh := (div_lt_iff₀ h5).mp hfloor'
    have hj1 : 1≤(j:ℝ) := by exact_mod_cast hj
    nlinarith
  refine ⟨j,hj,L/(j:ℝ),lt_of_lt_of_le (by positivity) hlow,?_,by linarith,hupp⟩
  field_simp

lemma dirichlet_near_energy {n : ℕ} {L : Length} {a s : ℝ}
    (hs : 0<s) (hL : 10*s≤L.val) (p : Fin n → Prop) [DecidablePred p] (ha : 0<a)
    (u : Jet n L) (hu : u∈dirichletDomain n L a) :
    ENNReal.ofReal (27/(262144*Real.sqrt 3)*a/s^3)*
      (∫⁻ X, ((nearLabels p s X).card:ℝ≥0∞)*ENNReal.ofReal (‖u.1 X‖^2)) ≤
        ENNReal.ofReal (selectedEnergy p u) := by
  obtain ⟨j,hj,l,hl,hLj,hsl,hls⟩ := near_grid_scale hs hL
  let : NeZero j := ⟨Nat.ne_of_gt hj⟩
  have h := dirichlet_near_energy_grid hl hLj hsl p ha u hu
  have he := selectedEnergy_nonneg p u
  have hc : 0≤27/(262144*Real.sqrt 3)*a/s^3 := by positivity
  have hs3 : 0<s^3 := by positivity
  have hratio : l^3/s^3≤1000 := by
    apply (div_le_iff₀ hs3).mpr
    have hh := pow_le_pow_left₀ hl.le hls 3
    nlinarith
  have hf : (27/(262144*Real.sqrt 3)*a/s^3)*(8*Real.sqrt 3*l^3/a)≤1 := by
    calc
      _ = (216/262144:ℝ)*(l^3/s^3) := by
        field_simp [ne_of_gt ha,ne_of_gt hs,ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<3))]
        ring
      _ ≤ (216/262144:ℝ)*1000 := mul_le_mul_of_nonneg_left hratio (by norm_num)
      _ ≤ 1 := by norm_num
  calc
    _ ≤ ENNReal.ofReal (27/(262144*Real.sqrt 3)*a/s^3) * ENNReal.ofReal (8*Real.sqrt 3*l^3/a*selectedEnergy p u) := mul_le_mul_of_nonneg_left h zero_le
    _ = ENNReal.ofReal ((27/(262144*Real.sqrt 3)*a/s^3)*(8*Real.sqrt 3*l^3/a)*selectedEnergy p u) := by
      rw [←ENNReal.ofReal_mul hc]
      congr 1
      ring
    _ ≤ ENNReal.ofReal (1*selectedEnergy p u) := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hf he)
    _ = _ := by rw [one_mul]
end HardSphere

end

end OAI
