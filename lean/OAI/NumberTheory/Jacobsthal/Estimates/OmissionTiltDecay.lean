import OAI.NumberTheory.Jacobsthal.Primes.BoundaryPrimeMass

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970

section

namespace NumberTheoryLean.OmissionTiltDecay

open _root_.Finset
open FinitePathGeometry ReferenceAdmission VariablePrimeTilt BoundaryPrimeMass

theorem omission_depth_lower {r : ℝ} (hr : 8 ≤ r) :
    r/4 ≤ ((⌊(r-4)/2⌋₊+1:ℕ):ℝ) := by
  have hf := Nat.lt_floor_add_one ((r-4)/2)
  push_cast
  linarith

theorem sqrt_tilt_decay {T r : ℝ} (hT : 0 ≤ T) (hr : 8 ≤ r)
    (hlog : 1 ≤ Real.log r) (hlarge : (16*T)^2 ≤ r) :
    Real.exp (Real.sqrt r*T)/(Real.sqrt r)^(⌊(r-4)/2⌋₊+1) ≤
      Real.exp (-(1/32:ℝ)*r*Real.log (r+2)) := by
  have hr0 : 0 < r := by linarith
  have hs0 : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr0
  have hs : 16*T ≤ Real.sqrt r := by
    have hsq := Real.sq_sqrt hr0.le
    nlinarith [Real.sqrt_nonneg r]
  have hmain : Real.sqrt r*T ≤ r/16 := by
    have hh := mul_le_mul_of_nonneg_right hs hs0.le
    nlinarith [Real.sq_sqrt hr0.le]
  have hlen := omission_depth_lower hr
  have hlog0 : 0 ≤ Real.log r := by linarith
  have hden : r*Real.log r/8 ≤
      ((⌊(r-4)/2⌋₊+1:ℕ):ℝ)*Real.log (Real.sqrt r) := by
    rw [Real.log_sqrt hr0.le]
    nlinarith [mul_le_mul_of_nonneg_right hlen hlog0]
  have hlog2 : Real.log (r+2) ≤ 2*Real.log r := by
    have hh : r+2 ≤ r^2 := by nlinarith
    have hm := Real.log_le_log (by linarith : 0 < r+2) hh
    simpa only [Real.log_pow,Nat.cast_ofNat] using hm
  have hpay : r/16 ≤ r*Real.log r/16 := by
    nlinarith [mul_le_mul_of_nonneg_left hlog hr0.le]
  have hcompare : Real.sqrt r*T-
      ((⌊(r-4)/2⌋₊+1:ℕ):ℝ)*Real.log (Real.sqrt r) ≤
      -(1/32:ℝ)*r*Real.log (r+2) := by
    nlinarith [mul_le_mul_of_nonneg_left hlog2 hr0.le]
  calc
    _ = Real.exp (Real.sqrt r*T-
        ((⌊(r-4)/2⌋₊+1:ℕ):ℝ)*Real.log (Real.sqrt r)) := by
      rw [Real.exp_sub,Real.exp_nat_mul,Real.exp_log hs0]
    _ ≤ _ := Real.exp_le_exp.mpr hcompare

theorem actual_omission_decay : ∃ C w₀ : ℝ,0 < C ∧ 1 < w₀ ∧
    ∀ w : ℝ,w₀ ≤ w → ∀ r : ℝ,2 ≤ r → ∀ i : Side,
      omissionMass w r i ≤ C*Real.exp (-(1/32:ℝ)*r*Real.log (r+2)) := by
  obtain ⟨T,w₀,hT,hw₀,hbound⟩ := uniform_boundary_mass
  let R : ℝ := max 8 (max (Real.exp 1) ((16*T)^2))
  have hR8 : 8 ≤ R := le_max_left _ _
  have hRe : Real.exp 1 ≤ R := (le_max_left _ _).trans (le_max_right _ _)
  have hRT : (16*T)^2 ≤ R := (le_max_right _ _).trans (le_max_right _ _)
  let C : ℝ := max 1 (T*Real.exp ((1/32:ℝ)*R*Real.log (R+2)))
  have hC1 : 1 ≤ C := le_max_left _ _
  have hCT : T*Real.exp ((1/32:ℝ)*R*Real.log (R+2)) ≤ C := le_max_right _ _
  refine ⟨C,w₀,by linarith,hw₀,?_⟩
  intro w hw r hr i
  obtain ⟨hp,_hm,ho⟩ := hbound w hw
  have hw1 : 1 < w := hw₀.trans_le hw
  have hr0 : 0 < r := by linarith
  by_cases hbig : R ≤ r
  · have hr8 := hR8.trans hbig
    have hl : 1 ≤ Real.log r := by
      have hh := Real.log_le_log (Real.exp_pos 1) (hRe.trans hbig)
      simpa using hh
    have ht : 1 ≤ Real.sqrt r := (Real.one_le_sqrt).mpr (by linarith)
    have hv := actual_omission_variable_tilt hw1 (by linarith : 4 ≤ r) ht i
    have hnum := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hp (Real.sqrt_nonneg r))
    calc
      _ ≤ Real.exp (Real.sqrt r*T)/(Real.sqrt r)^(⌊(r-4)/2⌋₊+1) :=
        hv.trans (div_le_div_of_nonneg_right hnum (pow_nonneg (Real.sqrt_nonneg r) _))
      _ ≤ Real.exp (-(1/32:ℝ)*r*Real.log (r+2)) := sqrt_tilt_decay hT.le hr8 hl (hRT.trans hbig)
      _ ≤ _ := le_mul_of_one_le_left (Real.exp_nonneg _) hC1
  · have hrR : r ≤ R := le_of_lt (lt_of_not_ge hbig)
    have hl0 : 0 ≤ Real.log (r+2) := Real.log_nonneg (by linarith)
    have hlR : Real.log (r+2) ≤ Real.log (R+2) := Real.log_le_log (by linarith) (by linarith)
    have hprod : r*Real.log (r+2) ≤ R*Real.log (R+2) :=
      mul_le_mul hrR hlR hl0 (by linarith)
    have hh : (1/32:ℝ)*R*Real.log (R+2) + (-(1/32:ℝ)*r*Real.log (r+2)) ≥ 0 := by nlinarith
    have he := Real.one_le_exp_iff.mpr hh
    calc
      _ ≤ T := ho r i
      _ ≤ T*Real.exp ((1/32:ℝ)*R*Real.log (R+2)+(-(1/32:ℝ)*r*Real.log (r+2))) :=
        le_mul_of_one_le_right hT.le he
      _ = (T*Real.exp ((1/32:ℝ)*R*Real.log (R+2)))*Real.exp (-(1/32:ℝ)*r*Real.log (r+2)) := by
        rw [Real.exp_add]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hCT (Real.exp_nonneg _)

end NumberTheoryLean.OmissionTiltDecay

end

end Erdos970

end OAI
