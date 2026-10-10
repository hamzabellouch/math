import OAI.NumberTheory.TotientAsymptotic.NormalityGrid

namespace OAI

/-! A common integer endpoint for every interval in the normality grid. -/
noncomputable section
namespace TotientAsymptotic

def normalityGridEnvelope (x : ℝ) : ℕ :=
  ⌈normalityGridPoint (⌊B x⌋₊+1)⌉₊

lemma normalityGridEnvelope_bounds {x : ℝ} (hx : Real.exp 1 ≤ x) :
    x ≤ normalityGridEnvelope x ∧ 2 ≤ normalityGridEnvelope x ∧
    normalityGridPoint (⌊B x⌋₊+1) ≤ normalityGridEnvelope x ∧
    Real.log (normalityGridEnvelope x) ≤ (Real.exp 1+1)*Real.log x := by
  have hx0 : 0<x := (Real.exp_pos _).trans_le hx
  have hx1 : 1<x := (Real.one_lt_exp_iff.mpr (by norm_num : (0:ℝ)<1)).trans_le hx
  have hlog : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).mpr hx
  have hB : 0 ≤ B x := Real.log_nonneg hlog
  let Y := normalityGridPoint (⌊B x⌋₊+1)
  have hY : 1<Y := normalityGridPoint_one_lt _
  have hceil : Y≤normalityGridEnvelope x := Nat.le_ceil Y
  have hNx : x≤normalityGridEnvelope x := (normalityGridPoint_bracket hx1 hB).2.le.trans hceil
  have hN2 : 2 ≤ normalityGridEnvelope x := by
    have htwo : (2:ℝ)≤Y := by
      have h1 := Real.one_le_exp (show (0:ℝ) ≤ ((⌊B x⌋₊+1:ℕ):ℝ) by positivity)
      have h2 := Real.add_one_le_exp (Real.exp ((⌊B x⌋₊+1:ℕ):ℝ))
      dsimp [Y,normalityGridPoint]
      linarith
    exact_mod_cast htwo.trans hceil
  have hN0 : (0:ℝ)<normalityGridEnvelope x := by exact_mod_cast (show 0<normalityGridEnvelope x by omega)
  have hupper : (normalityGridEnvelope x:ℝ)≤2*Y := by
    have hh := Nat.ceil_lt_add_one (le_of_lt (zero_lt_one.trans hY))
    dsimp [normalityGridEnvelope,Y] at *
    linarith
  have hinner : Real.exp (((⌊B x⌋₊+1:ℕ):ℝ)) ≤ Real.exp 1*Real.log x := by
    calc
      _ ≤ Real.exp (B x+1) := by
        apply Real.exp_le_exp.mpr
        push_cast
        linarith [Nat.floor_le hB]
      _ = _ := by rw [Real.exp_add]; simp only [B,Real.exp_log (by linarith : 0<Real.log x)]; ring
  have hlog2 : Real.log (2:ℝ)≤1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<2)]
  refine ⟨hNx,hN2,hceil,?_⟩
  calc
    _ ≤ Real.log (2*Y) := Real.log_le_log hN0 hupper
    _ = Real.log 2+Real.exp (((⌊B x⌋₊+1:ℕ):ℝ)) := by
      rw [Real.log_mul (by norm_num) (by linarith : Y≠0)]
      simp only [Y,normalityGridPoint,Real.log_exp]
    _ ≤ _ := by nlinarith

end TotientAsymptotic

end

end OAI
