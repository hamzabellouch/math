import OAI.NumberTheory.Ostmann.QuadraticCenter.NormalizedQuadraticGrid

namespace OAI

noncomputable section
namespace Ostmann.QuadraticCenter
open scoped BigOperators

def adaptiveArrayConstant : ℝ := 40*(cutoffFourierBound+1)*(Real.pi+1)

theorem adaptiveArrayConstant_pos : 0 < adaptiveArrayConstant := by
  unfold adaptiveArrayConstant
  have := cutoffFourierBound_pos
  have := Real.pi_pos
  positivity

theorem quadraticGridConstant_le {ω : Type*} (I : Finset ω)
    (a : ω → ℂ) (κ : ω → ℝ) {A B W : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hW : (I.card:ℝ) ≤ W)
    (ha : ∀ w ∈ I, ‖a w‖ ≤ A) (hk : ∀ w ∈ I, |κ w| ≤ B) :
    quadraticGridConstant I a κ ≤ W*A*cutoffFourierBound*((2*Real.pi)*B+(1+B)) := by
  unfold quadraticGridConstant
  calc
    _ ≤ ∑ _w ∈ I, A*cutoffFourierBound*((2*Real.pi)*B+(1+B)) := by
      apply Finset.sum_le_sum
      intro w hw
      have hc := cutoffFourierBound_pos.le
      have hpi := Real.pi_pos.le
      gcongr
      · exact ha w hw
      · exact hk w hw
      · exact hk w hw
    _ = (I.card:ℝ)*(A*cutoffFourierBound*((2*Real.pi)*B+(1+B))) := by simp
    _ ≤ W*(A*cutoffFourierBound*((2*Real.pi)*B+(1+B))) :=
      mul_le_mul_of_nonneg_right hW (by have := cutoffFourierBound_pos; have := Real.pi_pos; positivity)
    _ = _ := by ring

theorem adaptive_quadratic_support_bound {Z : ℕ} (hZ : 1 ≤ Z) {q : ℝ}
    (hq : 0 < q) (hqlo : 1 ≤ (Z:ℝ)*q) :
    ⌊Real.sqrt ((2*Z^13:ℕ)/q)⌋₊ ≤ 2*Z^7 := by
  apply Nat.floor_le_of_le
  apply (Real.sqrt_le_iff).mpr
  refine ⟨by positivity,?_⟩
  apply (div_le_iff₀ hq).mpr
  have h := mul_le_mul_of_nonneg_left hqlo (show 0≤2*(Z:ℝ)^13 by positivity)
  push_cast at *
  have hpos : 0 ≤ (Z:ℝ)^14*q := by positivity
  nlinarith [show 2*(Z:ℝ)^13*((Z:ℝ)*q)=2*(Z:ℝ)^14*q by ring,
    show ((2:ℝ)*(Z:ℝ)^7)^2*q=4*(Z:ℝ)^14*q by ring]

theorem adaptive_quadratic_grid_bound {Z : ℕ} (hZ : 1 ≤ Z)
    (P : ℕ) (a : ℕ → ℂ) {q : ℝ} (hq : 0 < q)
    (hqupper : q ≤ (Z:ℝ)^16) (ha : ∀ w, ‖a w‖ ≤ (Z:ℝ)) :
    2*Real.sqrt q * quadraticGridConstant
      ((Finset.Ioc 0 (2*Z^7)).filter (fun w => P ∣ w)) a
        (fun w => q*(w:ℝ)^2) ≤ adaptiveArrayConstant*(Z:ℝ)^46 := by
  have hZr : (1:ℝ) ≤ Z := by exact_mod_cast hZ
  let I := (Finset.Ioc 0 (2*Z^7)).filter (fun w => P ∣ w)
  have hcard : (I.card:ℝ) ≤ 2*(Z:ℝ)^7 := by
    have hh : I.card ≤ 2*Z^7 := by
      exact (Finset.card_filter_le _ _).trans_eq (by simp)
    exact_mod_cast hh
  have hk : ∀ w ∈ I, |q*(w:ℝ)^2| ≤ 4*(Z:ℝ)^30 := by
    intro w hw
    have hw' : (w:ℝ) ≤ 2*(Z:ℝ)^7 := by
      exact_mod_cast (Finset.mem_Ioc.mp (Finset.mem_filter.mp hw).1).2
    rw [abs_of_nonneg (by positivity)]
    calc
      _ ≤ (Z:ℝ)^16*(2*(Z:ℝ)^7)^2 := by gcongr
      _ = _ := by ring
  have hc := quadraticGridConstant_le I a (fun w => q*(w:ℝ)^2)
    (Nat.cast_nonneg Z) (by positivity : 0≤4*(Z:ℝ)^30) hcard
    (fun w _ => ha w) hk
  have hs : Real.sqrt q ≤ (Z:ℝ)^8 := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity,?_⟩
    convert hqupper using 1
    ring
  have hp : 1 ≤ (Z:ℝ)^30 := one_le_pow₀ hZr
  have hC := cutoffFourierBound_pos
  have hpi := Real.pi_pos
  have hbr : (2*Real.pi)*(4*(Z:ℝ)^30)+(1+4*(Z:ℝ)^30) ≤
      (8*Real.pi+5)*(Z:ℝ)^30 := by nlinarith
  have hcb : quadraticGridConstant I a (fun w => q*(w:ℝ)^2) ≤
      2*cutoffFourierBound*(8*Real.pi+5)*(Z:ℝ)^38 := by
    apply hc.trans
    calc
      _ ≤ (2*(Z:ℝ)^7)*(Z:ℝ)*cutoffFourierBound*((8*Real.pi+5)*(Z:ℝ)^30) := by gcongr
      _ = _ := by ring
  have hmul := mul_le_mul (mul_le_mul_of_nonneg_left hs (by norm_num : (0:ℝ)≤2)) hcb
    (quadraticGridConstant_nonneg _ _ _) (by positivity)
  change 2*Real.sqrt q*quadraticGridConstant I a (fun w => q*(w:ℝ)^2) ≤ _
  apply hmul.trans
  unfold adaptiveArrayConstant
  calc
    _ = (4*cutoffFourierBound*(8*Real.pi+5))*(Z:ℝ)^46 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (by nlinarith [mul_nonneg hC.le hpi.le]) (by positivity)

end Ostmann.QuadraticCenter

end

end OAI
