import OAI.NumberTheory.DirichletL.PrimeRows.PhysicalBound
import OAI.NumberTheory.DirichletL.Detector.HighAbsolute

namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ConcreteTraceCRT ActualEisensteinCubic
local notation "O" => HeckeFamily.O

lemma freeRow_count (R : Finset FreeRow) (H : ℝ) (hH : 1≤H)
    (hR : ∀u∈R,((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤H) :
    (R.card:ℝ)≤128*H := by
  have hc := DescentFiberCost.finite_element_count_real (R.image Subtype.val) H hH (by
    intro a ha
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hR u hu)
  rw [Finset.card_image_of_injective R Subtype.val_injective] at hc
  exact hc

lemma frequencyWeight_ideal_norm (z : ℂ) (u : FreeRow) :
    ‖frequencyWeight z ⟨u.val,u.property.1⟩‖=
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(-z.re) := by
  have hN : (0:ℝ)<((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  unfold frequencyWeight elementNorm
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN,Complex.neg_re]

lemma dyadic_weighted_rows (a r C U : ℝ) (hC : 0≤C) (hU : 1≤U)
    (R : Finset FreeRow)
    (hR : ∀u∈R,U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U)
    (F : FreeRow→ℝ) (hF : ∀u∈R,F u≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^a)
    (z : ℂ) (hz : z.re=r) :
    (∑u∈R,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u)≤
      256*C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(1+a-r) := by
  have hU0 : 0<U := by linarith
  have hcard : (R.card:ℝ)≤256*U := by
    have hc := freeRow_count R (2*U) (by linarith) (fun u hu=>(hR u hu).2)
    linarith
  have hA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 (a-r) (by norm_num)
  calc
    _ ≤ ∑u∈R,C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r) := by
      apply Finset.sum_le_sum
      intro u hu
      have hN : 0<((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := hU0.trans_le (hR u hu).1
      rw [frequencyWeight_ideal_norm,hz]
      calc
        _ ≤ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(-r)*
            (C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^a) :=
          mul_le_mul_of_nonneg_left (hF u hu) (Real.rpow_nonneg hN.le _)
        _ = C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(a-r) := by
          rw [show a-r=(-r)+a by ring,Real.rpow_add hN]
          ring
        _ ≤ _ := by
          have hb := ProbeSelectedPrimeSums.annular_rpow 1 2 U
            ((Ideal.span {u.val}:Ideal O).absNorm:ℝ) (a-r) (by norm_num) (by norm_num) hU0
            (by simpa only [one_mul] using (hR u hu).1) (hR u hu).2
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC
    _ = (R.card:ℝ)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r)) := by simp
    _ ≤ (256*U)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      have hp : U*U^(a-r)=U^(1+a-r) := by
        rw [show 1+a-r=1+(a-r) by ring,Real.rpow_add hU0,Real.rpow_one]
      calc
        _ = (256*C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r))*(U*U^(a-r)) := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily
end

end OAI
