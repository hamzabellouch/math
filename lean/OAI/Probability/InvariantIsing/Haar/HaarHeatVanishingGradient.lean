import OAI.Probability.InvariantIsing.Haar.HaarHeatGradient

namespace OAI

/-! A single decaying gradient envelope for each polynomial heat orbit. -/
noncomputable section
open Matrix MvPolynomial Filter
open scoped Topology
namespace InvariantIsing

lemma haarPolynomialHeat_gradient_envelope {N d : ℕ} (p : haarPolynomialSpace N d) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ, 0 ≤ t → ∀ U : SpecialOrthogonal N,
      haarPolynomialValue (haarPolynomialGamma
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)
        ((haarPolynomialHeat N d t p : haarPolynomialSpace N d) : MatrixPolynomial N)) U ≤
      (M*Real.exp (-((N:ℝ)-2)*t))^2 := by
  obtain ⟨B,hB⟩ := haarPolynomialValue_bound (haarPolynomialGamma (p : MatrixPolynomial N) p)
  let M := max B 1
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM : 0 ≤ M := by linarith
  have hC (U : SpecialOrthogonal N) :
      haarPolynomialValue (haarPolynomialGamma (p : MatrixPolynomial N) p) U ≤ M^2 := by
    have hb := (le_abs_self _).trans (hB U)
    have hm : B ≤ M := le_max_left _ _
    nlinarith
  refine ⟨M,hM,?_⟩
  intro t ht U
  have hg := haarPolynomialHeat_gradient_bound p (M^2) hC ht U
  have he : Real.exp (2*((N:ℝ)-2)*t)*(M*Real.exp (-((N:ℝ)-2)*t))^2 = M^2 := by
    calc
      _ = M^2*Real.exp (2*((N:ℝ)-2)*t+
          (-((N:ℝ)-2)*t+-((N:ℝ)-2)*t)) := by
        rw [Real.exp_add,Real.exp_add]
        ring
      _ = M^2 := by
        rw [show 2*((N:ℝ)-2)*t+(-((N:ℝ)-2)*t+-((N:ℝ)-2)*t)=0 by ring,
          Real.exp_zero,mul_one]
  have hpos := Real.exp_pos (2*((N:ℝ)-2)*t)
  nlinarith

lemma tendsto_haar_gradient_envelope {N : ℕ} (hN : 3 ≤ N) (M : ℝ) :
    Tendsto (fun t : ℝ => M*Real.exp (-((N:ℝ)-2)*t)) atTop (𝓝 0) := by
  have hρ : 0 < (N:ℝ)-2 := by
    have h3 : (3:ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have ht : Tendsto (fun t : ℝ => -((N:ℝ)-2)*t) atTop atBot := by
    simpa only [Function.comp_def,neg_mul,id_eq] using
      tendsto_neg_atTop_atBot.comp (tendsto_id.const_mul_atTop hρ)
  simpa only [Function.comp_def,mul_zero] using (Real.tendsto_exp_atBot.comp ht).const_mul M

end InvariantIsing

end

end OAI
