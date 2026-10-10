import Mathlib
import OAI.Probability.SphericalField.Perceptron.TimeLaw
import OAI.Probability.SphericalField.Control.Filtration

namespace OAI

section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal NNReal Topology BigOperators BoundedContinuousFunction

namespace SphericalPerceptron
open Matrix
open scoped InnerProductSpace

variable {H : Type*} [SeminormedAddCommGroup H] [InnerProductSpace ℝ H]
lemma controlPayoff_compact_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (f g : ℝ →ᵇ ℝ)
    (K R ε : ℝ) (hK : 0 ≤ K) (hR : 0 < R) (hε : 0 ≤ ε)
    (hf : ‖f‖ ≤ K) (hg : ‖g‖ ≤ K)
    (hnear : ∀ x : ℝ, |x| ≤ R → |f x - g x| ≤ ε)
    (m : Trial) {v : Time → BrownianPath → ℝ} (hv : Progressive P v)
    (hc : controlCost P m v < ∞) :
    |controlPayoff P f m v - controlPayoff P g m v| ≤
      ε + (2 * K / R^2) * (2 + 2 * (controlCost P m v).toReal) := by
  let X := fun ω => brownianEval 1 ω + controlDrift m v ω
  have hfI := controlReward_integrable P f m hv
  have hgI := controlReward_integrable P g m hv
  have hX : Integrable (fun ω => X ω ^ 2) P := by
    have hb := (hB.isGaussianProcess.hasGaussianLaw_eval 1).memLp_two
    have hd := (memLp_two_iff_integrable_sq
      (controlDrift_aemeasurable P m hv).aestronglyMeasurable).mpr
      (controlDrift_sq_integrable P m hv hc)
    exact (hb.add hd).integrable_sq
  have hconst : 0 ≤ 2 * K / R ^ 2 := div_nonneg (by positivity) (sq_nonneg _)
  have hbound (x : ℝ) : |f x - g x| ≤ ε + (2*K/R^2)*x^2 := by
    by_cases hx : |x| ≤ R
    · exact (hnear x hx).trans (le_add_of_nonneg_right (mul_nonneg hconst (sq_nonneg _)))
    · have habs : |f x - g x| ≤ 2*K := by
        calc
          _ ≤ |f x| + |g x| := abs_sub _ _
          _ ≤ K + K := add_le_add ((f.norm_coe_le_norm x).trans hf)
            ((g.norm_coe_le_norm x).trans hg)
          _ = _ := by ring
      have hsq : R^2 ≤ x^2 := by nlinarith [sq_abs x, lt_of_not_ge hx]
      have hr : R^2 ≠ 0 := ne_of_gt (sq_pos_of_pos hR)
      have heq : (2*K/R^2)*R^2 = 2*K := div_mul_cancel₀ _ hr
      have hb := mul_le_mul_of_nonneg_left hsq hconst
      rw [heq] at hb
      exact habs.trans (hb.trans (le_add_of_nonneg_left hε))
  have heq : controlPayoff P f m v - controlPayoff P g m v =
      ∫ ω, (f (X ω) - g (X ω)) ∂P := by
    rw [integral_sub hfI hgI]
    unfold controlPayoff controlDrift
    ring
  rw [heq]
  calc
    _ ≤ ∫ ω, |f (X ω) - g (X ω)| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (ε + (2*K/R^2)*X ω^2) ∂P :=
      integral_mono (hfI.sub hgI).abs ((integrable_const ε).add (hX.const_mul _))
        (fun ω => hbound (X ω))
    _ = ε + (2*K/R^2) * ∫ ω, X ω^2 ∂P := by
      rw [integral_add (integrable_const ε) (hX.const_mul _), integral_const_mul]
      simp
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_left
      (controlledTerminal_sq_integral_le P hB m hv hc) hconst)

lemma controlValue_le_of_cost_cutoff (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (f : ℝ →ᵇ ℝ) (m : Trial) (K b : ℝ) (hf : ‖f‖ ≤ K)
    (hb : -K ≤ b)
    (hsmall : ∀ v : Time → BrownianPath → ℝ, Progressive P v →
      controlCost P m v < ∞ → (controlCost P m v).toReal ≤ 4*K+2 →
      controlPayoff P f m v ≤ b) : controlValue P f m ≤ b := by
  apply csSup_le (controlPayoffs_nonempty P f m)
  rintro a ⟨v, hv, hc, rfl⟩
  by_cases hcost : (controlCost P m v).toReal ≤ 4*K+2
  · exact hsmall v hv hc hcost
  · have hr := (abs_le.mp (abs_integral_reward_le P f
      (fun ω => brownianEval 1 ω + ∫ t, m t * v t ω ∂timeLaw))).2
    unfold controlPayoff
    linarith [lt_of_not_ge hcost]

lemma controlValue_compact_bound (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (f g : ℝ →ᵇ ℝ)
    (K R ε : ℝ) (hK : 0 ≤ K) (hR : 0 < R) (hε : 0 ≤ ε)
    (hf : ‖f‖ ≤ K) (hg : ‖g‖ ≤ K)
    (hnear : ∀ x : ℝ, |x| ≤ R → |f x - g x| ≤ ε)
    (m : Trial) :
    |controlValue P f m - controlValue P g m| ≤
      ε + (2 * K / R^2) * (2 + 2 * (4*K+2)) := by
  let δ := ε + (2*K/R^2)*(2+2*(4*K+2))
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hfg : controlValue P f m ≤ controlValue P g m + δ := by
    apply controlValue_le_of_cost_cutoff P f m K _ hf
    · linarith [neg_norm_le_controlValue P g m]
    · intro v hv hc hcost
      have hd := (abs_le.mp (controlPayoff_compact_bound P hB f g K R ε hK hR hε
        hf hg hnear m hv hc)).2
      have hp : controlPayoff P g m v ≤ controlValue P g m :=
        le_csSup (controlPayoffs_bddAbove P g m) ⟨v, hv, hc, rfl⟩
      have hh : ε + (2*K/R^2)*(2+2*(controlCost P m v).toReal) ≤ δ := by
        dsimp [δ]
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      linarith
  have hgf : controlValue P g m ≤ controlValue P f m + δ := by
    apply controlValue_le_of_cost_cutoff P g m K _ hg
    · linarith [neg_norm_le_controlValue P f m]
    · intro v hv hc hcost
      have hd := (abs_le.mp (controlPayoff_compact_bound P hB f g K R ε hK hR hε
        hf hg hnear m hv hc)).1
      have hp : controlPayoff P f m v ≤ controlValue P f m :=
        le_csSup (controlPayoffs_bddAbove P f m) ⟨v, hv, hc, rfl⟩
      have hh : ε + (2*K/R^2)*(2+2*(controlCost P m v).toReal) ≤ δ := by
        dsimp [δ]
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
      linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

lemma controlValue_uniform_of_compact (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (hB : IsBrownianReal brownianEval P) (f : ℝ →ᵇ ℝ) (fseq : ℕ → ℝ →ᵇ ℝ)
    (K : ℝ) (hK : 0 ≤ K) (hf : ‖f‖ ≤ K) (hseq : ∀ n, ‖fseq n‖ ≤ K)
    (hcomp : ∀ R : ℝ, 0 < R → ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ x : ℝ, |x| ≤ R → |fseq n x - f x| ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m : Trial,
      |controlValue P (fseq n) m - controlValue P f m| < ε := by
  intro ε hε
  let C := 2*K*(2+2*(4*K+2))
  have hC : 0 ≤ C := by dsimp [C]; positivity
  let Q := C / (ε/2)
  have hQ : 0 ≤ Q := div_nonneg hC (by positivity)
  let R := Q+1
  have hR : 0 < R := by dsimp [R]; positivity
  have hQR : Q < R^2 := by dsimp [R]; nlinarith [sq_nonneg Q]
  have hCQ : C = (ε/2)*Q := by dsimp [Q]; field_simp
  have htail : C/R^2 < ε/2 := by
    apply (div_lt_iff₀ (sq_pos_of_pos hR)).mpr
    rw [hCQ]
    exact mul_lt_mul_of_pos_left hQR (by positivity)
  obtain ⟨N,hN⟩ := hcomp R hR (ε/2) (by positivity)
  refine ⟨N, fun n hn m => ?_⟩
  have hb := controlValue_compact_bound P hB (fseq n) f K R (ε/2) hK hR
    (by positivity) (hseq n) hf (hN n hn) m
  have heq : (2*K/R^2)*(2+2*(4*K+2)) = C/R^2 := by dsimp [C]; ring
  rw [heq] at hb
  linarith

def terminalVariational (P : Measure BrownianPath) (α : ℝ) (f : ℝ →ᵇ ℝ) : EReal :=
  ⨅ m : Trial, ((α * controlValue P f m : ℝ) : EReal) + (entropy m).toEReal

lemma variationalValue_eq_terminal (P : Measure BrownianPath) (α β : ℝ) (φ : ℝ →ᵇ ℝ) :
    variationalValue P α β φ = terminalVariational P α (β • φ) := rfl

lemma terminalVariational_bounds (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f : ℝ →ᵇ ℝ) :
    ((-α*‖f‖ : ℝ) : EReal) ≤ terminalVariational P α f ∧
      terminalVariational P α f ≤ ((α*‖f‖ : ℝ) : EReal) := by
  constructor
  · apply le_iInf
    intro m
    have hcv : -α*‖f‖ ≤ α*controlValue P f m := by
      nlinarith [mul_le_mul_of_nonneg_left (neg_norm_le_controlValue P f m) hα]
    exact (EReal.coe_le_coe_iff.mpr hcv).trans
      (le_add_of_nonneg_right (EReal.coe_ennreal_nonneg _))
  · calc
      _ ≤ ((α*controlValue P f oneTrial : ℝ) : EReal) + (entropy oneTrial).toEReal :=
        iInf_le _ oneTrial
      _ ≤ ((α*‖f‖ : ℝ) : EReal) := by
        simp only [entropy_oneTrial, EReal.coe_ennreal_zero, add_zero]
        exact EReal.coe_le_coe_iff.mpr (mul_le_mul_of_nonneg_left (controlValue_le_norm P f _) hα)

lemma terminalVariational_coe_toReal (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f : ℝ →ᵇ ℝ) :
    ((terminalVariational P α f).toReal : EReal) = terminalVariational P α f := by
  obtain ⟨hlo,hhi⟩ := terminalVariational_bounds P α hα f
  exact EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top _) hhi)
    (ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo)

lemma terminalVariational_toReal_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f g : ℝ →ᵇ ℝ) (δ : ℝ)
    (hfg : ∀ m : Trial, controlValue P f m - controlValue P g m ≤ δ) :
    (terminalVariational P α f).toReal - (terminalVariational P α g).toReal ≤ α*δ := by
  have hbound : (((terminalVariational P α f).toReal - α*δ : ℝ) : EReal) ≤
      terminalVariational P α g := by
    apply le_iInf
    intro m
    have h : terminalVariational P α f ≤
        ((α*controlValue P f m : ℝ) : EReal) + (entropy m).toEReal := iInf_le _ m
    have hh : (((terminalVariational P α f).toReal - α*δ : ℝ) : EReal) ≤
        ((α*controlValue P f m - α*δ : ℝ) : EReal) + (entropy m).toEReal := by
      have hs := add_le_add_right h ((-α*δ : ℝ) : EReal)
      rw [← terminalVariational_coe_toReal P α hα f] at hs
      convert hs using 1 <;> simp only [sub_eq_add_neg, EReal.coe_add, EReal.coe_neg] <;>
        push_cast <;> simp only [neg_mul, add_assoc, add_comm]
    apply hh.trans
    apply add_le_add_left
    apply EReal.coe_le_coe_iff.mpr
    nlinarith [mul_le_mul_of_nonneg_left (hfg m) hα]
  rw [← terminalVariational_coe_toReal P α hα g, EReal.coe_le_coe_iff] at hbound
  linarith

lemma terminalVariational_abs_sub_le (P : Measure BrownianPath) [IsProbabilityMeasure P]
    (α : ℝ) (hα : 0 ≤ α) (f g : ℝ →ᵇ ℝ) (δ : ℝ)
    (hfg : ∀ m : Trial, |controlValue P f m - controlValue P g m| ≤ δ) :
    |(terminalVariational P α f).toReal - (terminalVariational P α g).toReal| ≤ α*δ := by
  have h₁ := terminalVariational_toReal_sub_le P α hα f g δ
    (fun m => (abs_le.mp (hfg m)).2)
  have h₂ := terminalVariational_toReal_sub_le P α hα g f δ
    (fun m => by have hh := (abs_le.mp (hfg m)).1; linarith)
  exact abs_le.mpr ⟨by linarith, h₁⟩

end SphericalPerceptron
end
end

end OAI
