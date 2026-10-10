import OAI.MeasureTheory.Falconer.Geometry.ConditionalBalls
import OAI.MeasureTheory.Falconer.Incidence.TroublesomeIncidence

namespace OAI

/-! # Weak radial incidence for the actual conditional regularized class laws -/

namespace Falconer.Regularization
open Set Metric MeasureTheory
open scoped ENNReal
variable {n : ℕ}

noncomputable def radialClassBallBound (Q : DyadicCube (n+1))
    (μ : Measure (Space (n+1))) (N B : ℕ) (p : CellPath (n+1))
    (a b : ℕ) (lam : ℝ) : ℝ :=
  ((2*Nat.ceil (2*((n+1:ℕ):ℝ)^2+2+4*Real.sqrt (n+1:ℕ))+1)^(n+1):ℕ)*
    ((2:ℝ)^N)^(sourceProfile Q μ N B p a-sourceProfile Q μ N B p b+
      2*(((n+1:ℕ):ℝ)+1)*lam)

theorem regular_class_radial_incidence (hLW : PublishedFiniteLoomisWhitney) (hn : 1 ≤ n)
    (Q : DyadicCube (n+1)) (hQ : 0 < Q.side)
    (μ ν : Measure (Space (n+1))) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {N B : ℕ} (hN : 0 < N) (hB : 0 < B) {lam : ℝ}
    (hwidth : (B:ℝ) ≤ lam*(N:ℝ)) (hlarge : (2:ℝ)^(N/B+2) ≤ ((2:ℝ)^N)^lam)
    {p₀ : CellPath (n+1)} (hp₀ : p₀ ∈ regularizationLeaves Q μ N)
    {a b : ℕ} (haN : a ≤ N) (hbN : b ≤ N)
    {p : CellPath (n+1)} (hp : p.length = a)
    (hpos : 0 < sourceClass Q μ N B p₀ (Q.descendant p).carrier)
    {r C Bs F α R t : ℝ} (hr : 0 < r) (hF : 0 < F) (hα : 0 < α) (hα1 : α ≤ 1)
    (hfreeze : 8*(Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^a))^2/r ≤ Q.side/(2:ℝ)^b)
    (hR : ∀ᵐ x ∂ν, ‖(Q.descendant p).center-x‖ ≤ R)
    (K : ℝ≥0∞) (hslab : ∀ u : Space (n+1), ‖u‖ = 1 →
      ν {x | |inner ℝ u x-inner ℝ u (Q.descendant p).center| ≤ R*α} ≤ K)
    (L : ℕ) (hL : C+1+((n+1:ℕ):ℝ)+1/2 ≤ (L:ℝ)) (ht : 0 ≤ t)
    (hbudget : (((2*L+1)^(n+1):ℕ)/F)^(n+1)*
      (generalTubeCountConstant (n+1) ((n+1:ℕ):ℝ)/α^(n+1))^(n*(n+1))*
        (radialClassBallBound Q μ N B p₀ a b lam)^n ≤ t^n) :
    (((ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant p).carrier).prod ν)
      (troublesomePair (ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant p).carrier)
        (Q.descendant p).center r (Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^a)) Bs
          (C*(Q.side/(2:ℝ)^b)) (ENNReal.ofReal F)))^(n+1) ≤
      ENNReal.ofReal t+(n+1:ℝ≥0∞)*K := by
  let ρ := ProbabilityTheory.cond (sourceClass Q μ N B p₀) (Q.descendant p).carrier
  have : IsProbabilityMeasure ρ := sourceClass_conditional_probability Q hQ μ N B hp₀ p hpos
  have hδ : 0 < Q.side/(2:ℝ)^b := by positivity
  have hsrc : ∀ᵐ y ∂ρ, ‖y-(Q.descendant p).center‖ ≤
      Real.sqrt (n+1:ℕ)*(Q.side/(2:ℝ)^a) := by
    apply ProbabilityTheory.ae_cond_of_forall_mem (Q.descendant p).measurable
    intro y hy
    have hd := (Q.descendant p).dist_le (Q.descendant_side_pos hQ p).le hy
      ((Q.descendant p).center_mem (Q.descendant_side_pos hQ p))
    simpa only [dist_eq_norm,Q.descendant_side,hp] using hd
  have hH : 0 ≤ radialClassBallBound Q μ N B p₀ a b lam := by
    unfold radialClassBallBound
    positivity
  apply troublesome_pair_incidence_bound hLW hn ρ ν (Q.descendant p).center
    hr hδ hF hα hα1 hfreeze hsrc hR K hslab L hL hH ht _ hbudget
  intro x
  have hb := sourceClass_conditional_ball_upper Q hQ μ hN hB hwidth hlarge hp₀
    haN hbN hp hpos x (C := ((n+1:ℕ):ℝ)^2+1) (by positivity)
  have he : 2*(((n+1:ℕ):ℝ)^2+1)+4*Real.sqrt (n+1:ℕ) =
      2*((n+1:ℕ):ℝ)^2+2+4*Real.sqrt (n+1:ℕ) := by ring
  rw [he] at hb
  change (ρ (ball x ((((n+1:ℕ):ℝ)^2+1)*(Q.side/(2:ℝ)^b)))).toReal ≤
    radialClassBallBound Q μ N B p₀ a b lam at hb
  rw [← ENNReal.ofReal_toReal (measure_ne_top ρ _)]
  exact ENNReal.ofReal_le_ofReal hb

end Falconer.Regularization

end OAI
