import OAI.NumberTheory.DirichletL.Descent.TripleMass
import OAI.NumberTheory.DirichletL.Descent.Canonical

namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open SevenEighths.InverseSecondFibers IdealMobiusDivisorSum CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondLabelEnergy (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : ℝ :=
  ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(9+4*K) *
    ∑ k ∈ rows, ‖F (γ,f,k)‖^2

lemma secondLabelEnergy_nonneg (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : 0 ≤ secondLabelEnergy K labels rows F γ := by
  unfold secondLabelEnergy; positivity

theorem second_weighted_count {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild x).2.1 ∈ labels ∧ (secondChild x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℂ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ originalSource source oldLists newLists keep,
      w x * F (secondChild x) * star (G (secondChild x))‖ ≤
      Real.sqrt (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  have hF := second_energy_projection source oldLists newLists keep hvalid labels rows hf houter hchild
    K ho hn (fun x => ‖w x‖) hw F
  have hG := second_energy_projection source oldLists newLists keep hvalid labels rows hf houter hchild
    K ho hn (fun x => ‖w x‖) hw G
  apply (DescentWeightedCauchy.weighted_cauchy (originalSource source oldLists newLists keep)
    w (F ∘ secondChild) (G ∘ secondChild)).trans
  exact mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem second_weighted_count_of_child_bound {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild x).2.1 ∈ labels ∧ (secondChild x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℂ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows F γ ≤ E)
    (hG : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows G γ ≤ E) :
    ‖∑ x ∈ originalSource source oldLists newLists keep,
      w x * F (secondChild x) * star (G (secondChild x))‖ ≤
      E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ := by
  have hb (P : SecondChild → ℂ)
      (hP : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows P γ ≤ E) :
      (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows P γ) ≤
      E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ hγ
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hP γ hγ) (tripleDivisorWeight_nonneg K γ)
  apply (second_weighted_count source oldLists newLists keep hvalid labels rows hf houter hchild K ho hn w hw F G).trans
  calc
    _ ≤ Real.sqrt (E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ) *
      Real.sqrt (E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ) :=
      mul_le_mul (Real.sqrt_le_sqrt (hb F hF)) (Real.sqrt_le_sqrt (hb G hG))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (mul_nonneg hE (Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ)))

def secondCanonicalPolynomial {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : OuterTriple → Eis →* ℂ) (puncture : OuterTriple → Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) : ℂ :=
  finiteCanonicalMarkedRow p hp hcop hg pool (Ψ c.1) (puncture c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a (W c.1) X

theorem secondCanonicalPolynomial_actual_columns {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : OuterTriple → Eis →* ℂ) (puncture : OuterTriple → Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) :
    secondCanonicalPolynomial p hp hcop hg pool Ψ puncture slots lists a W X c =
      ∑ U ∈ pool.powerset,
        columnWeight (CanonicalRowCompletion.rowTwist (Ψ c.1) (puncture c.1)
          (primaryGenerator c.2.1) c.2.2) (Ideal.span {∏ i ∈ U, p i}) *
        (primeMark slots lists a U * W c.1 (FirstPassCubeLabels.primeProductNorm p U / X)) :=
  finiteCanonicalMarkedRow_actual_columns p hp hcop hg hpr pool (Ψ c.1) (puncture c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a (W c.1) X

end
end SevenEighths.InverseMoment

end OAI
