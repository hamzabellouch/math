import OAI.Probability.InvariantIsing.Fields.CascadeSeedPath

namespace OAI

/-! Finite two-path recursion for the ancestor-dependent uniform seeds. -/
noncomputable section
open MeasureTheory ProbabilityTheory IsingPerceptron
namespace InvariantIsing
variable {ι : Type}

def seedPairPathMean : (n : ℕ) → (ℕ → (ι → ℝ) → unitInterval → (ι → ℝ)) →
    ℕ → (ι → ℝ) → (ι → ℝ) → ((Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ) → ℝ
  | 0, _, _, _, _, F => F Fin.elim0
  | n+1, ψ, 0, z₁, z₂, F =>
      ∫ u : unitInterval × unitInterval,
        seedPairPathMean n (fun i => ψ (i+1)) 0
          (z₁+ψ 0 z₁ u.1) (z₂+ψ 0 z₂ u.2)
          (fun w => F (Fin.cons (ψ 0 z₁ u.1,ψ 0 z₂ u.2) w)) ∂volume.prod volume
  | n+1, ψ, d+1, z₁, z₂, F =>
      ∫ u : unitInterval,
        seedPairPathMean n (fun i => ψ (i+1)) d
          (z₁+ψ 0 z₁ u) (z₂+ψ 0 z₂ u)
          (fun w => F (Fin.cons (ψ 0 z₁ u,ψ 0 z₂ u) w))

lemma measurable_finCons {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {n : ℕ} {a : X → Y} {w : X → Fin n → Y} (ha : Measurable a) (hw : Measurable w) :
    Measurable (fun x => (Fin.cons (a x) (w x) : Fin (n+1) → Y)) := by
  apply Measurable.of_eval
  intro i
  exact Fin.cases ha (fun j => (measurable_pi_apply j).comp hw) i

lemma measurable_seedPairPathMean (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ))
    (hψ : ∀ i, Measurable (Function.uncurry (ψ i))) (d : ℕ)
    {X : Type*} [MeasurableSpace X] (z₁ z₂ : X → (ι → ℝ))
    (h₁ : Measurable z₁) (h₂ : Measurable z₂)
    (F : X → (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ)
    (hF : Measurable (Function.uncurry F)) :
    Measurable (fun x => seedPairPathMean n ψ d (z₁ x) (z₂ x) (F x)) := by
  induction n generalizing X ψ d with
  | zero => exact hF.comp (measurable_id.prodMk measurable_const)
  | succ n ih =>
    cases d with
    | zero =>
      have hA : Measurable (fun p : X × (unitInterval × unitInterval) => ψ 0 (z₁ p.1) p.2.1) :=
        (hψ 0).comp ((h₁.comp measurable_fst).prodMk measurable_snd.fst)
      have hB : Measurable (fun p : X × (unitInterval × unitInterval) => ψ 0 (z₂ p.1) p.2.2) :=
        (hψ 0).comp ((h₂.comp measurable_fst).prodMk measurable_snd.snd)
      have hC : Measurable (fun p : (X × (unitInterval × unitInterval)) ×
          (Fin n → (ι → ℝ) × (ι → ℝ)) =>
          F p.1.1 (Fin.cons (ψ 0 (z₁ p.1.1) p.1.2.1,ψ 0 (z₂ p.1.1) p.1.2.2) p.2)) :=
        hF.comp (measurable_fst.fst.prodMk
          (measurable_finCons ((hA.comp measurable_fst).prodMk (hB.comp measurable_fst)) measurable_snd))
      exact (ih (fun i => ψ (i+1)) (fun i => hψ (i+1)) 0
        (fun p : X × (unitInterval × unitInterval) => z₁ p.1+ψ 0 (z₁ p.1) p.2.1)
        (fun p => z₂ p.1+ψ 0 (z₂ p.1) p.2.2)
        ((h₁.comp measurable_fst).add hA) ((h₂.comp measurable_fst).add hB)
        (fun p w => F p.1 (Fin.cons (ψ 0 (z₁ p.1) p.2.1,ψ 0 (z₂ p.1) p.2.2) w)) hC
        ).stronglyMeasurable.integral_prod_right.measurable
    | succ d =>
      have hA : Measurable (fun p : X × unitInterval => ψ 0 (z₁ p.1) p.2) :=
        (hψ 0).comp ((h₁.comp measurable_fst).prodMk measurable_snd)
      have hB : Measurable (fun p : X × unitInterval => ψ 0 (z₂ p.1) p.2) :=
        (hψ 0).comp ((h₂.comp measurable_fst).prodMk measurable_snd)
      have hC : Measurable (fun p : (X × unitInterval) ×
          (Fin n → (ι → ℝ) × (ι → ℝ)) =>
          F p.1.1 (Fin.cons (ψ 0 (z₁ p.1.1) p.1.2,ψ 0 (z₂ p.1.1) p.1.2) p.2)) :=
        hF.comp (measurable_fst.fst.prodMk
          (measurable_finCons ((hA.comp measurable_fst).prodMk (hB.comp measurable_fst)) measurable_snd))
      exact (ih (fun i => ψ (i+1)) (fun i => hψ (i+1)) d
        (fun p : X × unitInterval => z₁ p.1+ψ 0 (z₁ p.1) p.2)
        (fun p => z₂ p.1+ψ 0 (z₂ p.1) p.2)
        ((h₁.comp measurable_fst).add hA) ((h₂.comp measurable_fst).add hB)
        (fun p w => F p.1 (Fin.cons (ψ 0 (z₁ p.1) p.2,ψ 0 (z₂ p.1) p.2) w)) hC
        ).stronglyMeasurable.integral_prod_right.measurable

private lemma seed_abs_integral_bound {A : Type*} [MeasurableSpace A]
    {μ : Measure A} [IsProbabilityMeasure μ] (f : A → ℝ) {C : ℝ}
    (hf : ∀ a, |f a| ≤ C) : |∫ a, f a ∂μ| ≤ C := by
  have hh : ∀ᵐ a ∂μ, ‖f a‖ ≤ C := ae_of_all _ fun a => by
    simpa only [Real.norm_eq_abs] using hf a
  simpa only [Real.norm_eq_abs, probReal_univ, mul_one] using
    norm_integral_le_of_norm_le_const (μ := μ) (f := f) hh

lemma seedPairPathMean_abs_le (n : ℕ)
    (ψ : ℕ → (ι → ℝ) → unitInterval → (ι → ℝ)) (d : ℕ) (z₁ z₂ : ι → ℝ)
    (F : (Fin n → (ι → ℝ) × (ι → ℝ)) → ℝ) {C : ℝ} (hF : ∀ w, |F w| ≤ C) :
    |seedPairPathMean n ψ d z₁ z₂ F| ≤ C := by
  induction n generalizing ψ d z₁ z₂ with
  | zero => exact hF _
  | succ n ih =>
    cases d <;> simp only [seedPairPathMean]
    all_goals
      apply seed_abs_integral_bound
      intro u
      exact ih _ _ _ _ _ (fun w => hF _)

end InvariantIsing

end

end OAI
