import Mathlib

namespace OAI

section
section
noncomputable section
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

section LowerProof
open Matrix Topology TopologicalSpace ProbabilityTheory Classical WithLp
open scoped Matrix.Norms.Elementwise
open MeasureTheory ProbabilityTheory

namespace LogConcaveSampling

lemma map_prod_eq_of_conditional_law {S A B C : Type*}
    [MeasurableSpace S] [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    {μ : Measure S} {ν : Measure A} {η : Measure B}
    [SFinite μ] [SFinite ν] [SFinite η]
    {f : S × A → C} {g : S × B → C}
    (hf : Measurable f) (hg : Measurable g)
    (h : ∀ s, ν.map (fun a => f (s,a)) = η.map (fun b => g (s,b))) :
    (μ.prod ν).map f = (μ.prod η).map g := by
  ext t ht
  rw [Measure.map_apply hf ht, Measure.map_apply hg ht,
    Measure.prod_apply (ht.preimage hf), Measure.prod_apply (ht.preimage hg)]
  apply lintegral_congr
  intro s
  have hs := congrArg (fun κ : Measure C => κ t) (h s)
  rw [Measure.map_apply (f := fun a => f (s,a)) (by fun_prop) ht,
    Measure.map_apply (f := fun b => g (s,b)) (by fun_prop) ht] at hs
  exact hs

theorem eliminate_fresh_residual {S T R H C : Type*}
    [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace R]
    [MeasurableSpace H] [MeasurableSpace C]
    {μ : Measure S} {γ : Measure R} {η η' : Measure H}
    [SFinite μ] [SFinite γ] [SFinite η] [SFinite η']
    {step : S × R → T} {f : T × H → C} {g : S × H → C}
    (hstep : Measurable step) (hf : Measurable f) (hg : Measurable g)
    (h : ∀ s, (γ.prod η').map (fun p => f (step (s,p.1),p.2)) =
      η.map (fun h => g (s,h))) :
    (((μ.prod γ).map step).prod η').map f = (μ.prod η).map g := by
  have hp := Measure.map_prod_map (μ.prod γ) η' hstep measurable_id
  rw [Measure.map_id] at hp
  rw [hp, Measure.map_map hf (by fun_prop)]
  have ha := Measure.prodAssoc_prod (μ := μ) (ν := γ) (τ := η')
  calc
    _ = (μ.prod (γ.prod η')).map (fun p => f (step (p.1,p.2.1),p.2.2)) := by
      rw [← ha, Measure.map_map (by fun_prop) MeasurableEquiv.prodAssoc.measurable]
      rfl
    _ = _ := map_prod_eq_of_conditional_law (by fun_prop) hg h

section Iteration
variable {S : ℕ → Type*} {R H C : Type*}
    [∀ n, MeasurableSpace (S n)] [MeasurableSpace R] [MeasurableSpace H] [MeasurableSpace C]

def stateLaw (μ : Measure (S 0)) (γ : Measure R)
    (step : (n : ℕ) → S n × R → S (n+1)) : (n : ℕ) → Measure (S n)
  | 0 => μ
  | n+1 => ((stateLaw μ γ step n).prod γ).map (step n)

lemma stateLaw_probability (μ : Measure (S 0)) (γ : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (step : (n : ℕ) → S n × R → S (n+1)) (hstep : ∀ n, Measurable (step n)) (n : ℕ) :
    IsProbabilityMeasure (stateLaw μ γ step n) := by
  induction n with
  | zero => exact inferInstanceAs (IsProbabilityMeasure μ)
  | succ n ih =>
    have := ih
    exact (Measure.isProbabilityMeasure_map_iff (hstep n).aemeasurable).mpr inferInstance

theorem stateLaw_completion (μ : Measure (S 0)) (γ : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (step : (n : ℕ) → S n × R → S (n+1)) (hstep : ∀ n, Measurable (step n))
    (η : ℕ → Measure H) [∀ n, IsProbabilityMeasure (η n)]
    (f : (n : ℕ) → S n × H → C) (hf : ∀ n, Measurable (f n))
    (N : ℕ)
    (hlocal : ∀ n < N, ∀ s : S n,
      (γ.prod (η (n+1))).map (fun p => f (n+1) (step n (s,p.1),p.2)) =
        (η n).map (fun h => f n (s,h))) :
    ((stateLaw μ γ step N).prod (η N)).map (f N) = (μ.prod (η 0)).map (f 0) := by
  have hprob (j : ℕ) := stateLaw_probability μ γ step hstep j
  have h : ∀ n ≤ N, ((stateLaw μ γ step n).prod (η n)).map (f n) =
      (μ.prod (η 0)).map (f 0) := by
    intro n hn
    induction n with
    | zero => rfl
    | succ n ih =>
      change ((((stateLaw μ γ step n).prod γ).map (step n)).prod (η (n+1))).map
        (f (n+1)) = _
      rw [eliminate_fresh_residual (hstep n) (hf (n+1)) (hf n) (hlocal n (by omega))]
      exact ih (by omega)
  exact h N le_rfl

theorem stateLaw_map {T : ℕ → Type*} [∀ n, MeasurableSpace (T n)]
    (μ : Measure (S 0)) (γ : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure γ]
    (step : (n : ℕ) → S n × R → S (n+1)) (hstep : ∀ n, Measurable (step n))
    (step' : (n : ℕ) → T n × R → T (n+1)) (hstep' : ∀ n, Measurable (step' n))
    (p : (n : ℕ) → S n → T n) (hp : ∀ n, Measurable (p n))
    (hcomm : ∀ n s r, p (n+1) (step n (s,r)) = step' n (p n s,r)) (n : ℕ) :
    (stateLaw μ γ step n).map (p n) = stateLaw (μ.map (p 0)) γ step' n := by
  have hprob (j : ℕ) := stateLaw_probability μ γ step hstep j
  induction n with
  | zero => rfl
  | succ n ih =>
    change (((stateLaw μ γ step n).prod γ).map (step n)).map (p (n+1)) = _
    rw [Measure.map_map (hp (n+1)) (hstep n)]
    change _ = ((stateLaw (μ.map (p 0)) γ step' n).prod γ).map (step' n)
    rw [← ih]
    have hpr := Measure.map_prod_map (stateLaw μ γ step n) γ (hp n) measurable_id
    rw [Measure.map_id] at hpr
    rw [hpr, Measure.map_map (hstep' n) (by fun_prop)]
    congr 1
    funext z
    exact hcomm n z.1 z.2

end Iteration
end LogConcaveSampling

end LowerProof
end
end
end

end OAI
