import Mathlib
import OAI.Probability.CriticalPercolation.ProductMeasure.FiniteMarkovAvg

namespace OAI

section
section
open Set MeasureTheory ProbabilityTheory
open Set
open scoped BigOperators

namespace CriticalPercolation.FiniteMarkov
open Filter
open scoped Topology

variable {X : Type*} [Fintype X] [Preorder X]

def Associated (μ : X → ℝ) : Prop :=
  ∀ f g : X → ℝ, Monotone f → Monotone g →
    avg μ f * avg μ g ≤ avg μ (fun x => f x * g x)

omit [Preorder X] in
lemma avg_neg (μ : X → ℝ) (f : X → ℝ) :
    avg μ (fun x => -f x) = -avg μ f := by
  simp [avg, Finset.sum_neg_distrib]

lemma Associated.antitone {μ : X → ℝ} (h : Associated μ)
    (f g : X → ℝ) (hf : Antitone f) (hg : Antitone g) :
    avg μ f * avg μ g ≤ avg μ (fun x => f x * g x) := by
  have hh := h (fun x => -f x) (fun x => -g x) hf.neg hg.neg
  simpa only [avg_neg, neg_mul_neg] using hh

lemma Associated.cross {μ : X → ℝ} (h : Associated μ)
    (f g : X → ℝ) (hf : Monotone f) (hg : Antitone g) :
    avg μ (fun x => f x * g x) ≤ avg μ f * avg μ g := by
  have hh := h f (fun x => -g x) hf hg.neg
  simp only [avg_neg, mul_neg] at hh
  linarith

omit [Preorder X] in
lemma step_mono {K : X → X → ℝ} (hK : ∀ x y, 0 ≤ K x y)
    {f g : X → ℝ} (hfg : ∀ x, f x ≤ g x) (x : X) :
    step K f x ≤ step K g x := avg_mono (hK x) hfg

lemma association_halfstep {K L : X → X → ℝ}
    (hK : ∀ x y, 0 ≤ K x y)
    (hKa : ∀ x, Associated (K x)) (hLa : ∀ x, Associated (L x))
    (hLa' : ∀ f : X → ℝ, Monotone f → Antitone (step L f))
    (f g : X → ℝ) (hf : Monotone f) (hg : Monotone g) (x : X) :
    step K (step L f) x * step K (step L g) x ≤
      step K (step L (fun y => f y * g y)) x := by
  calc
    _ ≤ step K (fun y => step L f y * step L g y) x :=
      (hKa x).antitone _ _ (hLa' f hf) (hLa' g hg)
    _ ≤ _ := step_mono hK (fun y => hLa y f g hf hg) x

lemma step_antitone_of_neg {K : X → X → ℝ}
    (hK : ∀ f : X → ℝ, Monotone f → Antitone (step K f))
    {f : X → ℝ} (hf : Antitone f) : Monotone (step K f) := by
  have hh := (hK (fun x => -f x) hf.neg).neg
  change Monotone (fun x => avg (K x) f)
  simpa only [step, avg_neg, neg_neg] using hh

lemma iterate_association {K : X → X → ℝ}
    (hK : ∀ x y, 0 ≤ K x y)
    (hKa : ∀ x, Associated (K x))
    (hmono : ∀ f : X → ℝ, Monotone f → Monotone (step K f))
    (f g : X → ℝ) (hf : Monotone f) (hg : Monotone g) (n : ℕ) (x : X) :
    (step K)^[n] f x * (step K)^[n] g x ≤
      (step K)^[n] (fun y => f y * g y) x := by
  have hit (f : X → ℝ) (hf : Monotone f) (n : ℕ) : Monotone ((step K)^[n] f) := by
    induction n with
    | zero => exact hf
    | succ n ih => simpa only [Function.iterate_succ_apply'] using hmono _ ih
  induction n generalizing x with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    calc
      _ ≤ step K (fun y => (step K)^[n] f y * (step K)^[n] g y) x :=
        hKa x _ _ (hit f hf n) (hit g hg n)
      _ ≤ _ := step_mono hK (fun y => ih y) x

noncomputable def compose (K L : X → X → ℝ) (x z : X) : ℝ :=
  ∑ y, K x y * L y z

omit [Preorder X] in
lemma step_compose (K L : X → X → ℝ) (f : X → ℝ) :
    step (compose K L) f = step K (step L f) := by
  funext x
  simp only [step, avg, compose, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  exact Finset.sum_comm

omit [Preorder X] in
lemma compose_nonneg {K L : X → X → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hL : ∀ x y, 0 ≤ L x y) (x z : X) :
    0 ≤ compose K L x z := Finset.sum_nonneg fun y _ => mul_nonneg (hK x y) (hL y z)

omit [Preorder X] in
lemma compose_mass {K L : X → X → ℝ}
    (hK : ∀ x, ∑ y, K x y = 1) (hL : ∀ x, ∑ y, L x y = 1) (x : X) :
    ∑ z, compose K L x z = 1 := by
  simp only [compose]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, hL, mul_one, hK]

omit [Preorder X] in
lemma compose_minorization {K L : X → X → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hKm : ∀ x, ∑ y, K x y = 1)
    {a : ℝ} {z : X} (haL : ∀ x, a ≤ L x z) (x : X) :
    a ≤ compose K L x z := by
  calc
    a = ∑ y, K x y * a := by rw [← Finset.sum_mul, hKm, one_mul]
    _ ≤ _ := Finset.sum_le_sum fun y _ => mul_le_mul_of_nonneg_left (haL y) (hK x y)

lemma compose_associated {K L : X → X → ℝ}
    (hK : ∀ x y, 0 ≤ K x y)
    (hKa : ∀ x, Associated (K x)) (hLa : ∀ x, Associated (L x))
    (hLa' : ∀ f : X → ℝ, Monotone f → Antitone (step L f)) (x : X) :
    Associated (compose K L x) := by
  intro f g hf hg
  change step (compose K L) f x * step (compose K L) g x ≤
    step (compose K L) (fun y => f y * g y) x
  simp only [step_compose]
  exact association_halfstep hK hKa hLa hLa' f g hf hg x

lemma compose_monotone {K L : X → X → ℝ}
    (hKa' : ∀ f : X → ℝ, Monotone f → Antitone (step K f))
    (hLa' : ∀ f : X → ℝ, Monotone f → Antitone (step L f))
    {f : X → ℝ} (hf : Monotone f) : Monotone (step (compose K L) f) := by
  rw [step_compose]
  exact step_antitone_of_neg hKa' (hLa' f hf)

theorem stationary_associated {K : X → X → ℝ}
    (hK : ∀ x y, 0 ≤ K x y) (hmass : ∀ x, ∑ y, K x y = 1)
    (hKa : ∀ x, Associated (K x))
    (hmono : ∀ f : X → ℝ, Monotone f → Monotone (step K f))
    {a : ℝ} {z : X} (ha : 0 < a) (ha_one : a ≤ 1) (haK : ∀ x, a ≤ K x z)
    (μ : X → ℝ) (hμ : ∀ x, 0 ≤ μ x) (hμmass : ∑ x, μ x = 1)
    (hstat : ∀ y, ∑ x, μ x * K x y = μ y) : Associated μ := by
  intro f g hf hg
  have hf' := tendsto_iterate hK hmass ha ha_one haK μ hμ hμmass hstat f z
  have hg' := tendsto_iterate hK hmass ha ha_one haK μ hμ hμmass hstat g z
  have hfg' := tendsto_iterate hK hmass ha ha_one haK μ hμ hμmass hstat
    (fun x => f x * g x) z
  exact le_of_tendsto_of_tendsto (hf'.mul hg') hfg'
    (Filter.Eventually.of_forall fun n => iterate_association hK hKa hmono f g hf hg n z)

end CriticalPercolation.FiniteMarkov

end
end

end OAI
