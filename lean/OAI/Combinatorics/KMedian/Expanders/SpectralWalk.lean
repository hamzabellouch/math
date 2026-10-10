import Mathlib
import OAI.Combinatorics.KMedian.Expanders.PortWalk
import OAI.Combinatorics.KMedian.PCP.FiniteTest

namespace OAI

section Inline_PCPSpectralWalk

namespace MetricKMedian.PCP
open Finset
open scoped BigOperators

section FiniteEnergy
variable {S T : Type} [Fintype S] [Fintype T]

theorem expect_prod (f : S × T → ℝ) :
    (𝔼 p, f p) = 𝔼 s, 𝔼 t, f (s,t) := by
  rw [← univ_product_univ, expect_product]

noncomputable def energy (f : S → ℝ) : ℝ := 𝔼 s, f s ^ 2
noncomputable def pairing (f g : S → ℝ) : ℝ := 𝔼 s, f s * g s

theorem energy_nonneg (f : S → ℝ) : 0 ≤ energy f :=
  expect_nonneg (fun _ _ => sq_nonneg _)

theorem pairing_sq_le (f g : S → ℝ) : pairing f g ^ 2 ≤ energy f * energy g :=
  expect_mul_sq_le_sq_mul_sq _ _ _

theorem energy_center [Nonempty S] (f : S → ℝ) :
    energy (fun s => f s - 𝔼 t, f t) = energy f - (𝔼 t, f t)^2 := by
  unfold energy
  simp_rw [sub_sq]
  rw [expect_add_distrib, expect_sub_distrib]
  simp only [← expect_mul, ← mul_expect, Fintype.expect_const]
  ring

theorem mean_center [Nonempty S] (f : S → ℝ) :
    (𝔼 s, (f s - 𝔼 t, f t)) = 0 := by
  rw [expect_sub_distrib, Fintype.expect_const, sub_self]

theorem energy_indicator_le (p : S → Prop) :
    energy (fun s => @ite ℝ (p s) (Classical.propDecidable _) 1 0) ≤ testRate p := by
  classical
  unfold energy testRate
  apply expect_le_expect
  intro s _
  by_cases h : p s <;> simp [h]

end FiniteEnergy

namespace PortGraph
variable {V D : Type} [Fintype V] [Fintype D] [Nonempty D]
variable (G : PortGraph V D)

noncomputable def adjacency (f : V → ℝ) (v : V) : ℝ := 𝔼 d, f (G.step v d)

omit [Fintype V] in
theorem adjacency_const (a : ℝ) : G.adjacency (fun _ => a) = fun _ => a := by
  funext v
  exact Fintype.expect_const a

omit [Fintype V] [Nonempty D] in
theorem adjacency_add (f g : V → ℝ) :
    G.adjacency (fun v => f v + g v) = fun v => G.adjacency f v + G.adjacency g v := by
  funext v
  exact expect_add_distrib _ _ _

omit [Fintype V] [Nonempty D] in
theorem adjacency_sub (f g : V → ℝ) :
    G.adjacency (fun v => f v - g v) = fun v => G.adjacency f v - G.adjacency g v := by
  funext v
  exact expect_sub_distrib _ _ _

theorem adjacency_mean (f : V → ℝ) : (𝔼 v, G.adjacency f v) = 𝔼 v, f v := by
  change (𝔼 v, 𝔼 d, f (G.step v d)) = _
  rw [← expect_prod (fun p : V × D => f (G.step p.1 p.2))]
  have h := Fintype.expect_equiv G.rotate
    (fun p : V × D => f (G.step p.1 p.2)) (fun p : V × D => f p.1)
    (fun _ => rfl)
  rw [h, expect_prod]
  simp only [Fintype.expect_const]

omit [Nonempty D] in
theorem adjacency_selfAdjoint (f g : V → ℝ) :
    pairing f (G.adjacency g) = pairing (G.adjacency f) g := by
  unfold pairing adjacency
  simp_rw [mul_expect, expect_mul]
  rw [← expect_prod (fun p : V × D => f p.1 * g (G.step p.1 p.2)),
    ← expect_prod (fun p : V × D => f (G.step p.1 p.2) * g p.1)]
  apply Fintype.expect_equiv G.rotate
  intro p
  change f p.1 * g (G.step p.1 p.2) =
    f (G.step (G.step p.1 p.2) (G.back p.1 p.2)) * g (G.step p.1 p.2)
  rw [step_back]

def Contracts (ρ : ℝ) : Prop :=
  ∀ f : V → ℝ, (𝔼 v, f v) = 0 → energy (G.adjacency f) ≤ ρ^2 * energy f

noncomputable def propagate : ℕ → (V → ℝ) → V → ℝ
  | 0, f => f
  | n+1, f => G.adjacency (propagate n f)

omit [Fintype V] [Nonempty D] in
@[simp] theorem propagate_zero (f : V → ℝ) : G.propagate 0 f = f := rfl
omit [Fintype V] [Nonempty D] in
@[simp] theorem propagate_succ (n : ℕ) (f : V → ℝ) :
    G.propagate (n+1) f = G.adjacency (G.propagate n f) := rfl

theorem propagate_mean (n : ℕ) (f : V → ℝ) :
    (𝔼 v, G.propagate n f v) = 𝔼 v, f v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [propagate_succ, adjacency_mean, ih]

theorem propagate_contract {ρ : ℝ} (hG : G.Contracts ρ) (n : ℕ)
    (f : V → ℝ) (hf : (𝔼 v, f v) = 0) :
    energy (G.propagate n f) ≤ ρ^(2*n) * energy f := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      energy (G.propagate (n+1) f) ≤ ρ^2 * energy (G.propagate n f) :=
        hG _ ((G.propagate_mean n f).trans hf)
      _ ≤ ρ^2 * (ρ^(2*n) * energy f) := mul_le_mul_of_nonneg_left ih (sq_nonneg _)
      _ = ρ^(2*(n+1)) * energy f := by rw [show 2*(n+1)=2+2*n by omega, pow_add]; ring

theorem correlation_sq {ρ : ℝ} (hG : G.Contracts ρ) (n : ℕ)
    (f g : V → ℝ) (hg : (𝔼 v, g v) = 0) :
    pairing f (G.propagate n g)^2 ≤ ρ^(2*n) * energy f * energy g := by
  calc
    _ ≤ energy f * energy (G.propagate n g) := pairing_sq_le _ _
    _ ≤ energy f * (ρ^(2*n) * energy g) :=
      mul_le_mul_of_nonneg_left (G.propagate_contract hG n g hg) (energy_nonneg f)
    _ = _ := by ring

omit [Fintype V] in
theorem propagate_const (n : ℕ) (a : ℝ) : G.propagate n (fun _ => a) = fun _ => a := by
  induction n with
  | zero => rfl
  | succ n ih => rw [propagate_succ, ih, adjacency_const]

omit [Fintype V] [Nonempty D] in
theorem propagate_sub (n : ℕ) (f g : V → ℝ) :
    G.propagate n (fun v => f v - g v) = fun v => G.propagate n f v - G.propagate n g v := by
  induction n with
  | zero => rfl
  | succ n ih => rw [propagate_succ, ih, adjacency_sub]; rfl

theorem centered_correlation [Nonempty V] (n : ℕ) (f : V → ℝ) :
    pairing (fun v => f v - 𝔼 w, f w) (G.propagate n (fun v => f v - 𝔼 w, f w)) =
      pairing f (G.propagate n f) - (𝔼 v, f v)^2 := by
  rw [G.propagate_sub, G.propagate_const]
  unfold pairing
  have h : ∀ v, (f v - 𝔼 w, f w) * (G.propagate n f v - 𝔼 w, f w) =
      f v * G.propagate n f v - (𝔼 w, f w) * G.propagate n f v -
      f v * (𝔼 w, f w) + (𝔼 w, f w)^2 := by intro v; ring
  simp_rw [h]
  rw [expect_add_distrib, expect_sub_distrib, expect_sub_distrib]
  simp only [← expect_mul, ← mul_expect, Fintype.expect_const, propagate_mean]
  ring

theorem bounded_correlation [Nonempty V] {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hG : G.Contracts ρ) (n : ℕ) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v ∧ f v ≤ 1) :
    pairing f (G.propagate n f) ≤ (𝔼 v, f v)^2 + ρ^n * (𝔼 v, f v) := by
  let μ : ℝ := 𝔼 v, f v
  let g : V → ℝ := fun v => f v - μ
  have hμ : 0 ≤ μ := expect_nonneg (fun v _ => (hf v).1)
  have hEg : energy g ≤ μ := by
    rw [show energy g = energy f - μ^2 from energy_center f]
    have hEf : energy f ≤ μ := by
      apply expect_le_expect
      intro v _
      nlinarith [(hf v).1, (hf v).2]
    linarith [sq_nonneg μ]
  have hEg0 := energy_nonneg g
  have hpair := G.correlation_sq hG n g g (mean_center f)
  have hbound : pairing g (G.propagate n g)^2 ≤ (ρ^n * μ)^2 := by
    calc
      _ ≤ ρ^(2*n) * energy g * energy g := hpair
      _ ≤ ρ^(2*n) * μ * μ := by gcongr
      _ = (ρ^n * μ)^2 := by rw [show 2*n=n*2 by omega, pow_mul]; ring
  have hh := le_of_sq_le_sq hbound (mul_nonneg (pow_nonneg hρ n) hμ)
  have hc := G.centered_correlation n f
  change pairing g (G.propagate n g) = pairing f (G.propagate n f) - μ^2 at hc
  linarith

end PortGraph
end MetricKMedian.PCP

end Inline_PCPSpectralWalk

end OAI
