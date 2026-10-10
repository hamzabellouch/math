import OAI.Probability.InvariantIsing.Core.FinitePushforwardEntropy
import OAI.Probability.InvariantIsing.Fields.SpinHammingBall

namespace OAI

/-! Entropy lost by a deterministic spin projection is controlled by its
expected Hamming distance. The estimate uses one finite conditional kernel,
so its constant does not depend on the depth of a Gaussian cascade. -/

noncomputable section
open scoped BigOperators

namespace InvariantIsing

lemma finitePushforwardWeights_pos_image {X Y : Type*} [Fintype X] [DecidableEq Y]
    (f : X → Y) (p : X → ℝ) (hp : ∀ x, 0 < p x) (x : X) :
    0 < finitePushforwardWeights f p (f x) :=
  (hp x).trans_le (finitePushforwardWeights_at_image f p (fun x => (hp x).le) x)

theorem finite_pushforward_entropy_bound {X Y : Type*}
    [Fintype X] [Fintype Y] [DecidableEq Y]
    (f : X → Y) (p C : X → ℝ) (hp : ∀ x, 0 < p x) (hpSum : ∑ x, p x = 1)
    (Z : ℝ) (hZ : 0 < Z)
    (hkernel : ∀ y, (∑ x ∈ Finset.univ.filter (fun x => f x = y),
      Real.exp (-C x)) ≤ Z) :
    finiteShannonEntropy p - finiteShannonEntropy (finitePushforwardWeights f p) ≤
      (∑ x, p x * C x) + Real.log Z := by
  let q := finitePushforwardWeights f p
  let r := fun x => q (f x) * Real.exp (-C x) / Z
  have hq (y : Y) : 0 ≤ q y :=
    finitePushforwardWeights_nonneg f p (fun x => (hp x).le) y
  have hqi (x : X) : 0 < q (f x) := finitePushforwardWeights_pos_image f p hp x
  have hr (x : X) : 0 < r x := div_pos (mul_pos (hqi x) (Real.exp_pos _)) hZ
  have hrSum : ∑ x, r x ≤ 1 := by
    rw [← Finset.sum_fiberwise Finset.univ f r]
    calc
      _ = ∑ y, q y / Z *
          (∑ x ∈ Finset.univ.filter (fun x => f x = y), Real.exp (-C x)) := by
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x hx
        dsimp only [r]
        rw [(Finset.mem_filter.mp hx).2]
        ring
      _ ≤ ∑ y, q y / Z * Z := Finset.sum_le_sum (fun y _ =>
        mul_le_mul_of_nonneg_left (hkernel y) (div_nonneg (hq y) hZ.le))
      _ = 1 := by
        simp only [div_mul_cancel₀ _ hZ.ne']
        exact (finitePushforwardWeights_sum f p).trans hpSum
  have hk := finite_relativeEntropy_nonneg_of_sum_le p r
    (fun x => (hp x).le) hpSum hr hrSum
  have hlog (x : X) : Real.log (r x) = Real.log (q (f x)) - C x - Real.log Z := by
    dsimp only [r]
    rw [Real.log_div (mul_ne_zero (hqi x).ne' (Real.exp_ne_zero _)) hZ.ne',
      Real.log_mul (hqi x).ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hi (x : X) : p x * Real.log (p x / r x) =
      p x * Real.log (p x) - p x * Real.log (q (f x)) +
        p x * C x + p x * Real.log Z := by
    rw [Real.log_div (hp x).ne' (hr x).ne', hlog]
    ring
  simp_rw [hi] at hk
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, hpSum, one_mul] at hk
  rw [finiteShannonEntropy, finitePushforwardWeights_entropy]
  change -(∑ x, p x * Real.log (p x)) - (-(∑ x, p x * Real.log (q (f x)))) ≤ _
  linarith

theorem spin_projection_entropy_bound {N : ℕ} (f : Spin N → Spin N)
    (p : Spin N → ℝ) (hp : ∀ σ, 0 < p σ) (hpSum : ∑ σ, p σ = 1) (t : ℝ) :
    finiteShannonEntropy p - finiteShannonEntropy (finitePushforwardWeights f p) ≤
      t * (∑ σ, p σ * (hammingDist σ (f σ) : ℝ)) +
        N * Real.log (1 + Real.exp (-t)) := by
  have hZ : 0 < (1 + Real.exp (-t)) ^ N := by positivity
  have hkernel (τ : Spin N) :
      (∑ σ ∈ Finset.univ.filter (fun σ => f σ = τ),
        Real.exp (-(t * (hammingDist σ (f σ) : ℝ)))) ≤
          (1 + Real.exp (-t)) ^ N := by
    calc
      _ = ∑ σ ∈ Finset.univ.filter (fun σ => f σ = τ),
          Real.exp (-t * (hammingDist σ τ : ℝ)) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        rw [(Finset.mem_filter.mp hσ).2]
        congr 1
        ring
      _ ≤ ∑ σ : Spin N, Real.exp (-t * (hammingDist σ τ : ℝ)) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun σ _ _ => (Real.exp_pos _).le)
      _ = _ := sum_exp_hamming τ t
  have he := finite_pushforward_entropy_bound f p
    (fun σ => t * (hammingDist σ (f σ) : ℝ)) hp hpSum _ hZ hkernel
  rw [Real.log_pow] at he
  calc
    _ ≤ (∑ σ, p σ * (t * (hammingDist σ (f σ) : ℝ))) +
        N * Real.log (1 + Real.exp (-t)) := he
    _ = _ := by rw [Finset.mul_sum]; congr 1; apply Finset.sum_congr rfl; intros; ring

end InvariantIsing

end

end OAI
