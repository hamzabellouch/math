import OAI.Combinatorics.Progressions.Probability.ObservedProductDensity

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residue_cell_pair_cancellation {A B R : Type*} [Fintype A] [Fintype B]
    [Fintype R] [Nonempty R] (p : FiniteProbabilityWeights A) (q : FiniteProbabilityWeights B)
    (e : A → R → ℝ) (d : B → R → ℝ) (Phi : A → B → R → ℝ)
    {delta gamma L : ℝ} (hdelta : 0 ≤ delta) (hL : 0 ≤ L)
    (he : ∀ a r, |e a r| ≤ delta / Fintype.card R)
    (hd : ∀ b r, |d b r| ≤ gamma / Fintype.card R)
    (hPhi : ∀ a b r, |Phi a b r| ≤ L) :
    |(Fintype.card R : ℝ) * ∑ r, p.mean (fun a => q.mean (fun b => Phi a b r * e a r * d b r))| ≤
      L * delta * gamma := by
  let K : ℝ := Fintype.card R
  have hK : 0 < K := by dsimp only [K]; exact_mod_cast Fintype.card_pos
  have hterm (a : A) (b : B) (r : R) : |Phi a b r * e a r * d b r| ≤
      L * (delta / K) * (gamma / K) := by
    rw [abs_mul, abs_mul]
    exact mul_le_mul (mul_le_mul (hPhi a b r) (he a r) (abs_nonneg _) hL)
      (hd b r) (abs_nonneg _) (mul_nonneg hL (div_nonneg hdelta hK.le))
  have hmean (r : R) : |p.mean (fun a => q.mean (fun b => Phi a b r * e a r * d b r))| ≤
      L * (delta / K) * (gamma / K) := by
    apply p.abs_mean_le_on_support
    intro a _
    apply q.abs_mean_le_on_support
    intro b _
    exact hterm a b r
  change |K * ∑ r, p.mean (fun a => q.mean (fun b => Phi a b r * e a r * d b r))| ≤ _
  rw [abs_mul, abs_of_pos hK]
  calc
    _ ≤ K * ∑ r, |p.mean (fun a => q.mean (fun b => Phi a b r * e a r * d b r))| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hK.le
    _ ≤ K * ∑ _r : R, L * (delta / K) * (gamma / K) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun r _ => hmean r)) hK.le
    _ = L * delta * gamma := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      change K * (K * (L * (delta / K) * (gamma / K))) = _
      field_simp [hK.ne']

end Erdos3

end

end OAI
