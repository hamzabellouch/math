import Mathlib
import OAI.Combinatorics.RamseyFive.Entropy.OriginalLevelLaw

namespace OAI

namespace SharpRamseyFive.FiniteEntropy
open scoped Classical BigOperators
variable {α β : Type*} [Fintype α] [Fintype β]
lemma scaled_uniform_density_iff (R : α → β → Prop) (X : Finset α) (Y : Finset β)
    (hX : X.Nonempty) (hY : Y.Nonempty) (Q τ : ℝ) :
    Q * (((X×ˢY).filter (fun z => R z.1 z.2)).card : ℝ) ≤ τ * X.card * Y.card ↔
      Q * relationMass R (uniformWeight X) (uniformWeight Y) ≤ τ := by
  have hx : (0:ℝ) < X.card := by exact_mod_cast hX.card_pos
  have hy : (0:ℝ) < Y.card := by exact_mod_cast hY.card_pos
  rw [relationMass_uniform, ← mul_div_assoc, div_le_iff₀ (mul_pos hx hy)]
  rw [mul_assoc]

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]
  {A : I → Type*} {B : J → Type*} [∀ i, Fintype (A i)] [∀ j, Fintype (B j)]

theorem original_level_density_rejection
    (μ : ∀ i, Law (A i)) (ν : ∀ j, Law (B j)) (i : I) (j : J)
    (R : α → β → Prop) (X : A i → Finset α) (Y : B j → Finset β)
    (p : Law α) (q : Law β) (L : ℝ) (hL : 0≤L)
    (hs : ∀ x, (∑ a, μ i a * uniformWeight (X a) x) ≤ L*p x)
    (ht : ∀ y, (∑ b, ν j b * uniformWeight (Y b) y) ≤ L*q y)
    (Q τ : ℝ) (hQ : 0≤Q) (hτ : 0<τ) :
    eventMass (originalLevelLaw μ ν) (Finset.univ.filter (fun z =>
      τ < Q*relationMass R (uniformWeight (X (z.1 i))) (uniformWeight (Y (z.2 j))))) ≤
        (Q/τ)*L^2*relationMass R p q := by
  have hm := event_markov (originalLevelLaw μ ν)
    (fun z => Q*relationMass R (uniformWeight (X (z.1 i))) (uniformWeight (Y (z.2 j))))
    (fun z => mul_nonneg hQ (relationMass_nonneg R _ _ (uniformWeight_nonneg _) (uniformWeight_nonneg _)))
    τ (Finset.univ.filter (fun z =>
      τ < Q*relationMass R (uniformWeight (X (z.1 i))) (uniformWeight (Y (z.2 j)))))
    (fun z hz => (Finset.mem_filter.mp hz).2.le)
  have he : (∑ z, originalLevelLaw μ ν z *
      (Q*relationMass R (uniformWeight (X (z.1 i))) (uniformWeight (Y (z.2 j))))) =
      Q*(∑ z, originalLevelLaw μ ν z *
        relationMass R (uniformWeight (X (z.1 i))) (uniformWeight (Y (z.2 j)))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z _
    ring
  rw [he] at hm
  have hd := originalLevelLaw_cross_domination μ ν i j R X Y p q L hL hs ht
  have hh := hm.trans (mul_le_mul_of_nonneg_left hd hQ)
  calc
    _ ≤ (Q*(L^2*relationMass R p q))/τ := (le_div_iff₀ hτ).mpr (by simpa only [mul_comm τ] using hh)
    _ = _ := by ring
end SharpRamseyFive.FiniteEntropy

end OAI
