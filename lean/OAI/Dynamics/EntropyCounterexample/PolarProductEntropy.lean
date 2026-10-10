import OAI.Dynamics.EntropyCounterexample.RegisterEntropyCoding
import OAI.Dynamics.EntropyCounterexample.EntropyBounds
import OAI.Dynamics.EntropyCounterexample.PolarLabels
import OAI.Dynamics.EntropyCounterexample.ImageEntropy

namespace OAI

namespace Problem340
namespace PolarProductEntropy

open Set Dynamics
open scoped Uniformity

def radialProduct {α S : Type*} (R : α → α) (q : ℕ)
    (x : Fin q → α × S) : Fin q → α × S :=
  fun j => (R (x j).1, (x j).2)

lemma radialProduct_iterate_apply {α S : Type*} (R : α → α) (q n : ℕ)
    (x : Fin q → α × S) (j : Fin q) :
    (radialProduct R q)^[n] x j = (R^[n] (x j).1, (x j).2) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    simp only [Function.iterate_succ_apply, ih, radialProduct]

theorem coverEntropy_radialProduct {S : Type*} [PseudoMetricSpace S]
    [CompactSpace S] [Nonempty S] (A : ℝ) (hA : 0 ≤ A)
    (R : Set.Icc (0 : ℝ) A → Set.Icc (0 : ℝ) A) (hR : Monotone R) (q : ℕ) :
    coverEntropy (radialProduct (S := S) R q) Set.univ = 0 := by
  let : Nonempty (Set.Icc (0 : ℝ) A) := ⟨⟨0, le_rfl, hA⟩⟩
  apply coverEntropy_eq_zero_of_polynomial_net_bound _ Set.univ_nonempty
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_uniformity_dist.mp hU
  obtain ⟨H, b, hb, hbdiam⟩ := exists_monotone_interval_labels A hε
  obtain ⟨K, c, hcdiam⟩ := exists_small_fiber_labels (X := S) hε
  refine ⟨(K * (H + 1 + 1)) ^ q, q, fun n => ?_⟩
  have hbound := RegisterEntropyCoding.netMaxcard_le_of_radius_angle
    (radialProduct (S := S) R q) Set.univ U n R b hR hb
    (fun x j => (x j).1) (fun x j => c (x j).2)
    (fun _ _ => Set.mem_univ _) (fun _ _ => rfl) (fun _ => rfl) (by
      intro x _ y _ ha hr
      apply hεU
      rw [dist_pi_lt_iff hε]
      intro j
      rw [Prod.dist_eq, max_lt_iff]
      constructor
      · simpa only [Subtype.dist_eq, Real.dist_eq] using hbdiam _ _ (hr j)
      · exact hcdiam _ _ (ha j))
  apply hbound.trans
  exact_mod_cast RegisterEntropyCoding.register_bound_le_polynomial K (H + 1) q n

theorem coverEntropy_polar_factor {S X : Type*} [PseudoMetricSpace S]
    [CompactSpace S] [Nonempty S] [UniformSpace X]
    (A : ℝ) (hA : 0 ≤ A)
    (R : Set.Icc (0 : ℝ) A → Set.Icc (0 : ℝ) A) (hR : Monotone R) (q : ℕ)
    (p : (Fin q → Set.Icc (0 : ℝ) A × S) → X) (hp : Continuous p)
    (T : X → X) (hsem : Function.Semiconj p (radialProduct R q) T) :
    coverEntropy T (Set.range p) = 0 := by
  let : Nonempty (Set.Icc (0 : ℝ) A) := ⟨⟨0, le_rfl, hA⟩⟩
  apply le_antisymm _ (coverEntropy_nonneg T (Set.range_nonempty p))
  have h := coverEntropy_image_le_of_uniformContinuous hsem
    (CompactSpace.uniformContinuous_of_continuous hp) Set.univ
  simpa only [Set.image_univ, coverEntropy_radialProduct A hA R hR q] using h

theorem coverEntropy_polar_factor_univ {S X : Type*} [PseudoMetricSpace S]
    [CompactSpace S] [Nonempty S] [UniformSpace X]
    (A : ℝ) (hA : 0 ≤ A)
    (R : Set.Icc (0 : ℝ) A → Set.Icc (0 : ℝ) A) (hR : Monotone R) (q : ℕ)
    (p : (Fin q → Set.Icc (0 : ℝ) A × S) → X) (hp : Continuous p)
    (hpsurj : Function.Surjective p)
    (T : X → X) (hsem : Function.Semiconj p (radialProduct R q) T) :
    coverEntropy T Set.univ = 0 := by
  simpa only [hpsurj.range_eq] using
    coverEntropy_polar_factor A hA R hR q p hp T hsem

theorem coverEntropy_polar_first_image {S X : Type*} [PseudoMetricSpace S]
    [CompactSpace S] [Nonempty S] [UniformSpace X] [CompactSpace X] [Nonempty X]
    (A : ℝ) (hA : 0 ≤ A)
    (R : Set.Icc (0 : ℝ) A → Set.Icc (0 : ℝ) A) (hR : Monotone R) (q : ℕ)
    (p : (Fin q → Set.Icc (0 : ℝ) A × S) → X) (hp : Continuous p)
    (T : X → X) (hsem : Function.Semiconj p (radialProduct R q) T)
    (himage : Set.range T ⊆ Set.range p) :
    coverEntropy T Set.univ = 0 :=
  coverEntropy_univ_eq_zero_of_first_image_factor T (radialProduct R q) p hsem
    (CompactSpace.uniformContinuous_of_continuous hp) himage
    (coverEntropy_radialProduct A hA R hR q)

end PolarProductEntropy
end Problem340

end OAI
