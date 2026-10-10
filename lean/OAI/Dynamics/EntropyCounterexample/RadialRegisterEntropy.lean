import OAI.Dynamics.EntropyCounterexample.PolarProductEntropy

namespace OAI

namespace Problem340
namespace RadialRegisterEntropy

open Set Dynamics

abbrev UnitComplex := Metric.sphere (0 : ℂ) (1 : ℝ)

lemma exists_polar_representation (A : ℝ) (z : ℂ) (hz : ‖z‖ ≤ A) :
    ∃ r : Set.Icc (0 : ℝ) A, ∃ u : UnitComplex, (r : ℝ) • (u : ℂ) = z := by
  refine ⟨⟨‖z‖, norm_nonneg z, hz⟩,
    ⟨Complex.exp (z.arg * Complex.I), ?_⟩, ?_⟩
  · simpa only [Metric.mem_sphere, dist_zero_right] using
      Complex.norm_exp_ofReal_mul_I z.arg
  · exact (Complex.real_smul).trans (Complex.norm_mul_exp_arg_mul_I z)

def coordinatewise {X : Type*} (T : X → X) (q : ℕ) (x : Fin q → X) : Fin q → X :=
  fun j => T (x j)

theorem coverEntropy_coordinatewise_eq_zero {X : Type*} [UniformSpace X]
    [CompactSpace X] [Nonempty X]
    (A : ℝ) (hA : 0 ≤ A)
    (embed : ℂ → X) (hembed : Continuous embed) (T : X → X)
    (R : Set.Icc (0 : ℝ) A → Set.Icc (0 : ℝ) A) (hR : Monotone R)
    (hradial : ∀ r : Set.Icc (0 : ℝ) A, ∀ u : UnitComplex,
      T (embed ((r : ℝ) • (u : ℂ))) = embed ((R r : ℝ) • (u : ℂ)))
    (himage : ∀ x, ∃ z : ℂ, ‖z‖ ≤ A ∧ T x = embed z) (q : ℕ) :
    coverEntropy (coordinatewise T q) Set.univ = 0 := by
  let p : (Fin q → Set.Icc (0 : ℝ) A × UnitComplex) → (Fin q → X) :=
    fun x j => embed (((x j).1 : ℝ) • ((x j).2 : ℂ))
  have hp : Continuous p := by
    dsimp [p]
    fun_prop
  apply PolarProductEntropy.coverEntropy_polar_first_image A hA R hR q p hp
    (coordinatewise T q)
  · intro x
    funext j
    exact (hradial (x j).1 (x j).2).symm
  · rintro _ ⟨x, rfl⟩
    have hx : ∀ j : Fin q, ∃ v : Set.Icc (0 : ℝ) A × UnitComplex,
        embed ((v.1 : ℝ) • (v.2 : ℂ)) = T (x j) := by
      intro j
      obtain ⟨z, hz, hT⟩ := himage (x j)
      obtain ⟨r, u, hru⟩ := exists_polar_representation A z hz
      exact ⟨(r, u), by rw [hru, hT]⟩
    choose v hv using hx
    exact ⟨v, funext hv⟩

end RadialRegisterEntropy
end Problem340

end OAI
