import OAI.NumberTheory.Ostmann.Construction.TupleFrequencyCutoff
import OAI.NumberTheory.Ostmann.Construction.RepeatedTuplePoisson

namespace OAI

/-! # The finite graph amplitude of an injective prime sample -/

namespace Ostmann

open scoped BigOperators FourierTransform SchwartzMap Classical

theorem prime_character_isPrimitive (p : ℕ) (hp : p.Prime)
    (χ : DirichletCharacter ℂ p) (hχ : χ ≠ 1) : χ.IsPrimitive := by
  let : NeZero p := ⟨hp.ne_zero⟩
  rcases (Nat.dvd_prime hp).mp χ.conductor_dvd_level with h | h
  · exact False.elim (hχ (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h))
  · exact h

noncomputable def sampledTupleAmplitude {I : Type*} [Fintype I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X : ℝ) (N : ℕ) (x : I → P) : ℂ :=
  let : ∀ i, NeZero (x i : ℕ) := fun i => ⟨(hP _ (x i).property).ne_zero⟩
  ∑ v ∈ tupleFrequencies (fun i => (x i : ℕ)) N,
    (Real.sqrt (X / (∏ i, (x i : ℕ))) : ℂ) *
      𝓕 ψ ((v : ℝ) * X / (∏ i, (x i : ℕ))) *
      tupleGraphPhase (fun i => (x i : ℕ)) (fun i => χ i (x i)) (fun i => t (x i)) v

theorem sampledTupleAmplitude_eq {I : Type*} [Fintype I] [Nonempty I]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (χ : I → ∀ p : ℕ, DirichletCharacter ℂ p)
    (hχ : ∀ i p, p ∈ P → χ i p ≠ 1) (t : ∀ p : ℕ, ZMod p)
    (ψ : 𝓢(ℝ, ℂ)) (X H : ℝ) (hX : 0 < X) (N : ℕ)
    (hsupp : ∀ u : ℝ, H < |u| → 𝓕 ψ u = 0)
    (x : I → P) (hx : Function.Injective x)
    (hcut : H * (∏ i, (x i : ℕ)) ≤ N * X) :
    characterTupleSum (fun i => (x i : ℕ)) χ t ψ X / (Real.sqrt X : ℂ) =
      sampledTupleAmplitude P hP χ t ψ X N x := by
  let : ∀ i, NeZero (x i : ℕ) := fun i => ⟨(hP _ (x i).property).ne_zero⟩
  let : NeZero (∏ i, (x i : ℕ)) := ⟨Finset.prod_ne_zero_iff.mpr
    (fun i _ => (hP _ (x i).property).ne_zero)⟩
  have hc : Pairwise (fun i j => (x i : ℕ).Coprime (x j : ℕ)) := by
    intro i j hij
    apply (hP _ (x i).property).coprime_iff_not_dvd.mpr
    intro hd
    have he : (x i : ℕ) = (x j : ℕ) :=
      ((Nat.dvd_prime (hP _ (x j).property)).mp hd).resolve_left (hP _ (x i).property).ne_one
    exact hij (hx (Subtype.ext he))
  exact tuple_character_poisson_finite (fun i => (x i : ℕ))
    (fun i => (hP _ (x i).property).two_le) hc (fun i => χ i (x i))
    (fun i => prime_character_isPrimitive _ (hP _ (x i).property) _ (hχ i _ (x i).property))
    (fun i => t (x i)) ψ X H hX N hcut hsupp

end Ostmann

end OAI
