import OAI.GroupTheory.PolycyclicRecognition.Algebra.IntertwinedActionWords
import Mathlib.RingTheory.Nilpotent.Basic

namespace OAI

/-! # Unipotent powers descend through surjective intertwining maps -/

namespace PolycyclicRecognition

variable {K V U : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup U] [Module K U]

theorem linear_power_intertwines (q : V →ₗ[K] U)
    (T : Module.End K V) (S : Module.End K U)
    (h : ∀ v, q (T v) = S (q v)) (n : ℕ) (v : V) :
    q ((T ^ n) v) = (S ^ n) (q v) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', pow_succ']
    change q (T ((T ^ n) v)) = S ((S ^ n) (q v))
    rw [h, ih]

theorem nilpotent_of_surjective_intertwining (q : V →ₗ[K] U)
    (hq : Function.Surjective q) (T : Module.End K V) (S : Module.End K U)
    (h : ∀ v, q (T v) = S (q v)) (hn : IsNilpotent T) : IsNilpotent S := by
  obtain ⟨n, hn⟩ := hn
  refine ⟨n, LinearMap.ext fun u => ?_⟩
  obtain ⟨v, rfl⟩ := hq u
  rw [← linear_power_intertwines q T S h, hn]
  simp

theorem unipotent_power_of_surjective_intertwining (q : V →ₗ[K] U)
    (hq : Function.Surjective q) (T : Module.End K V) (S : Module.End K U)
    (h : ∀ v, q (T v) = S (q v))
    (hn : ∃ m : ℕ, 0 < m ∧ IsNilpotent (T ^ m - 1)) :
    ∃ m : ℕ, 0 < m ∧ IsNilpotent (S ^ m - 1) := by
  obtain ⟨m, hm, hn⟩ := hn
  refine ⟨m, hm, nilpotent_of_surjective_intertwining q hq _ _ ?_ hn⟩
  intro v
  change q ((T ^ m) v - v) = (S ^ m) (q v) - q v
  rw [map_sub, linear_power_intertwines q T S h]

end PolycyclicRecognition

end OAI
