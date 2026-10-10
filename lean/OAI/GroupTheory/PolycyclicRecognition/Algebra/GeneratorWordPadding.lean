import OAI.GroupTheory.PolycyclicRecognition.Algebra.GeneratorSchemes
import Mathlib.Data.List.TakeDrop

namespace OAI

/-! # Fixed-length generator words and their consecutive prefixes -/

noncomputable section
namespace PolycyclicRecognition

variable {I L G : Type*} [AddCommMonoid L] [Module ℝ L] [Group G]
  (X : I → L) (Exp : L → G)

/-- Appending zero-amplitude letters changes no prefix product. -/
theorem generatorGroupWord_zero_padding
    (hzero : Exp 0 = 1)
    (i₀ : I) (u : List (I × ℝ)) (n j : ℕ) :
    generatorGroupWord X Exp ((u ++ List.replicate n (i₀, 0)).take j) =
      generatorGroupWord X Exp (u.take j) := by
  simp only [List.take_append, List.take_replicate]
  simp [generatorGroupWord, hzero]

/-- A bounded-length generator word can be padded to one prescribed length,
preserving its amplitude bound and all previous prefix products. -/
theorem exists_fixed_length_generator_word
    (hzero : Exp 0 = 1)
    (i₀ : I) (u : List (I × ℝ)) {N : ℕ} (hlen : u.length ≤ N)
    {C : ℝ} (hC : 0 ≤ C) (hamp : ∀ z ∈ u, |z.2| ≤ C) :
    ∃ v : List (I × ℝ), v.length = N ∧ (∀ z ∈ v, |z.2| ≤ C) ∧
      generatorGroupWord X Exp v = generatorGroupWord X Exp u ∧
      ∀ j, generatorGroupWord X Exp (v.take j) = generatorGroupWord X Exp (u.take j) := by
  let v := u ++ List.replicate (N - u.length) (i₀, 0)
  have hv : v.length = N := by simp only [v, List.length_append, List.length_replicate]; omega
  refine ⟨v, hv, ?_, ?_, generatorGroupWord_zero_padding X Exp hzero i₀ u _⟩
  · intro z hz
    rcases List.mem_append.mp hz with hz | hz
    · exact hamp z hz
    · have he := List.eq_of_mem_replicate hz
      simpa only [he, abs_zero] using hC
  · have hp := generatorGroupWord_zero_padding X Exp hzero i₀ u (N - u.length) N
    change generatorGroupWord X Exp (v.take N) = generatorGroupWord X Exp (u.take N) at hp
    rwa [List.take_of_length_le hv.le, List.take_of_length_le hlen] at hp

/-- Consecutive prefix products differ by precisely the next generator. -/
theorem generatorGroupWord_take_succ
    (u : List (I × ℝ)) (j : ℕ) (hj : j < u.length) :
    generatorGroupWord X Exp (u.take (j + 1)) =
      generatorGroupWord X Exp (u.take j) * Exp (u[j].2 • X u[j].1) := by
  rw [← List.take_concat_get' u j hj]
  simp only [generatorGroupWord, List.map_append, List.prod_append, List.map_cons, List.map_nil, List.prod_cons,
    List.prod_nil, mul_one]

/-- Logarithms of the actual prefixes have the required endpoints and edges. -/
theorem generator_prefix_log_chain
    (hinj : Function.Injective Exp) (hzero : Exp 0 = 1)
    (u : List (I × ℝ)) {N : ℕ} (hu : u.length = N)
    (k : ℕ → L) (hk : ∀ j, Exp (k j) = generatorGroupWord X Exp (u.take j))
    (v : L) (hend : generatorGroupWord X Exp u = Exp v) :
    k 0 = 0 ∧ k N = v ∧ ∀ j (hj : j < u.length),
      Exp (k (j + 1)) = Exp (k j) * Exp (u[j].2 • X u[j].1) := by
  refine ⟨?_, ?_, ?_⟩
  · apply hinj
    simpa only [List.take_zero, generatorGroupWord_nil, hzero] using hk 0
  · apply hinj
    have h := hk N
    rwa [List.take_of_length_le hu.le, hend] at h
  · intro j hj
    rw [hk (j + 1), generatorGroupWord_take_succ X Exp u j hj, hk j]

end PolycyclicRecognition

end

end OAI
