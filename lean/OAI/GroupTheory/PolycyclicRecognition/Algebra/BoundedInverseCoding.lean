import OAI.GroupTheory.PolycyclicRecognition.Algebra.ParametrizedGeneratorSchemes
import OAI.GroupTheory.PolycyclicRecognition.Algebra.BoundedGeneratorSchemes

namespace OAI

/-! # Continuous generator coding on a whole bounded logarithmic box

A continuous local inverse suffices: divide the logarithm by a fixed
integer, use the local inverse, and repeat its word. This keeps the
combinatorial pattern fixed and makes every amplitude continuous on the
entire prescribed box. In particular, these selectors can be sampled
independently of the starting sheet.
-/

noncomputable section
namespace PolycyclicRecognition

open Set Metric

variable {V L I G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [AddCommGroup L] [Module ℝ L] [Group G]

/-- Upgrade a continuous small-logarithm scheme to any fixed bounded box,
without a measurable-selection theorem or a parameter-dependent word length. -/
theorem bounded_continuous_generator_coding
    (X : I → L) (Exp : L → G) (q : V →ₗ[ℝ] L)
    (hzero : Exp 0 = 1)
    (hadd : ∀ v (s t : ℝ), Exp ((s + t) • v) = Exp (s • v) * Exp (t • v))
    {ε : ℝ} {N : ℕ} {C : ℝ}
    {d : ℕ} (w : Fin d → List (I × ℝ)) (i : Fin d → I)
    (σ : V → Fin d → ℝ) (hσ : ContinuousOn σ (ball 0 ε))
    (hlocal : ∀ y ∈ ball (0 : V) ε,
      (generatorSchemeWord w i (σ y)).length ≤ N ∧
      (∀ z ∈ generatorSchemeWord w i (σ y), |z.2| ≤ C) ∧
      generatorGroupWord X Exp (generatorSchemeWord w i (σ y)) = Exp (q y))
    (R : ℝ) (hR : 0 ≤ R) (k : ℕ) (hk0 : (0 : ℝ) < k)
    (hkR : R < (k : ℝ) * ε) :
    ∃ word : List (I × (closedBall (0 : V) R → ℝ)),
      word.length ≤ k * N ∧ (∀ z ∈ word, Continuous z.2) ∧
      (∀ y, ∀ z ∈ word, |z.2 y| ≤ C) ∧
      ∀ y, generatorGroupWord X Exp (word.map (fun z => (z.1, z.2 y))) = Exp (q y.val) := by
  let Y := closedBall (0 : V) R
  let small : Y → V := fun y => (k : ℝ)⁻¹ • y.val
  have hsmall (y : Y) : small y ∈ ball (0 : V) ε := by
    rw [mem_ball, dist_zero_right]
    dsimp only [small]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hk0), ← div_eq_inv_mul]
    apply (div_lt_iff₀ hk0).mpr
    have hy : ‖y.val‖ ≤ R := by
      have hy : y.val ∈ closedBall (0 : V) R := y.property
      simpa only [mem_closedBall, dist_zero_right] using hy
    exact hy.trans_lt (by simpa only [mul_comm] using hkR)
  have hsmallcont : Continuous small := continuous_const.smul continuous_subtype_val
  let τ : Y → Fin d → ℝ := σ ∘ small
  have hτ : Continuous τ := hσ.comp_continuous hsmallcont hsmall
  let u := parameterGeneratorSchemeWord w i τ
  let word := (List.replicate k u).flatten
  have heval (y : Y) : word.map (fun z => (z.1, z.2 y)) =
      (List.replicate k (generatorSchemeWord w i (τ y))).flatten := by
    simp only [word, List.map_flatten, List.map_replicate, u,
      parameterGeneratorSchemeWord_eval]
  have hlen : u.length ≤ N := by
    let y : Y := ⟨0, by
      change (0 : V) ∈ closedBall (0 : V) R
      simpa only [mem_closedBall, dist_self] using hR⟩
    have hh := (hlocal _ (hsmall y)).1
    change (generatorSchemeWord w i (τ y)).length ≤ N at hh
    rw [← parameterGeneratorSchemeWord_eval w i τ y, List.length_map] at hh
    exact hh
  refine ⟨word, ?_, ?_, ?_, ?_⟩
  · simpa only [word, List.length_flatten, List.map_replicate, List.sum_replicate,
      smul_eq_mul] using Nat.mul_le_mul_left k hlen
  · intro z hz
    obtain ⟨v, hv, hz⟩ := List.mem_flatten.mp hz
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hv
    exact parameterGeneratorSchemeWord_continuous w i τ hτ z hz
  · intro y z hz
    obtain ⟨v, hv, hz⟩ := List.mem_flatten.mp hz
    obtain ⟨_, rfl⟩ := List.mem_replicate.mp hv
    have hz' : (z.1, z.2 y) ∈ generatorSchemeWord w i (τ y) := by
      rw [← parameterGeneratorSchemeWord_eval w i τ y]
      exact List.mem_map.mpr ⟨z, hz, rfl⟩
    exact (hlocal _ (hsmall y)).2.1 _ hz'
  · intro y
    rw [heval]
    have hpow : ∀ v : L, ∀ n : ℕ, Exp ((n : ℝ) • v) = (Exp v) ^ n := by
      intro v n
      induction n with
      | zero => simp [hzero]
      | succ n ih => rw [Nat.cast_add, Nat.cast_one, hadd, ih, one_smul, pow_succ]
    calc
      generatorGroupWord X Exp ((List.replicate k (generatorSchemeWord w i (τ y))).flatten) =
          (generatorGroupWord X Exp (generatorSchemeWord w i (τ y))) ^ k := by
        simp only [generatorGroupWord, List.map_flatten, List.map_replicate,
          List.prod_flatten, List.prod_replicate]
      _ = (Exp (q (small y))) ^ k := congrArg (fun g : G => g ^ k) (hlocal _ (hsmall y)).2.2
      _ = Exp ((k : ℝ) • q (small y)) := (hpow _ _).symm
      _ = Exp (q y.val) := by
        simp only [small, map_smul, smul_smul, mul_inv_cancel₀ hk0.ne', one_smul]

end PolycyclicRecognition

end

end OAI
