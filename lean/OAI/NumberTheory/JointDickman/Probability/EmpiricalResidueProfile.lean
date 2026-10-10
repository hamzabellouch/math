import OAI.NumberTheory.JointDickman.Probability.ResidueProfiles
import Mathlib.Topology.Sequences

namespace OAI

/-! # Finite residue coefficients of a bounded arithmetic correlation -/

namespace JointDickman
open Finset Filter
open scoped Topology

noncomputable def empiricalResidueCoefficient (H : ℕ → ℕ → ℂ) (N : ℕ)
    (q : ℕ+) (a : ZMod (q : ℕ)) : ℂ :=
  (q : ℕ) * ((∑ n ∈ range N, if (n : ZMod (q : ℕ)) = a then H N n else 0) / (N : ℂ))

noncomputable def empiricalResidueTest (H : ℕ → ℕ → ℂ) (N : ℕ)
    {q : ℕ} (f : ZMod q → ℂ) : ℂ :=
  (∑ n ∈ range N, H N n * f (n : ZMod q)) / (N : ℂ)

theorem empiricalResidueCoefficient_test (H : ℕ → ℕ → ℂ) (N : ℕ)
    (q : ℕ+) (f : ZMod (q : ℕ) → ℂ) :
    residueMean (fun a => empiricalResidueCoefficient H N q a * f a) =
      empiricalResidueTest H N f := by
  classical
  have hq : ((q : ℕ) : ℂ) ≠ 0 := by exact_mod_cast q.ne_zero
  have hs : (∑ a : ZMod (q : ℕ),
      (∑ n ∈ range N, if (n : ZMod (q : ℕ)) = a then H N n else 0) * f a) =
      ∑ n ∈ range N, H N n * f (n : ZMod (q : ℕ)) := by
    simp only [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro n _
    simp only [ite_mul, zero_mul]
    simp
  unfold residueMean empiricalResidueCoefficient empiricalResidueTest
  have hf (a : ZMod (q : ℕ)) :
      (((q : ℕ) : ℂ) * ((∑ n ∈ range N,
        if (n : ZMod (q : ℕ)) = a then H N n else 0) / (N : ℂ))) * f a =
      (((q : ℕ) : ℂ) / N) * ((∑ n ∈ range N,
        if (n : ZMod (q : ℕ)) = a then H N n else 0) * f a) := by ring
  simp_rw [hf]
  rw [← mul_sum, hs]
  field_simp

theorem empiricalResidueCoefficient_norm_le (H : ℕ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hH : ∀ N n, ‖H N n‖ ≤ C) (N : ℕ) (q : ℕ+)
    (a : ZMod (q : ℕ)) : ‖empiricalResidueCoefficient H N q a‖ ≤ (q : ℕ) * C := by
  classical
  have hs : ‖∑ n ∈ range N, if (n : ZMod (q : ℕ)) = a then H N n else 0‖ ≤ (N : ℝ)*C := by
    have h := norm_sum_le_of_le (range N) (fun n _ => show
        ‖if (n : ZMod (q : ℕ)) = a then H N n else 0‖ ≤ C from by
      split_ifs
      · exact hH N n
      · simpa using hC)
    simpa using h
  by_cases hN : N = 0
  · simp [empiricalResidueCoefficient, hN, mul_nonneg (Nat.cast_nonneg _) hC]
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  unfold empiricalResidueCoefficient
  rw [norm_mul, norm_div, Complex.norm_natCast, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left ((div_le_iff₀ hNpos).mpr (by simpa only [mul_comm] using hs)) (Nat.cast_nonneg _)

/-- All residue coefficients converge simultaneously along one subsequence. -/
theorem empiricalResidueCoefficient_subsequence (H : ℕ → ℕ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hH : ∀ N n, ‖H N n‖ ≤ C) :
    ∃ (s : ℕ → ℕ), StrictMono s ∧
      ∃ V : (q : ℕ+) → ZMod (q : ℕ) → ℂ,
        ∀ q a, Tendsto (fun N => empiricalResidueCoefficient H (s N) q a) atTop (nhds (V q a)) := by
  let K : Set ((q : ℕ+) → ZMod (q : ℕ) → ℂ) :=
    {V | ∀ (q : ℕ+) (a : ZMod (q : ℕ)), V q a ∈ Metric.closedBall 0 ((q : ℕ) * C)}
  have hK : IsCompact K := isCompact_pi_infinite fun (q : ℕ+) =>
    isCompact_pi_infinite fun (_ : ZMod (q : ℕ)) => isCompact_closedBall 0 ((q : ℕ) * C)
  have hx (N : ℕ) : empiricalResidueCoefficient H N ∈ K := by
    intro q a
    rw [Metric.mem_closedBall, dist_zero_right]
    exact empiricalResidueCoefficient_norm_le H hC hH N q a
  obtain ⟨V,_,s,hs,hlim⟩ := hK.tendsto_subseq hx
  refine ⟨s,hs,V,fun q a => ?_⟩
  exact (tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hlim q)) a

end JointDickman

end OAI
