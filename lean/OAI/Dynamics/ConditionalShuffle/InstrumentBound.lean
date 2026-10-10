import OAI.Dynamics.ConditionalShuffle.Sequences

namespace OAI

noncomputable section
namespace Revealed.Instrument
open scoped Classical
open Thorp Thorp.Fourier Thorp.Specht Revealed.Disintegration
variable {E S Ω α β : Type} [fintype_S : Fintype S] [Fintype Ω] [nonempty_Ω : Nonempty Ω]
  [Fintype α] [DecidableEq α] [nontrivial_α : Nontrivial α] [Fintype β] [DecidableEq β]
variable (I : Data E S (Equiv.Perm α) Ω)

lemma kernels_dichotomy (h : ∀ e s, Trim.signDichotomy (kernel I e s))
    (e : E) (n : ℕ) (p : Fin n → S) : ∀ i, Trim.signDichotomy (kernels I e n p i) := by
  let retained_fintype_S := fintype_S
  let retained_nonempty_Ω := nonempty_Ω
  let retained_nontrivial_α := nontrivial_α
  induction n with
  | zero => intro i; exact Fin.elim0 i
  | succ n ih =>
      intro i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa only [kernels, Fin.snoc_last] using h (base I e n (Fin.init p)) (p (Fin.last n))
      · simpa only [kernels, Fin.snoc_castSucc] using ih (Fin.init p) j

lemma block_kernel_dichotomy (h : ∀ e s, Trim.signDichotomy (kernel I e s))
    (e : E) (t : ℕ) (p : Fin t → S) : Trim.signDichotomy (kernel (block I t) e p) := by
  change Trim.signDichotomy (conditional (pathJoint I e t) p)
  by_cases hp : weights I e t p = 0
  · have hh : conditional (pathJoint I e t) p = fun _ => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹ := by
      funext g
      simp [conditional, pathJoint_marginal, hp]
    rw [hh]
    exact Trim.signDichotomy_uniform
  · rw [conditional_pathJoint I e t p hp]
    exact Trim.signDichotomy_realProduct t _ (kernels_dichotomy I h e t p)

theorem distance_eight_le (hn : 16 ≤ Fintype.card α)
    (ψ : (Fin 8 → Equiv.Perm β) →* Equiv.Perm α)
    (hc : 2 * ((Fintype.card (Equiv.Perm β) : ℝ) / Fintype.card (Equiv.Perm α)) < 1)
    (hb : ∀ e s, Trim.signDichotomy (kernel I e s)) (C : ℝ)
    (hC : ∀ e, ∑ s, probability I e s * Trim.discarded ψ (kernel I e s) ≤ C) (e : E) :
    distance I e 8 ≤ 32 * C + (1/2 : ℝ) * Real.sqrt
      ((32 * (permutationFamily β).reciprocalSum)^8 * exceptionalReciprocalSum (Fintype.card α)) := by
  have hp (p : Fin 8 → S) := repaired_eight_tv hn ψ (kernels I e 8 p)
    (kernels_nonneg I e 8 p) (kernels_sum I e 8 p) hc (kernels_dichotomy I hb e 8 p)
  have ht := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
    mul_le_mul_of_nonneg_left (hp p) (weights_nonneg I e 8 p))
  have hcost := costs_sum_le I (fun e s => Trim.discarded ψ (kernel I e s)) C hC e 8
  simp_rw [costs_kernels] at hcost
  change distance I e 8 ≤ _ at ht
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, weights_sum,
    one_mul] at ht
  have he : (∑ p : Fin 8 → S, weights I e 8 p * (4 * ∑ i, Trim.discarded ψ (kernels I e 8 p i))) =
      4 * ∑ p : Fin 8 → S, weights I e 8 p * ∑ i, Trim.discarded ψ (kernels I e 8 p i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p _
    ring
  rw [he] at ht
  norm_num only [Nat.cast_ofNat] at hcost
  linarith

end Revealed.Instrument

end

end OAI
