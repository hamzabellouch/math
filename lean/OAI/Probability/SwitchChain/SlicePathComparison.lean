import OAI.Probability.SwitchChain.PermutationPathComparison
import OAI.Probability.SwitchChain.PermutationFactors
import OAI.Probability.SwitchChain.SlicePermutationAction

namespace OAI

noncomputable section
open scoped BigOperators
open Problem315.SlicePermutationAction

namespace Problem315.SlicePathComparison

variable {α : Type*} [Fintype α] [DecidableEq α]

def swaps : Finset (Equiv.Perm α) := by
  classical
  exact Finset.univ.filter Equiv.Perm.IsSwap

@[simp] theorem mem_swaps (σ : Equiv.Perm α) : σ ∈ swaps ↔ Equiv.Perm.IsSwap σ := by
  classical
  simp [swaps]

theorem variance_le_swap_squared_differences {q : ℕ} [Nonempty (Slice α q)]
    (f : Slice α q → ℝ) :
    (∑ s, (f s - (∑ t, f t) / (Fintype.card (Slice α q) : ℝ)) ^ 2) ≤
      (Fintype.card α : ℝ) ^ 2 / 2 *
        ∑ σ ∈ swaps, ∑ s, (f s - f (relabel σ s)) ^ 2 := by
  classical
  let S : Finset (Equiv.Perm (Slice α q)) := swaps.image relabelEquiv
  have hwords (σ : Equiv.Perm α) :
      ∃ l : List (Equiv.Perm (Slice α q)), l.length ≤ Fintype.card α ∧
        l.prod = relabelHom q σ ∧ ∀ τ ∈ l, τ ∈ S := by
    obtain ⟨l, hprod, hswap, hlen⟩ := PermutationFactors.exists_swap_factors_length_le σ
    refine ⟨l.map relabelEquiv, by simpa using hlen, ?_, ?_⟩
    · rw [← relabelEquiv_list_prod, hprod]
      rfl
    · intro τ hτ
      obtain ⟨υ, hυ, rfl⟩ := List.mem_map.mp hτ
      exact Finset.mem_image.mpr ⟨υ, (mem_swaps υ).mpr (hswap υ hυ), rfl⟩
  have h := PermutationPaths.variance_le_generator_energy_of_words
    (relabelHom q) (fun s t => exists_relabel_eq s t) S (Fintype.card α) hwords f
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact Finset.sum_image_le_of_nonneg (fun τ _ =>
    Finset.sum_nonneg fun s _ => sq_nonneg (f s - f (τ s)))

theorem relabel_displacement_eq_twice_energy {q : ℕ}
    (σ : Equiv.Perm α) (f : Slice α q → ℝ) :
    (∑ s, (f s - f (relabel σ s)) ^ 2) =
      2 * (∑ s, f s * (f s - f (relabel σ s))) := by
  have hnorm := sum_relabel σ (fun s => (f s) ^ 2)
  simp only [sub_sq, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum, ← sq]
  rw [hnorm]
  ring

theorem variance_le_card_sq_swap_energy {q : ℕ} [Nonempty (Slice α q)]
    (f : Slice α q → ℝ) :
    (∑ s, (f s - (∑ t, f t) / (Fintype.card (Slice α q) : ℝ)) ^ 2) ≤
      (Fintype.card α : ℝ) ^ 2 *
        ∑ s, f s * (∑ σ ∈ swaps, (f s - f (relabel σ s))) := by
  have h := variance_le_swap_squared_differences f
  simp_rw [relabel_displacement_eq_twice_energy] at h
  rw [← Finset.mul_sum] at h
  have hcomm : (∑ σ ∈ swaps, ∑ s, f s * (f s - f (relabel σ s))) =
      ∑ s, f s * (∑ σ ∈ swaps, (f s - f (relabel σ s))) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    exact (Finset.mul_sum _ _ _).symm
  rw [hcomm] at h
  nlinarith [h]

theorem uniform_variance_le_card_sq_swap_energy {q : ℕ} [Nonempty (Slice α q)]
    (f : Slice α q → ℝ) :
    (∑ s, (f s - (∑ t, f t) / (Fintype.card (Slice α q) : ℝ)) ^ 2) /
        (Fintype.card (Slice α q) : ℝ) ≤
      (Fintype.card α : ℝ) ^ 2 *
        ((∑ s, f s * (∑ σ ∈ swaps, (f s - f (relabel σ s)))) /
          (Fintype.card (Slice α q) : ℝ)) := by
  simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
    (variance_le_card_sq_swap_energy f) (Nat.cast_nonneg (Fintype.card (Slice α q)))

theorem variance_le_card_sq_transport {q : ℕ} {X : Type*} [Fintype X] [Nonempty X]
    (e : X ≃ Slice α q) (f : X → ℝ) :
    (∑ x, (f x - (∑ y, f y) / (Fintype.card X : ℝ)) ^ 2) ≤
      (Fintype.card α : ℝ) ^ 2 *
        ∑ x, f x * (∑ σ ∈ swaps, (f x - f (e.symm (relabel σ (e x))))) := by
  classical
  let : Nonempty (Slice α q) := ⟨e (Classical.arbitrary X)⟩
  have hmean : (∑ s : Slice α q, f (e.symm s)) = ∑ x : X, f x :=
    Equiv.sum_comp e.symm f
  have hcard : Fintype.card (Slice α q) = Fintype.card X := Fintype.card_congr e.symm
  have h := variance_le_card_sq_swap_energy (fun s => f (e.symm s))
  rw [hmean, hcard] at h
  have hleft : (∑ s : Slice α q,
      (f (e.symm s) - (∑ y, f y) / (Fintype.card X : ℝ)) ^ 2) =
      ∑ x : X, (f x - (∑ y, f y) / (Fintype.card X : ℝ)) ^ 2 :=
    Equiv.sum_comp e.symm (fun x => (f x - (∑ y, f y) / (Fintype.card X : ℝ)) ^ 2)
  have hright : (∑ s : Slice α q, f (e.symm s) *
      (∑ σ ∈ swaps, (f (e.symm s) - f (e.symm (relabel σ s))))) =
      ∑ x : X, f x * (∑ σ ∈ swaps, (f x - f (e.symm (relabel σ (e x))))) := by
    apply Fintype.sum_equiv e.symm
    intro s
    simp
  rwa [hleft, hright] at h

end Problem315.SlicePathComparison

end

end OAI
