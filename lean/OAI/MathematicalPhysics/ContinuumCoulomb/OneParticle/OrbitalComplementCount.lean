import OAI.Analysis.CoulombRadii.FieldAnalysis.FermionicCoefficients

namespace OAI

/-! A coefficient array orthogonal to all tensors of the chosen orbitals
has at least one particle outside them. This counts particles, not basis
configurations, and so introduces no exponential dimension factor. -/

noncomputable section
open scoped BigOperators Classical
namespace ContinuumCoulomb

theorem complement_coefficient_pointwise {α : Type*} {n : ℕ}
    (S : Set α) (c : (Fin (n+1) → α) → ℂ)
    (hzero : ∀ b, (∀ i, b i ∈ S) → c b = 0) (b : Fin (n+1) → α) :
    (∑ i, if b i ∈ S then ‖c b‖^2 else (0:ℝ)) ≤ (n:ℝ)*‖c b‖^2 := by
  by_cases hz : c b = 0
  · simp [hz]
  obtain ⟨j,hj⟩ : ∃ j, b j ∉ S := by
    by_contra! hh
    exact hz (hzero b hh)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),ite_eq_right hj,add_zero]
  calc
    _ ≤ ∑ _i ∈ Finset.univ.erase j, ‖c b‖^2 :=
      Finset.sum_le_sum (fun i _ => by split_ifs <;> first | exact le_rfl | exact sq_nonneg _)
    _ = _ := by simp

theorem complement_coefficient_occupation_sum {α : Type*} {n : ℕ}
    (S : Set α) (c : (Fin (n+1) → α) → ℂ)
    (hzero : ∀ b, (∀ i, b i ∈ S) → c b = 0)
    (hs : Summable (fun b => ‖c b‖^2)) :
    (∑ i, ∑' b, if b i ∈ S then ‖c b‖^2 else (0:ℝ)) ≤
      (n:ℝ)*(∑' b, ‖c b‖^2) := by
  have hi (i : Fin (n+1)) : Summable (fun b => if b i ∈ S then ‖c b‖^2 else (0:ℝ)) :=
    Summable.of_nonneg_of_le (fun b => by positivity)
      (fun b => by split_ifs <;> first | exact le_rfl | exact sq_nonneg _) hs
  rw [← Summable.tsum_finsetSum (fun i _ => hi i),← tsum_mul_left]
  exact Summable.tsum_le_tsum (complement_coefficient_pointwise S c hzero)
    (summable_sum (fun i _ => hi i)) (hs.mul_left (n:ℝ))

theorem coefficient_set_occupation_eq {α : Type*} {n : ℕ}
    {c : (Fin n → α) → ℂ} (hc : Coulomb.FermionicCoefficients c)
    (S : Set α) (i j : Fin n) :
    (∑' b, if b i ∈ S then ‖c b‖^2 else (0:ℝ)) =
      ∑' b, if b j ∈ S then ‖c b‖^2 else (0:ℝ) := by
  let p := Equiv.swap i j
  have he := (Coulomb.coefficientPermEquiv (α := α) p).tsum_eq
    (fun b => if b i ∈ S then ‖c b‖^2 else (0:ℝ))
  change (∑' b, if (b ∘ p) i ∈ S then ‖c (b ∘ p)‖^2 else (0:ℝ)) = _ at he
  simpa only [Function.comp_apply,p,Equiv.swap_apply_left,hc.norm_permute] using he.symm

theorem complement_coefficient_single_occupation {α : Type*} {n : ℕ}
    (S : Set α) (c : (Fin (n+1) → α) → ℂ) (hc : Coulomb.FermionicCoefficients c)
    (hzero : ∀ b, (∀ i, b i ∈ S) → c b = 0)
    (hs : Summable (fun b => ‖c b‖^2)) (i : Fin (n+1)) :
    (n+1:ℕ)*(∑' b, if b i ∈ S then ‖c b‖^2 else (0:ℝ)) ≤
      (n:ℝ)*(∑' b, ‖c b‖^2) := by
  have h := complement_coefficient_occupation_sum S c hzero hs
  simp_rw [coefficient_set_occupation_eq hc S _ i] at h
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using h

end ContinuumCoulomb

end

end OAI
