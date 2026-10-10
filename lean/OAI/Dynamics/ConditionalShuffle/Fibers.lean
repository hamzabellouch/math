import OAI.Dynamics.ConditionalShuffle.Trimming

namespace OAI

noncomputable section
namespace Revealed.Disintegration
open scoped Classical
open Thorp

lemma fairMass_comp_equiv {Ω X : Type*} [Fintype Ω] (f : Ω → X) (C : Equiv.Perm Ω) :
    fairMass (f ∘ C) = fairMass f := by
  funext x
  unfold fairMass
  congr 1
  exact Equiv.sum_comp C (fun ω => if f ω = x then (1 : ℝ) else 0)

lemma conditional_injective {E G Ω : Type*} [Fintype E] [Fintype G] [Nonempty G]
    [Fintype Ω] [Nonempty Ω] [DecidableEq G]
    (a : Ω → E) (b : Ω → G) (ha : Function.Injective a) (e : E) :
    (conditional (fairMass (fun ω => (a ω, b ω))) e = fun _ => (Fintype.card G : ℝ)⁻¹) ∨
      ∃ g, conditional (fairMass (fun ω => (a ω, b ω))) e = fun h => if h = g then 1 else 0 := by
  by_cases he : ∃ ω, a ω = e
  · obtain ⟨ω, rfl⟩ := he
    right
    refine ⟨b ω, ?_⟩
    have hq : marginal (fairMass (fun ω => (a ω, b ω))) (a ω) = (Fintype.card Ω : ℝ)⁻¹ := by
      rw [marginal_fairMass]
      simp [fairMass, ha.eq_iff]
    funext g
    have hj : fairMass (fun ω => (a ω, b ω)) (a ω, g) =
        (if b ω = g then 1 else 0) / (Fintype.card Ω : ℝ) := by
      simp [fairMass, Prod.mk.injEq, ha.eq_iff, ite_and]
    have hn : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [conditional, hq, ite_eq_right (inv_ne_zero hn), hj]
    by_cases hg : g = b ω
    · subst g
      simp [hn]
    · simp [hg, Ne.symm hg]
  · left
    have hq : marginal (fairMass (fun ω => (a ω, b ω))) e = 0 := by
      rw [marginal_fairMass]
      have hh : ∀ ω, a ω ≠ e := by simpa using he
      simp [fairMass, hh]
    funext g
    simp [conditional, hq]

lemma conditional_mul_invariant {E G Ω : Type*} [Fintype E] [Fintype G] [Group G]
    [Fintype Ω] (a : Ω → E) (b : Ω → G) (C : Equiv.Perm Ω) (τ : G)
    (ha : ∀ ω, a (C ω) = a ω) (hb : ∀ ω, b (C ω) = b ω * τ) (e : E) (g : G) :
    conditional (fairMass (fun ω => (a ω, b ω))) e (g * τ) =
      conditional (fairMass (fun ω => (a ω, b ω))) e g := by
  have hj : fairMass (fun ω => (a ω, b ω)) (e, g * τ) =
      fairMass (fun ω => (a ω, b ω)) (e, g) := by
    have h := congrFun (fairMass_comp_equiv (fun ω => (a ω, b ω)) C) (e, g * τ)
    simp only [fairMass, Function.comp_apply, ha, hb, Prod.mk.injEq, mul_right_cancel_iff] at h
    simpa only [fairMass, Prod.mk.injEq] using h.symm
  unfold conditional
  split_ifs <;> simp [hj]

end Revealed.Disintegration

namespace Thorp.Trim
open scoped Classical
open Revealed.Disintegration
variable {α : Type} [Fintype α] [DecidableEq α] [nontrivial_α : Nontrivial α]

lemma signDichotomy_uniform : signDichotomy (fun _ : Equiv.Perm α => (Fintype.card (Equiv.Perm α) : ℝ)⁻¹) := by
  left
  rw [← Finset.mul_sum, Specht.complexSign_sum, mul_zero]

lemma sign_zero_of_right_invariant (μ : Equiv.Perm α → ℝ) (τ : Equiv.Perm α)
    (hm : ∀ g, μ (g * τ) = μ g) (hτ : Specht.complexSign τ = -1) :
    (∑ g, (μ g : ℂ) * Specht.complexSign g) = 0 := by
  let retained_nontrivial_α := nontrivial_α
  have h := Equiv.sum_comp (Equiv.mulRight τ) (fun g => (μ g : ℂ) * Specht.complexSign g)
  change (∑ g, (μ (g * τ) : ℂ) * Specht.complexSign (g * τ)) = _ at h
  simp only [hm, map_mul, hτ, mul_neg, mul_one, Finset.sum_neg_distrib] at h
  linear_combination - (1 / 2 : ℂ) * h

lemma signDichotomy_conditional_injective {E Ω : Type*} [Fintype E] [Fintype Ω] [Nonempty Ω]
    (a : Ω → E) (b : Ω → Equiv.Perm α) (ha : Function.Injective a) (e : E) :
    signDichotomy (conditional (fairMass (fun ω => (a ω, b ω))) e) := by
  rcases conditional_injective a b ha e with h | h
  · rw [h]
    exact signDichotomy_uniform
  · exact Or.inr h

lemma signDichotomy_conditional_symmetry {E Ω : Type*} [Fintype E] [Fintype Ω]
    (a : Ω → E) (b : Ω → Equiv.Perm α) (C : Equiv.Perm Ω) (τ : Equiv.Perm α)
    (ha : ∀ ω, a (C ω) = a ω) (hb : ∀ ω, b (C ω) = b ω * τ)
    (hτ : Specht.complexSign τ = -1) (e : E) :
    signDichotomy (conditional (fairMass (fun ω => (a ω, b ω))) e) := by
  left
  exact sign_zero_of_right_invariant _ τ (conditional_mul_invariant a b C τ ha hb e) hτ

end Thorp.Trim

end

end OAI
