import OAI.Probability.SwitchChain.PermutationGenerator

namespace OAI

noncomputable section
open scoped BigOperators RealInnerProductSpace

namespace Problem315.PermutationPoincare

variable {Ω : Type*} [sectionFintypeΩ : Fintype Ω]

def pull (σ : Equiv.Perm Ω) (f : EuclideanSpace ℝ Ω) : EuclideanSpace ℝ Ω :=
  WithLp.toLp 2 (fun x => f (σ x))

include sectionFintypeΩ in
@[simp] theorem pull_apply (σ : Equiv.Perm Ω) (f : EuclideanSpace ℝ Ω) (x : Ω) :
    pull σ f x = f (σ x) := by
  have retainedsectionFintypeΩ := sectionFintypeΩ
  exact rfl

theorem norm_sq_eq_sum (f : EuclideanSpace ℝ Ω) :
    ‖f‖ ^ 2 = ∑ x, (f x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, pow_two]

theorem norm_pull (σ : Equiv.Perm Ω) (f : EuclideanSpace ℝ Ω) :
    ‖pull σ f‖ = ‖f‖ := by
  have h : ‖pull σ f‖ ^ 2 = ‖f‖ ^ 2 := by
    simp only [norm_sq_eq_sum, pull_apply]
    exact Equiv.sum_comp σ (fun x => (f x) ^ 2)
  nlinarith [norm_nonneg (pull σ f), norm_nonneg f]

theorem displacement_mul_le (σ τ : Equiv.Perm Ω) (f : EuclideanSpace ℝ Ω) :
    ‖f - pull (σ * τ) f‖ ≤ ‖f - pull σ f‖ + ‖f - pull τ f‖ := by
  have h : f - pull (σ * τ) f = (f - pull τ f) + pull τ (f - pull σ f) := by
    ext x
    change f x - f (σ (τ x)) = (f x - f (τ x)) + (f (τ x) - f (σ (τ x)))
    ring
  rw [h]
  calc
    _ ≤ ‖f - pull τ f‖ + ‖pull τ (f - pull σ f)‖ := norm_add_le _ _
    _ = _ := by rw [norm_pull]; ring

theorem displacement_prod_le (L : List (Equiv.Perm Ω)) (f : EuclideanSpace ℝ Ω)
    (K : ℝ) (hK : ∀ σ ∈ L, ‖f - pull σ f‖ ≤ K) :
    ‖f - pull L.prod f‖ ≤ (L.length : ℝ) * K := by
  induction L with
  | nil =>
      have h : pull (1 : Equiv.Perm Ω) f = f := by ext x; rfl
      simp [h]
  | cons σ L ih =>
      rw [List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      calc
        _ ≤ ‖f - pull σ f‖ + ‖f - pull L.prod f‖ := displacement_mul_le σ L.prod f
        _ ≤ K + (L.length : ℝ) * K :=
          add_le_add (hK σ (by simp)) (ih (fun τ hτ => hK τ (by simp [hτ])))
        _ = _ := by ring

variable {Γ : Type*} [Group Γ] [Fintype Γ]

theorem sum_action_eq_zero (ρ : Γ →* Equiv.Perm Ω)
    (htrans : ∀ x y : Ω, ∃ g : Γ, ρ g x = y)
    (f : Ω → ℝ) (hf : ∑ x, f x = 0) (x : Ω) :
    ∑ g : Γ, f (ρ g x) = 0 := by
  have hsame (y : Ω) : (∑ g : Γ, f (ρ g y)) = ∑ g : Γ, f (ρ g x) := by
    obtain ⟨h, rfl⟩ := htrans x y
    have hm (g : Γ) : ρ (g * h) x = ρ g (ρ h x) := by
      rw [map_mul]; rfl
    have he := Equiv.sum_comp (Equiv.mulRight h) (fun g => f (ρ g x))
    change (∑ g, f (ρ (g * h) x)) = _ at he
    simpa only [hm] using he
  have htotal : (Fintype.card Ω : ℝ) * (∑ g : Γ, f (ρ g x)) = 0 := by
    calc
      _ = ∑ y : Ω, ∑ g : Γ, f (ρ g y) := by simp only [hsame, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      _ = ∑ g : Γ, ∑ y : Ω, f (ρ g y) := Finset.sum_comm
      _ = ∑ g : Γ, ∑ y : Ω, f y := by
        apply Finset.sum_congr rfl
        intro g _
        exact Equiv.sum_comp (ρ g) f
      _ = 0 := by simp [hf]
  have : Nonempty Ω := ⟨x⟩
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  exact (mul_eq_zero.mp htotal).resolve_left hc

theorem sum_displacement_sq (ρ : Γ →* Equiv.Perm Ω)
    (htrans : ∀ x y : Ω, ∃ g : Γ, ρ g x = y)
    (f : EuclideanSpace ℝ Ω) (hf : ∑ x, f x = 0) :
    (∑ g : Γ, ‖f - pull (ρ g) f‖ ^ 2) =
      2 * (Fintype.card Γ : ℝ) * ‖f‖ ^ 2 := by
  have hexpand (g : Γ) : ‖f - pull (ρ g) f‖ ^ 2 =
      2 * ‖f‖ ^ 2 - 2 * ∑ x, f x * f (ρ g x) := by
    rw [norm_sub_sq_real, norm_pull]
    simp only [PiLp.inner_apply, pull_apply, RCLike.inner_apply, conj_trivial, mul_comm]
    ring
  simp_rw [hexpand]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    ← Finset.mul_sum, Finset.sum_comm]
  have hz : (∑ x, ∑ g : Γ, f x * f (ρ g x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x _
    rw [← Finset.mul_sum, sum_action_eq_zero ρ htrans f hf x, mul_zero]
  rw [hz]
  ring

theorem centered_norm_sq_le_of_bounded_words
    {S : Type*} [Fintype S] (ρ : Γ →* Equiv.Perm Ω) (moves : S → Γ)
    (htrans : ∀ x y : Ω, ∃ g : Γ, ρ g x = y) (N : ℕ)
    (hwords : ∀ g : Γ, ∃ L : List Γ,
      L.prod = g ∧ L.length ≤ N ∧ ∀ a ∈ L, ∃ s, moves s = a)
    (f : EuclideanSpace ℝ Ω) (hf : ∑ x, f x = 0) :
    ‖f‖ ^ 2 ≤ (N : ℝ) ^ 2 / 2 *
      ∑ s, ‖f - pull (ρ (moves s)) f‖ ^ 2 := by
  let E : ℝ := ∑ s, ‖f - pull (ρ (moves s)) f‖ ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg (fun s _ => sq_nonneg _)
  have hroot := Real.sq_sqrt hE
  have hmove (s : S) : ‖f - pull (ρ (moves s)) f‖ ≤ Real.sqrt E := by
    have hle : ‖f - pull (ρ (moves s)) f‖ ^ 2 ≤ E := by
      exact Finset.single_le_sum (fun t _ => sq_nonneg ‖f - pull (ρ (moves t)) f‖)
        (Finset.mem_univ s)
    nlinarith [Real.sqrt_nonneg E, norm_nonneg (f - pull (ρ (moves s)) f)]
  have hnorm (g : Γ) : ‖f - pull (ρ g) f‖ ≤ (N : ℝ) * Real.sqrt E := by
    obtain ⟨L, hprod, hlen, hmem⟩ := hwords g
    have hp : (L.map ρ).prod = ρ g := by rw [← map_list_prod, hprod]
    have h := displacement_prod_le (L.map ρ) f (Real.sqrt E) (by
      intro σ hσ
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hσ
      obtain ⟨s, rfl⟩ := hmem a ha
      exact hmove s)
    rw [hp, List.length_map] at h
    exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hlen)
      (Real.sqrt_nonneg E))
  have hsquare (g : Γ) : ‖f - pull (ρ g) f‖ ^ 2 ≤ (N : ℝ) ^ 2 * E := by
    have h := hnorm g
    have hnonneg : 0 ≤ (N : ℝ) * Real.sqrt E := by positivity
    have hsq := sq_le_sq₀ (norm_nonneg (f - pull (ρ g) f)) hnonneg |>.mpr h
    simpa only [mul_pow, hroot] using hsq
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun g _ => hsquare g)
  rw [sum_displacement_sq ρ htrans f hf, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul] at hsum
  have hc : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos
  have hcancel : 2 * ‖f‖ ^ 2 ≤ (N : ℝ) ^ 2 * E := by
    apply (mul_le_mul_iff_right₀ hc).mp
    nlinarith only [hsum]
  change ‖f‖ ^ 2 ≤ (N : ℝ) ^ 2 / 2 * E
  linarith

end Problem315.PermutationPoincare

end

end OAI
