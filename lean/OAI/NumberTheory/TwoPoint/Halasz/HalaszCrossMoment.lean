import OAI.NumberTheory.TwoPoint.Halasz.HalaszCollisionMoment

namespace OAI

/-! Fourier counting with two different collections of tuples, applied
to a prescribed repeated coordinate. -/
namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical ComplexConjugate

noncomputable def halaszCrossCount {ι κ : Type*} {k : ℕ}
    (F : Finset ι) (G : Finset κ) (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) : ℕ :=
  ((F×ˢG).filter (fun x => f x.1=g x.2)).card

theorem halasz_cross_integral {ι κ : Type*} {k : ℕ}
    (F : Finset ι) (G : Finset κ) (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) :
    (∫ α, halaszFinitePhase F f α * conj (halaszFinitePhase G g α)
      ∂halaszVinogradovHaar k) = (halaszCrossCount F G f g:ℂ) := by
  have hi (x : ι) (y : κ) : Integrable (fun α =>
      halaszVinogradovCharacter (f x) α * conj (halaszVinogradovCharacter (g y) α))
      (halaszVinogradovHaar k) := by
    simp_rw [← halasz_vinogradov_character_neg,← halasz_vinogradov_character_add]
    exact halasz_vinogradov_character_integrable _
  unfold halaszFinitePhase
  simp_rw [map_sum,sum_mul,mul_sum]
  rw [integral_finsetSum F (fun x _ => integrable_finsetSum G (fun y _ => hi x y))]
  simp_rw [integral_finsetSum G (fun y _ => hi _ y),halasz_vinogradov_character_inner]
  simp only [halaszCrossCount,card_eq_sum_ones,sum_filter,sum_product,Nat.cast_sum,
    Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

theorem halasz_cross_count_bound {ι κ : Type*} {k : ℕ}
    (F : Finset ι) (G : Finset κ) (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) :
    (halaszCrossCount F G f g:ℝ) ≤
      ∫ α, ‖halaszFinitePhase F f α‖ * ‖halaszFinitePhase G g α‖
        ∂halaszVinogradovHaar k := by
  have h := norm_integral_le_integral_norm
    (fun α => halaszFinitePhase F f α * conj (halaszFinitePhase G g α))
    (μ := halaszVinogradovHaar k)
  rw [halasz_cross_integral,Complex.norm_natCast] at h
  simpa only [norm_mul,Complex.norm_conj] using h

def halaszRepeatedFrequency (n k N : ℕ) (x : Fin N × (Fin n → Fin N)) : Fin k → ℤ :=
  fun j => 2*((x.1.val+1)^(j.val+1):ℕ)+halaszVinogradovFrequency k x.2 j

noncomputable def halaszRepeatedCount (n k N : ℕ) : ℕ :=
  halaszCrossCount univ univ (halaszRepeatedFrequency n k N)
    (halaszVinogradovFrequency (s := n+2) (N := N) k)

lemma halasz_repeated_phase (n k N : ℕ) (α : Fin k → AddCircle (1:ℝ)) :
    halaszFinitePhase univ (halaszRepeatedFrequency n k N) α =
      halaszScaledPolynomial k N 2 α * (halaszVinogradovPolynomial k N α)^n := by
  let f (x : Fin N) : Fin k → ℤ := fun j => 2*((x.val+1)^(j.val+1):ℕ)
  let g (x : Fin N) : Fin k → ℤ := fun j => ((x.val+1)^(j.val+1):ℕ)
  have h := halasz_finite_phase_product (univ : Finset (Fin N))
    (Fintype.piFinset (fun _ : Fin n => (univ : Finset (Fin N)))) f
    (fun x => ∑ i, g (x i)) α
  rw [halasz_finite_phase_power] at h
  have hf : (fun x : Fin N × (Fin n → Fin N) => f x.1+∑ i, g (x.2 i)) =
      halaszRepeatedFrequency n k N := by
    funext x j
    simp only [Pi.add_apply,Finset.sum_apply,halaszRepeatedFrequency,
      halaszVinogradovFrequency,f,g]
  rw [hf] at h
  simpa only [Fintype.piFinset_univ,univ_product_univ,halaszScaledPolynomial,
    halaszVinogradovPolynomial,halaszFinitePhase,f,g] using h

theorem halasz_repeated_count_bound {s k : ℕ} (hk : 2≤k) (N : ℕ) :
    (halaszRepeatedCount (s+k-2) k N:ℝ) ≤ halaszCollisionMoment s k N := by
  have hn : s+k-2+2=s+k := by omega
  have h := halasz_cross_count_bound (univ : Finset (Fin N × (Fin (s+k-2) → Fin N)))
    (univ : Finset (Fin (s+k-2+2) → Fin N)) (halaszRepeatedFrequency (s+k-2) k N)
    (halaszVinogradovFrequency k)
  simp_rw [halasz_repeated_phase,show ∀ α, halaszFinitePhase univ
      (halaszVinogradovFrequency (s := s+k-2+2) (N := N) k) α =
        (halaszVinogradovPolynomial k N α)^(s+k-2+2) by
    intro α
    exact (halasz_vinogradov_power_expand _ _ _ α).symm,
    norm_mul,norm_pow] at h
  change (halaszRepeatedCount (s+k-2) k N:ℝ) ≤ _ at h
  convert h using 1
  unfold halaszCollisionMoment
  apply integral_congr_ae
  filter_upwards [] with α
  rw [mul_comm,mul_assoc,← pow_add]
  congr 2
  omega

end TwoPointCorrelations

end OAI
