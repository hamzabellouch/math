import OAI.NumberTheory.TwoPoint.Halasz.HalaszFinitePhase

namespace OAI

/-! Averaging the short-variable moment over residue classes. This is
the p^(2s) step in the fundamental complete-system estimate. -/
namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical

lemma halasz_torus_power_sum_bound {ι : Type*} {k : ℕ} (S : Finset ι)
    (F : (Fin k → AddCircle (1:ℝ)) → ℂ)
    (G : ι → (Fin k → AddCircle (1:ℝ)) → ℂ)
    (hF : Continuous F) (hG : ∀ b∈S, Continuous (G b)) (n : ℕ) :
    (∫ α, ‖F α‖^2 * ‖∑ b∈S, G b α‖^(n+1) ∂halaszVinogradovHaar k) ≤
      (S.card:ℝ)^n * ∑ b∈S,
        ∫ α, ‖F α‖^2 * ‖G b α‖^(n+1) ∂halaszVinogradovHaar k := by
  have hi (b : ι) (hb : b∈S) : Integrable
      (fun α => ‖F α‖^2 * ‖G b α‖^(n+1)) (halaszVinogradovHaar k) :=
    halasz_torus_integrable _ ((hF.norm.pow 2).mul ((hG b hb).norm.pow _))
  have hpoint (α : Fin k → AddCircle (1:ℝ)) :
      ‖F α‖^2 * ‖∑ b∈S, G b α‖^(n+1) ≤
        (S.card:ℝ)^n * ∑ b∈S, ‖F α‖^2 * ‖G b α‖^(n+1) := by
    have hs := pow_sum_le_card_mul_sum_pow
      (s := S) (f := fun b => ‖G b α‖) (fun b _ => norm_nonneg (G b α)) n
    have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S (fun b => G b α)) (n+1)
    calc
      _ ≤ ‖F α‖^2 * ((S.card:ℝ)^n * ∑ b∈S, ‖G b α‖^(n+1)) :=
        mul_le_mul_of_nonneg_left (hn.trans hs) (sq_nonneg _)
      _ = _ := by
        simp only [mul_sum]
        apply sum_congr rfl
        intro b _
        ring
  calc
    _ ≤ ∫ α, (S.card:ℝ)^n * ∑ b∈S, ‖F α‖^2 * ‖G b α‖^(n+1)
        ∂halaszVinogradovHaar k := by
      apply integral_mono
      · exact halasz_torus_integrable _ ((hF.norm.pow 2).mul
          ((continuous_finsetSum S hG).norm.pow _))
      · exact (integrable_finsetSum S hi).const_mul _
      · exact hpoint
    _ = _ := by rw [integral_const_mul,integral_finsetSum S hi]

theorem halasz_residue_average_energy {ι κ : Type*} {k p s : ℕ}
    (hs : 0<s) (F : Finset ι) (G : Finset κ) (c : κ → Fin p)
    (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) (B : ℕ)
    (hB : ∀ b : Fin p,
      halaszFiberEnergy (F×ˢFintype.piFinset (fun _ : Fin s => G.filter (fun x => c x=b)))
        (fun x => f x.1+∑ i, g (x.2 i)) ≤ B) :
    halaszFiberEnergy (F×ˢFintype.piFinset (fun _ : Fin s => G))
      (fun x => f x.1+∑ i, g (x.2 i)) ≤ p^(2*s)*B := by
  have hsplit (α : Fin k → AddCircle (1:ℝ)) :
      halaszFinitePhase G g α =
        ∑ b : Fin p, halaszFinitePhase (G.filter (fun x => c x=b)) g α := by
    exact (sum_fiberwise_of_maps_to (s := G) (t := univ) (g := c)
      (fun _ _ => mem_univ _) (fun x => halaszVinogradovCharacter (g x) α)).symm
  have h := halasz_torus_power_sum_bound (univ : Finset (Fin p))
    (halaszFinitePhase F f)
    (fun b => halaszFinitePhase (G.filter (fun x => c x=b)) g)
    (halasz_finite_phase_continuous F f)
    (fun b _ => halasz_finite_phase_continuous _ g) (2*s-1)
  have hexp : 2*s-1+1=2*s := by omega
  simp_rw [hexp,← hsplit,halasz_finite_mixed_moment] at h
  have hb (b : Fin p) :
      (halaszFiberEnergy (F×ˢFintype.piFinset (fun _ : Fin s => G.filter (fun x => c x=b)))
        (fun x => f x.1+∑ i, g (x.2 i)) : ℝ) ≤ B := by
    exact_mod_cast hB b
  have hh := h.trans (mul_le_mul_of_nonneg_left
    (sum_le_sum (fun b _ => hb b)) (by positivity))
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  have hp : (p:ℝ)^(2*s-1)*((p:ℝ)*B)=(p:ℝ)^(2*s)*B := by
    rw [← mul_assoc,← pow_succ,hexp]
  rw [hp] at hh
  exact_mod_cast hh

end TwoPointCorrelations

end OAI
