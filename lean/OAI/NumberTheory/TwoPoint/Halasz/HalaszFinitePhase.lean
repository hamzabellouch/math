import OAI.NumberTheory.TwoPoint.Halasz.HalaszFiberEnergy

namespace OAI

/-! Exact Fourier formulas for the finite energies used when the short
variables are restricted to one residue class. -/
namespace TwoPointCorrelations

open Finset MeasureTheory
open scoped Classical ComplexConjugate

noncomputable def halaszFinitePhase {ι : Type*} {k : ℕ} (F : Finset ι)
    (f : ι → Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) : ℂ :=
  ∑ x∈F, halaszVinogradovCharacter (f x) α

lemma halasz_finite_phase_continuous {ι : Type*} {k : ℕ}
    (F : Finset ι) (f : ι → Fin k → ℤ) : Continuous (halaszFinitePhase F f) := by
  exact continuous_finsetSum F (fun x _ => halasz_vinogradov_character_continuous (f x))

lemma halasz_torus_integrable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {k : ℕ} (f : (Fin k → AddCircle (1:ℝ)) → E) (hf : Continuous f) :
    Integrable f (halaszVinogradovHaar k) :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem halasz_finite_phase_energy {ι : Type*} {k : ℕ} (F : Finset ι)
    (f : ι → Fin k → ℤ) :
    (∫ α, ‖halaszFinitePhase F f α‖^2 ∂halaszVinogradovHaar k) =
      (halaszFiberEnergy F f : ℝ) := by
  have hi (x y : ι) : Integrable (fun α =>
      halaszVinogradovCharacter (f x) α * conj (halaszVinogradovCharacter (f y) α))
      (halaszVinogradovHaar k) := by
    simp_rw [← halasz_vinogradov_character_neg,← halasz_vinogradov_character_add]
    exact halasz_vinogradov_character_integrable _
  have hc : (∫ α, halaszFinitePhase F f α * conj (halaszFinitePhase F f α)
      ∂halaszVinogradovHaar k) = (halaszFiberEnergy F f : ℂ) := by
    unfold halaszFinitePhase
    simp_rw [map_sum,sum_mul,mul_sum]
    rw [integral_finsetSum F (fun x _ => integrable_finsetSum F (fun y _ => hi x y))]
    simp_rw [integral_finsetSum F (fun y _ => hi _ y),halasz_vinogradov_character_inner]
    rw [halasz_fiber_energy_rows,Nat.cast_sum]
    apply sum_congr rfl
    intro x _
    simp only [sum_boole]
    congr 2
    ext y
    simp only [mem_filter]
    exact and_congr_right (fun _ => eq_comm)
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  simpa only [Complex.mul_conj',Complex.ofReal_pow,Complex.ofReal_natCast] using hc

lemma halasz_finite_phase_product {ι κ : Type*} {k : ℕ} (F : Finset ι) (G : Finset κ)
    (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) (α : Fin k → AddCircle (1:ℝ)) :
    halaszFinitePhase (F×ˢG) (fun x => f x.1+g x.2) α =
      halaszFinitePhase F f α * halaszFinitePhase G g α := by
  simp only [halaszFinitePhase,sum_product,halasz_vinogradov_character_add,sum_mul,mul_sum]
  rw [sum_comm]

lemma halasz_finite_phase_power {ι : Type*} {k : ℕ} (F : Finset ι)
    (f : ι → Fin k → ℤ) (s : ℕ) (α : Fin k → AddCircle (1:ℝ)) :
    halaszFinitePhase (Fintype.piFinset (fun _ : Fin s => F))
        (fun x => ∑ i, f (x i)) α = (halaszFinitePhase F f α)^s := by
  rw [halaszFinitePhase,halaszFinitePhase,sum_pow']
  apply sum_congr rfl
  intro x _
  exact halasz_vinogradov_character_sum univ (fun i => f (x i)) α

theorem halasz_finite_mixed_moment {ι κ : Type*} {k : ℕ}
    (F : Finset ι) (G : Finset κ) (f : ι → Fin k → ℤ) (g : κ → Fin k → ℤ) (s : ℕ) :
    (∫ α, ‖halaszFinitePhase F f α‖^2 * ‖halaszFinitePhase G g α‖^(2*s)
      ∂halaszVinogradovHaar k) =
      (halaszFiberEnergy (F×ˢFintype.piFinset (fun _ : Fin s => G))
        (fun x => f x.1+∑ i, g (x.2 i)) : ℝ) := by
  rw [← halasz_finite_phase_energy]
  apply integral_congr_ae
  filter_upwards [] with α
  rw [halasz_finite_phase_product F (Fintype.piFinset (fun _ : Fin s => G)) f
    (fun x => ∑ i, g (x i)),halasz_finite_phase_power,norm_mul,mul_pow,norm_pow]
  congr 1
  rw [← pow_mul,Nat.mul_comm s 2]

end TwoPointCorrelations

end OAI
