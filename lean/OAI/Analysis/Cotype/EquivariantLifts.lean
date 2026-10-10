import OAI.Analysis.Cotype.PrimalMomentLifts
import OAI.Analysis.Cotype.FiniteL2DualNorm

namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {Γ I X : Type*} [Group Γ] [Fintype Γ] [MulAction Γ I]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

omit [Fintype Γ] in
theorem isometryAction_mul (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (g h : Γ) (z : X) :
    ρ (g*h) z = ρ g (ρ h z) := by rw [map_mul]; rfl

omit [Fintype Γ] in
theorem isometryAction_one (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (z : X) :
    ρ 1 z = z := by rw [map_one]; rfl

def orbitAverage (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (f : I → X) (a : I) : X :=
  average (fun g : Γ => ρ g (f (g⁻¹ • a)))

theorem orbitAverage_equivariant (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (f : I → X)
    (h : Γ) (a : I) : orbitAverage ρ f (h • a) = ρ h (orbitAverage ρ f a) := by
  unfold orbitAverage
  rw [← average_equiv (Equiv.mulLeft h)]
  change average (fun g : Γ => ρ (h*g) (f ((h*g)⁻¹ • (h • a)))) = _
  simp only [mul_inv_rev, mul_smul, inv_smul_smul, isometryAction_mul]
  simp [average, map_smul, map_sum]

theorem orbitAverage_norm_le_one (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (f : I → X)
    (hf : ∀ a, ‖f a‖ ≤ 1) (a : I) : ‖orbitAverage ρ f a‖ ≤ 1 := by
  have hc : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    _ ≤ average (fun g : Γ => ‖ρ g (f (g⁻¹ • a))‖) := norm_average_le _
    _ ≤ average (fun _ : Γ => (1 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun g _ => by simpa using hf (g⁻¹ • a))
    _ = 1 := by simp [average, smul_eq_mul, hc]

theorem orbitAverage_moment {m : ℕ} (ρ : Γ →* (X ≃ₗᵢ[ℝ] X))
    (x : I → Fin m → X) (hx : ∀ h a i, x (h • a) i = ρ h (x a i))
    (c : ℝ) (P : I → Cube m → X)
    (hP : ∀ a i, moment X (P a) i = c • x a i) (a : I) (i : Fin m) :
    moment X (fun ε => orbitAverage ρ (fun b => P b ε) a) i = c • x a i := by
  have hc : (Fintype.card Γ : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have he (g : Γ) : ρ g (moment X (P (g⁻¹ • a)) i) = c • x a i := by
    rw [hP, map_smul, hx]
    rw [← isometryAction_mul, mul_inv_cancel, isometryAction_one]
  calc
    _ = average (fun g : Γ => ρ g (moment X (P (g⁻¹ • a)) i)) := by
      unfold moment orbitAverage
      simp only [average, map_smul, map_sum, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro g _
      apply Finset.sum_congr rfl
      intro ε _
      congr 1
      ring
    _ = c • x a i := by simp [he, average, ← Nat.cast_smul_eq_nsmul ℝ, hc, smul_smul]

theorem exists_equivariant_primal_lifts [CompleteSpace X] {m : ℕ} (hm : 0 < m)
    {D : ℝ} (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) (hDone : 1 ≤ D)
    (ρ : Γ →* (X ≃ₗᵢ[ℝ] X)) (x : I → Fin m → X)
    (hx : ∀ a i, ‖x a i‖ ≤ 1) (he : ∀ h a i, x (h • a) i = ρ h (x a i)) :
    ∃ P : I → Cube m → X, (∀ a ε, ‖P a ε‖ ≤ 1) ∧
      (∀ a i, moment X (P a) i = (1 / (2*24*D*Real.sqrt m)) • x a i) ∧
      ∀ h a ε, P (h • a) ε = ρ h (P a ε) := by
  choose P hn hp using (fun a => exists_primal_moment_lift hm hD hDone (x a) (hx a))
  exact ⟨fun a ε => orbitAverage ρ (fun b => P b ε) a,
    fun a ε => orbitAverage_norm_le_one ρ _ (fun b => hn b ε) a,
    orbitAverage_moment ρ x he _ P hp,
    fun h a ε => orbitAverage_equivariant ρ _ h a⟩

theorem exists_equivariant_dual_lifts {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {m : ℕ} (hm : 0 < m) {D : ℝ} (hD : FixedCotypeBound Y m D) (hDone : 1 ≤ D)
    (ρ : Γ →* ((Y →L[ℝ] ℝ) ≃ₗᵢ[ℝ] (Y →L[ℝ] ℝ)))
    (y : I → Fin m → (Y →L[ℝ] ℝ)) (hy : ∀ a i, ‖y a i‖ ≤ 1)
    (he : ∀ h a i, y (h • a) i = ρ h (y a i)) :
    ∃ Z : I → Cube m → (Y →L[ℝ] ℝ), (∀ a ε, ‖Z a ε‖ ≤ 1) ∧
      (∀ a i, moment (Y →L[ℝ] ℝ) (Z a) i = (1 / (2*24*D*Real.sqrt m)) • y a i) ∧
      ∀ h a ε, Z (h • a) ε = ρ h (Z a ε) := by
  choose Z hn hp using (fun a => exists_dual_moment_lift hm hD hDone (y a) (hy a))
  exact ⟨fun a ε => orbitAverage ρ (fun b => Z b ε) a,
    fun a ε => orbitAverage_norm_le_one ρ _ (fun b => hn b ε) a,
    orbitAverage_moment ρ y he _ Z hp,
    fun h a ε => orbitAverage_equivariant ρ _ h a⟩

end Cotype

end

end OAI
