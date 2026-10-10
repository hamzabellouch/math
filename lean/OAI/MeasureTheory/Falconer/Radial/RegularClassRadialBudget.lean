import OAI.MeasureTheory.Falconer.Incidence.RegularClassRadialIncidence
import OAI.MeasureTheory.Falconer.Radial.WeakRadialLocalBudget

namespace OAI

/-! # Uniform profile cancellation in the actual class ball bound -/

namespace Falconer.Regularization
open MeasureTheory
variable {n : ℕ}

theorem radialClassBallBound_le (Q : DyadicCube (n+1)) (μ : Measure (Space (n+1)))
    (N B : ℕ) (p : CellPath (n+1)) (a b : ℕ) (lam τ : ℝ)
    (hC : ((2*Nat.ceil (2*((n+1:ℕ):ℝ)^2+2+4*Real.sqrt (n+1:ℕ))+1)^(n+1):ℕ) ≤
      ((2:ℝ)^N)^(τ-2*(((n+1:ℕ):ℝ)+1)*lam)) :
    radialClassBallBound Q μ N B p a b lam ≤
      ((2:ℝ)^N)^τ / ((2:ℝ)^N)^(sourceProfile Q μ N B p b-sourceProfile Q μ N B p a) := by
  have hR : 0 < (2:ℝ)^N := by positivity
  unfold radialClassBallBound
  calc
    _ ≤ ((2:ℝ)^N)^(τ-2*(((n+1:ℕ):ℝ)+1)*lam) *
        ((2:ℝ)^N)^(sourceProfile Q μ N B p a-sourceProfile Q μ N B p b+
          2*(((n+1:ℕ):ℝ)+1)*lam) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hR.le _)
    _ = _ := by
      rw [← Real.rpow_add hR,← Real.rpow_sub hR]
      congr 1
      ring

theorem eventually_radialClassBallBound_le (n : ℕ) {lam τ : ℝ}
    (hτ : 2*(((n+1:ℕ):ℝ)+1)*lam < τ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (Q : DyadicCube (n+1)) (μ : Measure (Space (n+1)))
      (B : ℕ) (p : CellPath (n+1)) (a b : ℕ),
      radialClassBallBound Q μ N B p a b lam ≤
        ((2:ℝ)^N)^τ / ((2:ℝ)^N)^(sourceProfile Q μ N B p b-sourceProfile Q μ N B p a) := by
  obtain ⟨N₀,hN₀⟩ := fixed_constant_absorbed (sub_pos.mpr hτ)
    (((2*Nat.ceil (2*((n+1:ℕ):ℝ)^2+2+4*Real.sqrt (n+1:ℕ))+1)^(n+1):ℕ):ℝ)
  exact ⟨N₀,fun N hN Q μ B p a b => radialClassBallBound_le Q μ N B p a b lam τ (hN₀ N hN)⟩

end Falconer.Regularization

namespace Falconer

theorem weak_radial_reciprocal_count {R D : ℝ} (hR : 0 < R) (hD : 0 < D)
    (n : ℕ) (K G e τ η : ℝ) :
    (K/(R^e/D^((n:ℝ)/(n+1))))^(n+1)*
      (G/(R^(-η))^(n+1))^(n*(n+1))*(R^τ/D)^n =
    (K^(n+1)*G^(n*(n+1)))*R^(-((n+1)*e-n*τ-η*n*(n+1)^2)) := by
  have hh := weak_radial_local_count_power (inv_pos.mpr hR) hD n K G e τ η
  simp only [Real.inv_rpow hR.le,← Real.rpow_neg hR.le,neg_neg] at hh
  exact hh

theorem eventually_weak_radial_reciprocal_budget (n : ℕ) (K G e τ η u : ℝ)
    (hgap : 0 < (n+1)*e-n*τ-η*n*(n+1)^2-n*u) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ D > 0,
      (K/(((2:ℝ)^N)^e/D^((n:ℝ)/(n+1))))^(n+1)*
        (G/(((2:ℝ)^N)^(-η))^(n+1))^(n*(n+1))*(((2:ℝ)^N)^τ/D)^n ≤
          (((2:ℝ)^N)^(-u))^n := by
  let A : ℝ := K^(n+1)*G^(n*(n+1))
  let gap : ℝ := (n+1)*e-n*τ-η*n*(n+1)^2-n*u
  obtain ⟨N₀,hN₀⟩ := Regularization.fixed_constant_absorbed hgap A
  refine ⟨N₀,fun N hN D hD => ?_⟩
  have hR : 0 < (2:ℝ)^N := by positivity
  rw [weak_radial_reciprocal_count hR hD]
  calc
    _ ≤ ((2:ℝ)^N)^gap*((2:ℝ)^N)^(-((n+1)*e-n*τ-η*n*(n+1)^2)) :=
      mul_le_mul_of_nonneg_right (hN₀ N hN) (Real.rpow_nonneg hR.le _)
    _ = _ := by
      rw [← Real.rpow_add hR,← Real.rpow_natCast (((2:ℝ)^N)^(-u)) n,
        ← Real.rpow_mul hR.le]
      congr 1
      dsimp [gap]
      ring

end Falconer

end OAI
