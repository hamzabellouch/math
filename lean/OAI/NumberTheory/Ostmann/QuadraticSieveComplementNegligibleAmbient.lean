import OAI.NumberTheory.Ostmann.QuadraticSieveComplementNegligible
import OAI.NumberTheory.Ostmann.QuadraticSievePoissonDecayOrder

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped SchwartzMap

theorem complementaryCorrelation_negligible_ambient (W : 𝓢(ℝ, ℂ)) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ (M P : ℝ) (K Δ N : ℕ) (S : Finset ℕ) (a : ℕ → ℂ),
      1 ≤ M → M ≤ P → 1 ≤ P → (N : ℝ) ≤ P → (K : ℝ) ≤ P^3 → Δ ≠ 0 →
      (∀ n ∈ S, 0 < n ∧ n ≤ N) →
      ‖complementaryCorrelation W M K Δ S a -
        complementaryCorrelationMain W M K Δ S a
          (complementWindowLower M (P^η))
          (complementWindowUpper M (P^η)) (fun _ => 16*(P^η)^2)‖ ≤
        C*coefficientEnergy S a := by
  obtain ⟨A,hA⟩ := poisson_decay_absorbs_polynomial η 5 hη
  obtain ⟨C,hC,hbound⟩ := complementaryCorrelation_window_error W A
  refine ⟨C,hC,?_⟩
  intro M P K Δ N S a hM hMle hP hNle hK hΔ hS
  have hMp : 0 < M := by linarith
  have hT : 1 ≤ P^η := Real.one_le_rpow hP hη.le
  have hsqrt : Real.sqrt M ≤ P := (Real.sqrt_le_self_iff.mpr (Or.inr hM)).trans hMle
  have hpoly : (N : ℝ)*K*Real.sqrt M ≤ P^(5 : ℝ) := by
    calc
      _ ≤ P*P^3*P := by gcongr
      _ = P^5 := by ring
      _ = _ := (Real.rpow_natCast _ _).symm
  have habs := hA P ((N : ℝ)*K*Real.sqrt M) hP hpoly
  have h := hbound M (P^η) K Δ N S a hMp hT hΔ hS
  apply h.trans
  have hE := coefficientEnergy_nonneg S a
  calc
    C*(N : ℝ)*K*Real.sqrt M/(P^η)^A*coefficientEnergy S a =
        C*((N : ℝ)*K*Real.sqrt M/(P^η)^A)*coefficientEnergy S a := by ring
    _ ≤ C*1*coefficientEnergy S a := by gcongr
    _ = _ := by ring

end Ostmann.QuadraticSieve

end OAI
