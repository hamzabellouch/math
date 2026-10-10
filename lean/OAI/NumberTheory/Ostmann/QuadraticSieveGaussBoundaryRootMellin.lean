import OAI.NumberTheory.Ostmann.QuadraticSieveGaussBoundaryMellin
import OAI.NumberTheory.Ostmann.QuadraticSieveRootGaussCoefficients

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap

theorem rootGauss_mellin_sqrt_boundary_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ), 0 < σ →
      ∀ (N : ℕ) (V S T : Finset ℕ) (a b : ℕ → ℂ) (z : ℤ) (c B L : ℝ),
      0 < N → 0 < L → (∀ v ∈ V, 0 < v ∧ Odd v ∧ (v : ℝ) ≤ B) →
      S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, L ≤ (n : ℝ)) → (∀ t ∈ T, L ≤ (t : ℝ)) → 0 < c → 0 < B →
      (∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T,
        rootGaussMellinKernel a b z 1 v n t *
          ρ (c*Real.sqrt ((n : ℝ)*t)/Real.sqrt v)‖) ≤
        (1/(2*Real.pi))*(∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖)*
          (c/Real.sqrt B)^(-σ)*(2*(N : ℝ)/L)*
          Real.sqrt (C*(N : ℝ)^ε*quadraticNorm V (oddSquarefreeUpTo N)^2*
            coefficientEnergy S a*coefficientEnergy T b) := by
  obtain ⟨C,hC,hmain⟩ := gauss_mellin_boundary_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ρ σ hσ N V S T a b z c B L hN hL hV hS hT hSL hTL hc hB
  have hSpos (n : ℕ) (hn : n ∈ S) : 0 < n := (mem_oddSquarefreeUpTo.mp (hS hn)).1
  have hTpos (t : ℕ) (ht : t ∈ T) : 0 < t := (mem_oddSquarefreeUpTo.mp (hT ht)).1
  have hβ (n : ℕ) (hn : n ∈ S) : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hSpos n hn)
  have hγ (t : ℕ) (ht : t ∈ T) : 0 < Real.sqrt (t : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hTpos t ht)
  have hα (v : ℕ) (hv : v ∈ V) : 0 < c/Real.sqrt v := by
    have hvp : (0:ℝ)<v := by exact_mod_cast (hV v hv).1
    positivity
  have hscale (v : ℕ) (hv : v ∈ V) : (c/Real.sqrt v)^(-σ) ≤ (c/Real.sqrt B)^(-σ) :=
    mellin_outer_sqrt_scale_bound c B σ hc hB hσ.le v (hV v hv).1 (hV v hv).2.2
  have hbound := hmain ρ σ hσ N V S T (sqrtCoefficients a) (sqrtCoefficients b) z
    (fun v => c/Real.sqrt v) (fun n => Real.sqrt n) (fun t => Real.sqrt t)
    ((c/Real.sqrt B)^(-σ)) L hN hL (fun v hv => (hV v hv).2.1)
    hS hT hSL hTL hα hβ hγ (Real.rpow_nonneg (by positivity) _) hscale
  simp_rw [mellin_sqrt_scale_factorization,←rootGaussMellinKernel_eq] at hbound
  apply hbound.trans
  have hEA := mellinWeightedEnergy_sqrtCoefficients_le S a N σ hσ.le
    (fun n hn => ⟨hSpos n hn,(mem_oddSquarefreeUpTo.mp (hS hn)).2.1⟩)
  have hEB := mellinWeightedEnergy_sqrtCoefficients_le T b N σ hσ.le
    (fun t ht => ⟨hTpos t ht,(mem_oddSquarefreeUpTo.mp (hT ht)).2.1⟩)
  have hQ := quadraticNorm_nonneg V (oddSquarefreeUpTo N)
  have hEa := coefficientEnergy_nonneg S a
  have hEb := coefficientEnergy_nonneg T b
  have hbase : 0 ≤ C*(N : ℝ)^ε*
      quadraticNorm V (oddSquarefreeUpTo N)^2 := by positivity
  have hM : 0 ≤ ∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  let R := C*(N : ℝ)^ε*quadraticNorm V (oddSquarefreeUpTo N)^2*coefficientEnergy S a*coefficientEnergy T b
  have hrad : Real.sqrt (C*(N : ℝ)^ε*
      quadraticNorm V (oddSquarefreeUpTo N)^2*
      mellinWeightedEnergy S (sqrtCoefficients a) (fun n => Real.sqrt n) σ*
      mellinWeightedEnergy T (sqrtCoefficients b) (fun t => Real.sqrt t) σ) ≤
      (N : ℝ)*Real.sqrt R := by
    have h := Real.sqrt_le_sqrt (mul_le_mul (mul_le_mul_of_nonneg_left hEA hbase) hEB
      (mellinWeightedEnergy_nonneg _ _ _ _) (by positivity))
    have heq : C*(N : ℝ)^ε*
        quadraticNorm V (oddSquarefreeUpTo N)^2*
        ((N : ℝ)*coefficientEnergy S a)*((N : ℝ)*coefficientEnergy T b) = (N : ℝ)^2*R := by
      dsimp only [R]
      ring
    rw [heq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg N)] at h
    exact h
  have h := mul_le_mul_of_nonneg_left hrad (show 0 ≤
      (1/(2*Real.pi))*(∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖)*
        (c/Real.sqrt B)^(-σ)*(2/L) by positivity)
  convert h using 1
  dsimp only [R]
  ring

end Ostmann.QuadraticSieve

end OAI
