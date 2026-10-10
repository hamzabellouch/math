import OAI.NumberTheory.Ostmann.QuadraticSieveRootGaussCoefficients

namespace OAI

namespace Ostmann.QuadraticSieve
open MeasureTheory
open scoped SchwartzMap

theorem rootGauss_mellin_sqrt_divisor_range_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (ρ : 𝓢(ℝ, ℂ)) (σ : ℝ), 0 < σ →
      ∀ (D N : ℕ) (V S T : Finset ℕ) (a b : ℕ → ℂ) (z : ℤ) (c B L : ℝ),
      0 < D → 0 < N → 0 < L → (∀ v ∈ V, 0 < v ∧ Odd v ∧ (v : ℝ) ≤ B) →
      S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, L ≤ (n : ℝ)) → (∀ t ∈ T, L ≤ (t : ℝ)) → 0 < c → 0 < B →
      ∃ p ∈ divisorRangeScales D,
        (∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V, ‖∑ n ∈ S, ∑ t ∈ T,
          rootGaussMellinKernel a b z d v n t *
            ρ (c*Real.sqrt ((n : ℝ)*t)/((d : ℝ)*Real.sqrt v))‖) ≤
          (1/(2*Real.pi))*(∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖)*
            (c/((2*D : ℕ)*Real.sqrt B))^(-σ)*(2*(N : ℝ)/L)*
            Real.sqrt (C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
              quadraticNorm V (oddSquarefreeUpTo (N/p.1))*
              quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
              coefficientEnergy S a*coefficientEnergy T b) := by
  obtain ⟨C,hC,hmain⟩ := gauss_mellin_divisor_range_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ρ σ hσ D N V S T a b z c B L hD hN hL hV hS hT hSL hTL hc hB
  have hSpos (n : ℕ) (hn : n ∈ S) : 0 < n := (mem_oddSquarefreeUpTo.mp (hS hn)).1
  have hTpos (t : ℕ) (ht : t ∈ T) : 0 < t := (mem_oddSquarefreeUpTo.mp (hT ht)).1
  have hβ (n : ℕ) (hn : n ∈ S) : 0 < Real.sqrt (n : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hSpos n hn)
  have hγ (t : ℕ) (ht : t ∈ T) : 0 < Real.sqrt (t : ℝ) :=
    Real.sqrt_pos.mpr (by exact_mod_cast hTpos t ht)
  have hα (d : ℕ) (hd : d ∈ Finset.Ioc D (2*D)) (v : ℕ) (hv : v ∈ V) :
      0 < c/((d : ℝ)*Real.sqrt v) := by
    have hdp : (0 : ℝ) < d := by exact_mod_cast hD.trans (Finset.mem_Ioc.mp hd).1
    have hvp : (0 : ℝ) < v := by exact_mod_cast (hV v hv).1
    positivity
  have hscale (d : ℕ) (hd : d ∈ Finset.Ioc D (2*D)) (v : ℕ) (hv : v ∈ V) :
      (c/((d : ℝ)*Real.sqrt v))^(-σ) ≤ (c/((2*D : ℕ)*Real.sqrt B))^(-σ) := by
    have hdp : (0 : ℝ) < d := by exact_mod_cast hD.trans (Finset.mem_Ioc.mp hd).1
    have hvp : (0 : ℝ) < v := by exact_mod_cast (hV v hv).1
    have hD2 : (0 : ℝ) < (2*D : ℕ) := by exact_mod_cast (show 0 < 2*D by omega)
    apply Real.rpow_le_rpow_of_nonpos (by positivity) _ (neg_nonpos.mpr hσ.le)
    apply div_le_div_of_nonneg_left hc.le (by positivity)
    exact mul_le_mul (by exact_mod_cast (Finset.mem_Ioc.mp hd).2)
      (Real.sqrt_le_sqrt (hV v hv).2.2) (Real.sqrt_nonneg _) hD2.le
  obtain ⟨p,hp,hbound⟩ := hmain ρ σ hσ D N V S T (sqrtCoefficients a) (sqrtCoefficients b) z
    (fun d v => c/((d : ℝ)*Real.sqrt v)) (fun n => Real.sqrt n) (fun t => Real.sqrt t)
    ((c/((2*D : ℕ)*Real.sqrt B))^(-σ)) L hD hN hL (fun v hv => (hV v hv).2.1)
    hS hT hSL hTL hα hβ hγ (Real.rpow_nonneg (by positivity) _) hscale
  refine ⟨p,hp,?_⟩
  have harg (d v n t : ℕ) : c/((d : ℝ)*Real.sqrt v)*Real.sqrt n*Real.sqrt t =
      c*Real.sqrt ((n : ℝ)*t)/((d : ℝ)*Real.sqrt v) := by
    rw [Real.sqrt_mul (Nat.cast_nonneg n)]
    ring
  simp_rw [harg,←rootGaussMellinKernel_eq] at hbound
  apply hbound.trans
  have hEA := mellinWeightedEnergy_sqrtCoefficients_le S a N σ hσ.le
    (fun n hn => ⟨hSpos n hn,(mem_oddSquarefreeUpTo.mp (hS hn)).2.1⟩)
  have hEB := mellinWeightedEnergy_sqrtCoefficients_le T b N σ hσ.le
    (fun t ht => ⟨hTpos t ht,(mem_oddSquarefreeUpTo.mp (hT ht)).2.1⟩)
  have hQA := quadraticNorm_nonneg V (oddSquarefreeUpTo (N/p.1))
  have hQB := quadraticNorm_nonneg V (oddSquarefreeUpTo (N/p.2))
  have hEa := coefficientEnergy_nonneg S a
  have hEb := coefficientEnergy_nonneg T b
  have hbase : 0 ≤ C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
      quadraticNorm V (oddSquarefreeUpTo (N/p.1))*quadraticNorm V (oddSquarefreeUpTo (N/p.2)) := by positivity
  have hM : 0 ≤ ∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖ :=
    integral_nonneg (fun _ => norm_nonneg _)
  let R := C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*quadraticNorm V (oddSquarefreeUpTo (N/p.1))*
    quadraticNorm V (oddSquarefreeUpTo (N/p.2))*coefficientEnergy S a*coefficientEnergy T b
  have hrad : Real.sqrt (C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
      quadraticNorm V (oddSquarefreeUpTo (N/p.1))*quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
      mellinWeightedEnergy S (sqrtCoefficients a) (fun n => Real.sqrt n) σ*
      mellinWeightedEnergy T (sqrtCoefficients b) (fun t => Real.sqrt t) σ) ≤
      (N : ℝ)*Real.sqrt R := by
    have h := Real.sqrt_le_sqrt (mul_le_mul (mul_le_mul_of_nonneg_left hEA hbase) hEB
      (mellinWeightedEnergy_nonneg _ _ _ _) (by positivity))
    have heq : C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
        quadraticNorm V (oddSquarefreeUpTo (N/p.1))*quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
        ((N : ℝ)*coefficientEnergy S a)*((N : ℝ)*coefficientEnergy T b) = (N : ℝ)^2*R := by
      dsimp only [R]
      ring
    rw [heq,Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (Nat.cast_nonneg N)] at h
    exact h
  have h := mul_le_mul_of_nonneg_left hrad (show 0 ≤
      (1/(2*Real.pi))*(∫ r : ℝ, ‖mellin (ρ : ℝ → ℂ) (σ+r*Complex.I)‖)*
        (c/((2*D : ℕ)*Real.sqrt B))^(-σ)*(2/L) by positivity)
  convert h using 1; dsimp only [R]; ring

end Ostmann.QuadraticSieve

end OAI
