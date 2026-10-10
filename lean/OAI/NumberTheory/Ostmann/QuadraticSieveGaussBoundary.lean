import OAI.NumberTheory.Ostmann.QuadraticSieveGaussRows
import OAI.NumberTheory.Ostmann.QuadraticSieveGcdSeparationSelection

namespace OAI

namespace Ostmann.QuadraticSieve

theorem gauss_coefficients_boundary_bound (V S T : Finset ℕ)
    (a b : ℕ → ℂ) (c : ℤ) {F L : ℝ} (hF : 0 ≤ F) (hL : 0 < L)
    (hS : ∀ n ∈ S, L ≤ (n : ℝ)) (hT : ∀ t ∈ T, L ≤ (t : ℝ))
    (hbound : (∑ v ∈ V,
      ‖coprimeProductDivisorJacobiRow S T (gaussRowCoefficients c a)
        (gaussRowCoefficients c b) 1 (v : ℤ)‖)^2 ≤
      F*coefficientEnergy S (gaussRowCoefficients c a)*coefficientEnergy T (gaussRowCoefficients c b)) :
    (∑ v ∈ V,
      ‖coprimeProductDivisorJacobiRow S T (gaussRowCoefficients c a)
        (gaussRowCoefficients c b) 1 (v : ℤ)‖) ≤
      Real.sqrt (F*coefficientEnergy S a*coefficientEnergy T b)/L := by
  have hA := coefficientEnergy_gaussRowCoefficients_le S a c hL hS
  have hB := coefficientEnergy_gaussRowCoefficients_le T b c hL hT
  have ha0 := coefficientEnergy_nonneg S a
  have hb0 := coefficientEnergy_nonneg T b
  have hA0 := coefficientEnergy_nonneg S (gaussRowCoefficients c a)
  have hB0 := coefficientEnergy_nonneg T (gaussRowCoefficients c b)
  have hsum0 : 0 ≤ ∑ v ∈ V,
      ‖coprimeProductDivisorJacobiRow S T (gaussRowCoefficients c a)
        (gaussRowCoefficients c b) 1 (v : ℤ)‖ :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  apply (sq_le_sq₀ hsum0 (by positivity)).mp
  rw [div_pow,Real.sq_sqrt (by positivity)]
  apply hbound.trans
  calc
    _ ≤ F*(coefficientEnergy S a/L)*(coefficientEnergy T b/L) := by gcongr
    _ = _ := by ring

theorem gauss_product_boundary_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (V S T : Finset ℕ) (L : ℝ),
      0 < N → 0 < L → (∀ v ∈ V, Odd v) →
      S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      (∀ n ∈ S, L ≤ (n : ℝ)) → (∀ t ∈ T, L ≤ (t : ℝ)) →
      ∀ (a b : ℕ → ℂ) (c : ℤ),
        (∑ v ∈ V, ‖gaussProductDivisorJacobiRow S T a b c 1 (v : ℤ)‖) ≤
          (2/L)*Real.sqrt (C*(N : ℝ)^ε*quadraticNorm V (oddSquarefreeUpTo N)^2*
            coefficientEnergy S a*coefficientEnergy T b) := by
  obtain ⟨C,hC,hsep⟩ := exists_gcd_separation_scales ε hε
  refine ⟨C,hC,?_⟩
  intro N V S T L hN hL hV hS hT hSL hTL a b c
  let F : ℝ := C*(N:ℝ)^ε*quadraticNorm V (oddSquarefreeUpTo N)^2
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hall (A B : ℕ → ℂ) :
      (∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T A B 1 (v:ℤ)‖)^2 ≤
        F*coefficientEnergy S A*coefficientEnergy T B := by
    obtain ⟨d₁,d₂,hd₁,hd₂,heq,hbound⟩ := hsep V S T A B 1 N (by norm_num) hV hS hT
    have he₁ : d₁=1 := Nat.dvd_one.mp ⟨d₂,heq.symm⟩
    have he₂ : d₂=1 := by simpa only [he₁,one_mul] using heq
    subst d₁
    subst d₂
    simpa only [F,Nat.div_one,pow_two,mul_assoc] using hbound
  have htwist (z : ℤ) := gauss_coefficients_boundary_bound V S T a b z hF hL hSL hTL
    (hall (gaussRowCoefficients z a) (gaussRowCoefficients z b))
  have hSsf (n : ℕ) (hn : n ∈ S) : Odd n ∧ Squarefree n := (mem_oddSquarefreeUpTo.mp (hS hn)).2.2
  have hTsf (t : ℕ) (ht : t ∈ T) : Odd t ∧ Squarefree t := (mem_oddSquarefreeUpTo.mp (hT ht)).2.2
  calc
    _ ≤ ∑ v ∈ V,
        (‖coprimeProductDivisorJacobiRow S T (gaussRowCoefficients c a)
          (gaussRowCoefficients c b) 1 (v : ℤ)‖ +
        ‖coprimeProductDivisorJacobiRow S T (gaussRowCoefficients (-c) a)
          (gaussRowCoefficients (-c) b) 1 (v : ℤ)‖) := by
      apply Finset.sum_le_sum
      intro v hv
      rw [gaussProductDivisorJacobiRow_eq_two_rows S T a b c 1 v hSsf hTsf]
      apply (norm_add_le _ _).trans
      simp only [norm_mul]
      exact add_le_add
        ((mul_le_mul_of_nonneg_right norm_gaussPhaseA_le_one (norm_nonneg _)).trans_eq (one_mul _))
        ((mul_le_mul_of_nonneg_right norm_gaussPhaseB_le_one (norm_nonneg _)).trans_eq (one_mul _))
    _ = (∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T (gaussRowCoefficients c a)
        (gaussRowCoefficients c b) 1 (v:ℤ)‖) +
        (∑ v ∈ V, ‖coprimeProductDivisorJacobiRow S T (gaussRowCoefficients (-c) a)
        (gaussRowCoefficients (-c) b) 1 (v:ℤ)‖) := Finset.sum_add_distrib
    _ ≤ Real.sqrt (F*coefficientEnergy S a*coefficientEnergy T b)/L +
        Real.sqrt (F*coefficientEnergy S a*coefficientEnergy T b)/L := add_le_add (htwist c) (htwist (-c))
    _ = _ := by dsimp only [F]; ring

end Ostmann.QuadraticSieve

end OAI
