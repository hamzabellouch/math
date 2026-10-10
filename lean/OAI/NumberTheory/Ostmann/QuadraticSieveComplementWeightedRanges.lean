import OAI.NumberTheory.Ostmann.QuadraticSieveWeightedDivisorRanges

namespace OAI

namespace Ostmann.QuadraticSieve
open scoped ArithmeticFunction.Moebius

theorem complement_weight_norm_le {M B H : ℝ} {r D d v : ℕ} (z : ℂ)
    (hM : 0 < M) (hB : 0 < B) (hr : 0 < r) (hD : 0 < D) (hDd : D ≤ d)
    (hv : B ≤ (v : ℝ)) (_hH : 0 ≤ H) (hz : ‖z‖ ≤ H) :
    ‖(μ r : ℂ)*(μ d : ℂ)*((Real.sqrt (M/v)/((r : ℝ)*d) : ℝ) : ℂ)*z‖ ≤
      H*Real.sqrt (M/B)/((r : ℝ)*D) := by
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hdr : (0 : ℝ) < d := by exact_mod_cast hD.trans_le hDd
  have hvr : (0 : ℝ) < v := hB.trans_le hv
  have hs : Real.sqrt (M/v) ≤ Real.sqrt (M/B) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hM.le hB hv)
  have hquot : Real.sqrt (M/v)/((r : ℝ)*d) ≤ Real.sqrt (M/B)/((r : ℝ)*D) := by
    apply div_le_div₀ (Real.sqrt_nonneg _) hs (by positivity)
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hDd) hrr.le
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (M/v)/((r : ℝ)*d))]
  calc
    _ ≤ 1*1*(Real.sqrt (M/B)/((r : ℝ)*D))*H := by
      gcongr
      · exact norm_moebius_complex_le_one r
      · exact norm_moebius_complex_le_one d
    _ = _ := by ring

theorem complementary_weighted_divisor_range_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D N : ℕ) (V S T : Finset ℕ) (a b : ℕ → ℂ) (M B : ℝ),
      0 < D → 0 < N → 0 < M → 0 < B →
      (∀ v ∈ V, Odd v ∧ B ≤ (v : ℝ)) →
      S ⊆ oddSquarefreeUpTo N → T ⊆ oddSquarefreeUpTo N →
      ∃ p ∈ divisorRangeScales D, ∀ (r : ℕ), 0 < r → ∀ (g : ℕ → ℕ → ℂ) (H : ℝ),
        0 ≤ H → (∀ d ∈ Finset.Ioc D (2*D), ∀ v ∈ V, ‖g d v‖ ≤ H) →
        ‖∑ d ∈ Finset.Ioc D (2*D), ∑ v ∈ V,
          (μ r : ℂ)*(μ d : ℂ)*((Real.sqrt (M/v)/((r : ℝ)*d) : ℝ) : ℂ)*g d v*
            coprimeProductDivisorJacobiRow S T a b d (v : ℤ)‖ ≤
          (H*Real.sqrt (M/B)/((r : ℝ)*D))*
            Real.sqrt (C*(N : ℝ)^ε*(p.1*p.2 : ℕ)*
              quadraticNorm V (oddSquarefreeUpTo (N/p.1))*
              quadraticNorm V (oddSquarefreeUpTo (N/p.2))*
              coefficientEnergy S a*coefficientEnergy T b) := by
  obtain ⟨C,hC,hbound⟩ := product_divisor_weighted_range_bound ε hε
  refine ⟨C,hC,?_⟩
  intro D N V S T a b M B hD hN hM hB hV hS hT
  obtain ⟨p,hp,hrow⟩ := hbound D N V S T a b hD hN (fun v hv => (hV v hv).1) hS hT
  refine ⟨p,hp,?_⟩
  intro r hr g H hH hg
  exact hrow (fun d v => (μ r : ℂ)*(μ d : ℂ)*
      ((Real.sqrt (M/v)/((r : ℝ)*d) : ℝ) : ℂ)*g d v)
    (H*Real.sqrt (M/B)/((r : ℝ)*D)) (by positivity)
    (fun d hd v hv => complement_weight_norm_le (g d v) hM hB hr hD
      (Finset.mem_Ioc.mp hd).1.le (hV v hv).2 hH (hg d hd v hv))

end Ostmann.QuadraticSieve

end OAI
