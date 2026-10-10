import OAI.Analysis.IrrationalRotation.Product.ProductCocycleWindow
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences

namespace OAI

noncomputable section
open scoped BigOperators ComplexConjugate lp

namespace Invariant233.ProductScaleData

def earlyCoordinates (p : ProductScaleData) (e : ℕ ≃ Σ s, Fin (p.m s))
    (j : ℕ) : Finset ℕ :=
  ((Finset.range j).sigma (fun s => (Finset.univ : Finset (Fin (p.m s))))).map
    e.symm.toEmbedding

@[simp] theorem mem_earlyCoordinates (p : ProductScaleData)
    (e : ℕ ≃ Σ s, Fin (p.m s)) (j i : ℕ) :
    i ∈ p.earlyCoordinates e j ↔ (e i).1 < j := by
  simp [earlyCoordinates]

theorem sum_earlyCoordinates_cost (p : ProductScaleData)
    (e : ℕ ≃ Σ s, Fin (p.m s)) (j : ℕ) :
    (∑ i ∈ p.earlyCoordinates e j, p.C (e i).1) = p.prefixCost j := by
  simp [earlyCoordinates, Finset.sum_sigma, prefixCost, mul_comm]

end Invariant233.ProductScaleData

namespace Invariant233.ProductScaleLaws
variable {p : ProductScaleData} (hp : ProductScaleLaws p)
include hp

theorem current_window_margin (j : ℕ) :
    2 * (p.K j : ℝ) / p.N j = 2 / (p.m j : ℝ) := by
  have hK : (p.K j : ℝ) ≠ 0 := (hp.real_K_pos j).ne'
  have hm : (p.m j : ℝ) ≠ 0 := by exact_mod_cast (hp.m_pos j).ne'
  unfold ProductScaleData.N
  field_simp

theorem product_finite_window_coefficients
    (e : ℕ ≃ Σ s, Fin (p.m s)) (θ : ℕ → ℝ)
    (hphase : ∀ i, θ i ∈ Set.Icc (1 / p.N (e i).1) (2 / p.N (e i).1))
    (j : ℕ) (x y : ProductCocycle.Space ℕ)
    (hcurrent : ∀ i, (e i).1 = j →
      ProductCocycle.representative (x i) < 1 - 2 / (p.m j : ℝ) ∧
        2 / (p.m j : ℝ) < ProductCocycle.representative (y i))
    (hfuture : ∀ i, j < (e i).1 →
      ProductCocycle.representative (x i) < 1 - 2 * (p.K j : ℝ) / p.N (e i).1 ∧
        2 * (p.K j : ℝ) / p.N (e i).1 < ProductCocycle.representative (y i))
    (ξ γ : ℓ²(ℤ, ℂ)) (hξ : ‖ξ‖ ≤ 1) (hγ : ‖γ‖ ≤ 1) :
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖ξ v / (ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) v x : ℂ)‖ ≤
        p.coefficientBound j) ∧
    (∀ v : ℤ, |v| ≤ (p.K j : ℤ) →
      ‖(ProductCocycle.cocycleVersion θ (fun i => p.C (e i).1) (-v) y : ℂ) *
        conj (γ (-v))‖ ≤ p.coefficientBound j) := by
  have hN (s : ℕ) : 2 ≤ p.N s := by
    have hm : (100 : ℝ) ≤ p.m s := by exact_mod_cast hp.m_ge_100 s
    have hK : (1 : ℝ) ≤ p.K s := by exact_mod_cast hp.K_pos s
    dsimp [ProductScaleData.N]
    nlinarith
  have hθ (i : ℕ) : θ i ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · exact (div_nonneg (by norm_num) (by linarith [hN (e i).1])).trans (hphase i).1
    · exact (hphase i).2.trans ((div_le_one (by linarith [hN (e i).1])).mpr (hN _))
  have hexclude (i : ℕ) (hi : i ∉ p.earlyCoordinates e j) :
      ProductCocycle.representative (x i) + (p.K j : ℝ) * θ i < 1 ∧
      (p.K j : ℝ) * θ i ≤ ProductCocycle.representative (y i) := by
    have htag : j ≤ (e i).1 := by simpa only [p.mem_earlyCoordinates, not_lt] using hi
    have hevent : ProductCocycle.representative (x i) < 1 - 2 * (p.K j : ℝ) / p.N (e i).1 ∧
        2 * (p.K j : ℝ) / p.N (e i).1 < ProductCocycle.representative (y i) := by
      rcases eq_or_lt_of_le htag with h | h
      · simpa only [← h, hp.current_window_margin] using hcurrent i h.symm
      · exact hfuture i h
    have hmul := mul_le_mul_of_nonneg_left (hphase i).2 (Nat.cast_nonneg (p.K j))
    have hbound : (p.K j : ℝ) * θ i ≤ 2 * (p.K j : ℝ) / p.N (e i).1 := by
      calc
        _ ≤ (p.K j : ℝ) * (2 / p.N (e i).1) := hmul
        _ = _ := by ring
    constructor
    · linarith [hevent.1]
    · exact hbound.trans hevent.2.le
  have h := ProductCocycle.finite_window_coefficients (p.earlyCoordinates e j)
    θ (fun i => p.C (e i).1) (p.K j) x y hθ (fun i => (hp.C_pos _).le)
    (fun i hi => (hexclude i hi).1) (fun i hi => (hexclude i hi).2) ξ γ hξ hγ
  simpa only [p.sum_earlyCoordinates_cost, ProductScaleData.coefficientBound] using h

end Invariant233.ProductScaleLaws

end

end OAI
