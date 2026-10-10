import OAI.Analysis.IrrationalRotation.Model.ProductCoupling

namespace OAI

noncomputable section
namespace Invariant233.OrderedProductCoupling

def sourceKappa (s : ℕ) : ℝ := 1 / (100 * ((s : ℝ) + 1))

def ofBlocks (m : ℕ → ℕ) (κ a b : ℕ → ℝ)
    (hκ0 : ∀ s, 0 ≤ κ s) (hκ : ∀ s, κ s ≤ 1 / 100)
    (hm : ∀ s, 100 ≤ m s)
    (ha : ∀ s, 1 / (m s : ℝ) ≤ a s) (ha' : ∀ s, a s ≤ 1 / 4)
    (hb : ∀ s, 1 / (m s : ℝ) ≤ b s) (hb' : ∀ s, b s ≤ 1 / 4)
    (e : ℕ ≃ Σ s, Fin (m s)) (tag : ℕ) : Parameters where
  κ i := κ (e i).1
  m i := m (e i).1
  a i := a (e i).1
  b i := b (e i).1
  t i := if (e i).1 = tag then 1 else 0
  κ_nonneg i := hκ0 (e i).1
  κ_le i := hκ (e i).1
  m_ge i := by exact_mod_cast hm (e i).1
  a_lower i := ha (e i).1
  a_upper i := ha' (e i).1
  b_lower i := hb (e i).1
  b_upper i := hb' (e i).1
  t_nonneg i := by split_ifs <;> norm_num
  t_le i := by split_ifs <;> norm_num

def blockDensityBound (κ : ℕ → ℝ) : ℝ :=
  Real.exp (10 * (2 * (∑' s, κ s ^ 2) + 1))

end Invariant233.OrderedProductCoupling

end

end OAI
