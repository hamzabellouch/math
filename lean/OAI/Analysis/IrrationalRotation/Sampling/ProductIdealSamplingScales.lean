import OAI.Analysis.IrrationalRotation.Sampling.ProductIdealSamplingLimit
import OAI.Analysis.IrrationalRotation.Product.ProductScaleConsequences

namespace OAI

noncomputable section
open Filter
open scoped Topology

namespace Invariant233.ProductModel.IdealSampling

theorem scale_m_tendsto_atTop {p : ProductScaleData} (hp : ProductScaleLaws p) :
    Tendsto p.m atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop b] with n hn
  have hn2 : n + 1 < 2 ^ (n + 1) := Nat.lt_two_pow_self
  have hnm := hp.m_ge_pow n
  omega

theorem law_weaklyConverges_of_productScaleLaws (I : Finset ℕ)
    {p : ProductScaleData} (hp : ProductScaleLaws p) :
    WeaklyConverges (fun l => law I (Finset.range (p.prefixCount (l + 1)))
      ((p.m l : ℝ) ^ (-(3 / 5 : ℝ))) (1 / (p.m l : ℝ) ^ 2)) (triangularLaw I) := by
  apply law_weaklyConverges_of_linear_dimension I _ p.m
    (fun l => (hp.m_pos l)) (scale_m_tendsto_atTop hp) (C := 101 / 100)
  intro l
  simpa only [Finset.card_range] using hp.prefix_count_succ_le l

end Invariant233.ProductModel.IdealSampling

end

end OAI
