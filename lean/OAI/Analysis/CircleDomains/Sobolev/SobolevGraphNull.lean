import OAI.Analysis.CircleDomains.Selection.GraphHausdorffDomination
import OAI.Analysis.CircleDomains.Sobolev.SobolevGraphEnergyRegular
import OAI.Analysis.CircleDomains.Sobolev.SobolevGraphLocalCover

namespace OAI

/-! A continuous compact Sobolev scalar function sends volume-null base
sets to graphs of zero two-dimensional Hausdorff measure. The proof uses
only the constructed local energy covers and measure regularity. -/
open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity

lemma compact_sobolev_graph_null {u : EuclideanPlane → ℝ} (hu : Continuous u)
    (W : DeGiorgi.MemW1pWitness 2 u univ) (hsu : HasCompactSupport u)
    {E : Set EuclideanPlane} (hE : MeasurableSet E) (hnull : volume E = 0) :
    (μH[2] : Measure GraphSpace) (sobolevGraph u '' E) = 0 := by
  obtain ⟨C,hC0,hC,hηd⟩ := exists_capacity_cutoff_derivative_bound
  let μ := sobolevGraphEnergy u W.weakGrad
  let : μ.OuterRegular := sobolevGraphEnergy_outerRegular hu W
  let K : ℝ≥0∞ := 4194304 * ENNReal.ofReal (1+8*C^2)
  have hK : K ≠ ∞ := ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top
  apply graph_hausdorff_zero_of_local_covers μ K hK
  · intro s hs x hx
    obtain ⟨a,ha,rfl⟩ := hx
    exact sobolev_graph_local_cover hu W hsu E a (u a) hs hC0 hC hηd
  · exact sobolevGraphEnergy_null hu W.weakGrad hE hnull

end CircleDomainRigidity

end

end OAI
