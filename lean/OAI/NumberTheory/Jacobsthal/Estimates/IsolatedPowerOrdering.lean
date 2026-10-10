import OAI.NumberTheory.Jacobsthal.Partitions.GeometricInverseGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.IsolatedPowerOrdering
open LogarithmicBinScale LogarithmicBinLabels LogarithmicBinEndpoints PrimeBinRepresentatives
open GeometricBinOrdering BoundedEdgeBins BoundedEdgePrimeRange


theorem source_power_before_edge {w top xi B alpha M X : ℝ} {Y : ℕ}
    (hw : 1 < w) (htop : w < top) (hxi : 0 < xi) (hpower : w^B=top)
    (m : Fin (binCount w top xi) → ℕ) (i j : Fin (binCount w top xi))
    (hi : top^alpha ≤ lower w top xi i) (hj : boundedEdgeBin w top xi Y m M X j)
    (hlarge : X < alpha*B) : j < i := by
  have htop0 : 0 < top := (zero_lt_one.trans hw).trans htop
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos htop0 alpha) hi
  rw [Real.log_rpow htop0] at hlog
  have ht : Real.log top=B*Real.log w := by rw [← hpower,Real.log_rpow (zero_lt_one.trans hw)]
  rw [ht] at hlog
  have hlow : alpha*B ≤ leftExponent w (lower w top xi i) := by
    apply (le_div_iff₀ (Real.log_pos hw)).mpr
    nlinarith
  by_contra! hle
  have hh := left_exponent_mono hw htop hxi i j hle
  have hb := bounded_edge_lower_exponent hw htop hxi m j hj
  linarith
end NumberTheoryLean.IsolatedPowerOrdering


end Erdos970

end OAI
