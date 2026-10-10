import OAI.NumberTheory.Jacobsthal.Partitions.CrossingBandGeometry

namespace OAI

namespace Erdos970
open scoped _root_.Erdos970


namespace NumberTheoryLean.IsolatedRealPrimeRange
open LogarithmicBinScale LogarithmicBinEndpoints PrimeBinRepresentatives IsolatedBinGeometry

theorem isolated_real_range {w top xi B alpha beta : ℝ} (hw : 1 < w) (htop : w < top)
    (hxi : 0 < xi) (hpower : w^B=top) {b : Fin (binCount w top xi)}
    (hb : isolatedBin w top xi B alpha beta b) :
    top^alpha ≤ lower w top xi b ∧ upper w top xi b ≤ top^beta := by
  have hw0 : 0 < w := zero_lt_one.trans hw
  have htop0 : 0 < top := hw0.trans htop
  have hlow : 0 < lower w top xi b := endpoint_pos hw0 _
  have hupp : 0 < upper w top xi b := hlow.trans (bin_source_bounds hw0 htop hxi b).2.1
  have hlog : Real.log top=B*Real.log w := by rw [← hpower,Real.log_rpow hw0]
  have hlo : alpha*B*Real.log w ≤ Real.log (lower w top xi b) :=
    (le_div_iff₀ (Real.log_pos hw)).mp hb.1
  have hhi : Real.log (upper w top xi b) ≤ beta*B*Real.log w :=
    (div_le_iff₀ (Real.log_pos hw)).mp hb.2
  constructor
  · apply (Real.log_le_log_iff (Real.rpow_pos_of_pos htop0 alpha) hlow).mp
    rw [Real.log_rpow htop0,hlog]
    nlinarith
  · apply (Real.log_le_log_iff hupp (Real.rpow_pos_of_pos htop0 beta)).mp
    rw [Real.log_rpow htop0,hlog]
    nlinarith
end NumberTheoryLean.IsolatedRealPrimeRange


end Erdos970

end OAI
