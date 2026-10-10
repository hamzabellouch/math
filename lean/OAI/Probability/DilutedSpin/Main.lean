import OAI.Probability.DilutedSpin.ExactVariationalLower
import OAI.Probability.DilutedSpin.ProxyRateIncrement

namespace OAI

section
namespace DilutedSpinGlass
open Filter
open scoped Topology

 
theorem mezard_parisi {p : ℕ} (M : Model p) (hM : Admissible M) :
    Tendsto (pressure M) atTop (𝓝 (variationalValue M)) := by
  have hb := pressure_bounded M hM.interaction_integrable hM.field_integrable
  have hu : limsup (pressure M) atTop ≤ variationalValue M := by
    apply limsup_le_of_le hb.2.isCobounded_le
    filter_upwards [eventually_gt_atTop 0] with N hN
    exact pressure_le_variationalValue_exact M hM hN
  exact tendsto_of_le_liminf_of_limsup_le (variationalValue_le_liminf_pressure M hM) hu hb.1 hb.2
end DilutedSpinGlass

end

end OAI
