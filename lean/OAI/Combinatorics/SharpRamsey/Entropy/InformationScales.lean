import Mathlib
import OAI.Combinatorics.SharpRamsey.Parameters.ExposureScales

namespace OAI

section
namespace SharpLogRamsey.SourceScales
open Real Filter
open scoped Topology
noncomputable section

theorem eventually_information_bad_small (η C c ε : ℝ)
    (hη : 0<η) (hC : 0≤C) (hc : 0<c) (hε : 0<ε) :
    ∀ᶠ σ : ℝ in atTop, ∀ q D N budget k : ℝ,
      0<q → 0<D → 0≤N → budget≤C*N*D*σ^(-beta η) →
      c*q*D*σ^(3000*beta η)≤k →
      let a:=σ^(-2000*beta η)/q
      budget/(D*σ^beta η)+2*budget/(k*a)≤N*ε := by
  filter_upwards [eventually_integer_bad_small η C c ε hη hC hc hε,
    eventually_ge_atTop (0:ℝ)] with σ h hσ
  intro q D N budget k hq hD hN hb hk
  have hh:=h q D N budget 0 (c*q*σ^(1+η/2)) k hq hD hN hb
    (mul_nonneg hC hσ) hk le_rfl
  simpa only [mul_zero,zero_div,add_zero] using hh
end
end SharpLogRamsey.SourceScales

end

end OAI
