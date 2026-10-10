import OAI.Analysis.Laughlin.Asymptotics.Convergence
import OAI.Analysis.Laughlin.ThreeBody.Basic

namespace OAI

namespace Laughlin
open scoped Topology
open Filter

theorem three_body_real (z : ℕ) (hz : z ∈ [2,4,5,6,7,8,9,10,11,12,13,14,15]) :
    (Certificate.e z : ℝ) <
      (3/2 : ℝ)*(3*(z : ℝ)-1)*(-1/2 : ℝ)^z := by
  have hh : (Certificate.e z : ℝ) < (Certificate.limitBound z : ℝ) :=
    Rat.cast_lt.mpr (Certificate.threeBody_certificate z hz)
  simpa [Certificate.limitBound] using hh

theorem eta_real :
    (Certificate.rows.map (fun r => ((r.2.1 : ℝ)/(10^7 : ℝ))^2)).sum =
      (93527408868499/10^14 : ℝ) := by
  norm_num [Certificate.rows]

theorem eventual_scalar_budget (error : ℕ → ℝ)
    (he : Tendsto error atTop (𝓝 0)) :
    ∀ᶠ Q : ℕ in atTop, (1/100 : ℝ) ≤
      1-93527408868499/10^14-deltaFormula Q-10946*(3/10^6)-error Q := by
  have ht : Tendsto (fun Q : ℕ =>
      1-93527408868499/10^14-deltaFormula Q-10946*(3/10^6)-error Q) atTop
        (𝓝 ((1-93527408868499/10^14)-61/4096-10946*(3/10^6)-(0 : ℝ))) :=
    (((tendsto_const_nhds.sub deltaFormula_tendsto).sub tendsto_const_nhds).sub he)
  have hlim : (1/100 : ℝ) <
      (1-93527408868499/10^14)-61/4096-10946*(3/10^6)-0 := by norm_num
  exact (tendsto_order.mp ht).1 _ hlim |>.mono (fun Q hQ => le_of_lt hQ)

end Laughlin

end OAI
