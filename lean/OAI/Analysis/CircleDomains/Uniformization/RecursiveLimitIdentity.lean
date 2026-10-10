import OAI.Analysis.CircleDomains.Uniformization.RecursiveLimitDust
import OAI.Analysis.CircleDomains.Rigidity.MatchedEndsHomeomorph
import OAI.Analysis.CircleDomains.Rigidity.RemovableNormalizedExtension

namespace OAI

/-! The actual normalized recursive limit is the identity when the source
complement is removable. Its sphere extension and orientation are proved
from matched ends; neither is a separate assumption. -/
open Set Function Filter
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
namespace AppendingSequence
variable {G : Set Sphere} {a ε : ℝ}
variable (hsupply : FiniteAppendingSupply G a)
  (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hinf : OnePoint.infty ∈ G)
  (hTD : IsTotallyDisconnected Gᶜ) (ha : 0 < a)
  (hBa : {z : ℂ | (z : Sphere) ∉ G} ⊆ Metric.ball 0 a) (hε : 0 < ε)
  (T : FiniteCompactTests G)
local notation "states" => appendingStates hsupply hsard hsch hG hinf hTD ha hBa hε T

 theorem recursive_limit_eq_id
    (harea : ExteriorCoefficientAreaTheorem) (hconn : IsConnected G)
    (hrem : IsConformallyRemovable Gᶜ)
    (M : ∀ n, CompactScalarCircleModel G (states n).family.test)
    {σ : ℕ → ℕ} (hσ : StrictMono σ) {F : ℂ → ℂ}
    (hnorm : IsPrincipalNormalized (extendAtInfinity F))
    (hF : IsConformalEquivalence (extendAtInfinity F) G (extendAtInfinity F '' G))
    (hlim : TendstoLocallyUniformlyOn (fun n => (M (σ n)).function) F atTop
      {z : ℂ | (z : Sphere) ∈ G}) :
    ∀ z : ℂ, (z : Sphere) ∈ G → F z = z := by
  have htarget := recursive_limit_complement_totallyDisconnected
    hsupply hsard hsch hG hinf hTD ha hBa hε T harea hconn M hσ hF hlim
  obtain ⟨D⟩ := exists_matched_conformal_ends hsard hsch hG hconn hinf hF rfl
  obtain ⟨H,he⟩ := D.exists_homeomorph_extension hG hF hTD htarget
  have hid := removable_normalized_extension_eq_id hG hinf hrem hF.1 hnorm H he
  intro z hz
  have hh : extendAtInfinity F (z : Sphere) = (z : Sphere) := (he _ hz).symm.trans (hid _)
  exact OnePoint.coe_injective hh

end AppendingSequence
end CircleDomainRigidity

end

end OAI
