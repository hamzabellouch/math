import OAI.Analysis.CircleDomains.Transfer.NonpointModelEnds
import OAI.Analysis.CircleDomains.Sobolev.ModelLocalEnergy

namespace OAI

/-! Actual countable ends, selected target points and a common horizontal
bound for priority interpolation. The enumeration may repeat a harmless
point end when the nonpoint family is finite or empty. -/
open Set Function
open scoped Topology
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem exists_priority_source_data (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    (hB : IsCompact {q : ℂ | (q : Sphere) ∉ G})
    (hne : {q : ℂ | (q : Sphere) ∉ G}.Nonempty) :
    ∃ (b : ℕ → ℂ) (z : ℕ → Sphere) (K : ℝ),
      0 ≤ K ∧ (∀ n, (b n : Sphere) ∉ G) ∧
      (∀ n, M.projection (z n) = (b n : Sphere)) ∧
      (∀ n, ‖(finiteCoord (z n)).re‖ ≤ K) ∧
      (∀ q : ℂ, (q : Sphere) ∉ G → (M.projection ⁻¹' {(q : Sphere)}).Nontrivial →
        ∃ n, b n = q) := by
  obtain ⟨b, hb, hc⟩ := M.exists_enumerated_source_ends hsard hsch hG hconn hinf hTD hne
  let z := fun n => invFun M.projection (b n : Sphere)
  have hz (n : ℕ) : M.projection (z n) = (b n : Sphere) :=
    rightInverse_invFun (M.projection_surjective hsard hsch hG hconn hinf hTD) _
  obtain ⟨K, hK, hbound⟩ := M.projection_bounded_lifts hinf hB
  refine ⟨b, z, K, hK, hb, hz, ?_, hc⟩
  intro n
  apply (show ‖(finiteCoord (z n)).re‖ ≤ ‖finiteCoord (z n)‖ by
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (finiteCoord (z n))).trans
  apply hbound
  rw [hz n]
  exact ⟨b n, hb n, rfl⟩

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
