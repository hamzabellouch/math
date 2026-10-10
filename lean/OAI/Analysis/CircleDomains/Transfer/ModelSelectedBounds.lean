import OAI.Analysis.CircleDomains.Transfer.ModelSelectedTests
import OAI.Analysis.CircleDomains.Uniformization.ModelUniformBounds

namespace OAI

/-! Uniform bounds on the actual selected priority traces. The selected
horizontal values are values on the model complement, not extra data. -/
open Set Function Filter MeasureTheory
open scoped Topology ENNReal
noncomputable section
namespace CircleDomainRigidity
namespace CompactScalarModel
variable {G : Set Sphere} {m : ℕ} {u : Fin m → EuclideanPlane → ℝ}

 theorem outside_of_projection_outside (M : CompactScalarModel G u)
    {p : Sphere} (hp : M.projection p ∉ G) : p ∉ extendAtInfinity M.function '' G := by
  rintro ⟨q,hq,rfl⟩
  exact hp ((M.projection_inverse q hq).symm ▸ hq)

 theorem finiteCoord_bound_of_projection_outside (M : CompactScalarModel G u)
    (hinf : OnePoint.infty ∈ G) {C : ℝ}
    (hC : ∀ z : ℂ, (z : Sphere) ∉ extendAtInfinity M.function '' G → ‖z‖ ≤ C)
    {p : Sphere} (hp : M.projection p ∉ G) : ‖finiteCoord p‖ ≤ C := by
  have hout := M.outside_of_projection_outside hp
  cases p using OnePoint.rec with
  | infty => exact (hout ⟨OnePoint.infty,hinf,rfl⟩).elim
  | coe z => exact hC z hout

 theorem horizontalSection_trace_bound (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {C : ℝ} (hC : ∀ z : ℂ, (z : Sphere) ∉ extendAtInfinity M.function '' G → ‖z‖ ≤ C)
    {z : ℂ} (hz : (z : Sphere) ∉ G) : ‖M.horizontalSection (z : Sphere)‖ ≤ C := by
  obtain ⟨_,_,hproj⟩ := M.section_target_complement hsard hsch hG hconn hinf hTD hz
  have hh := M.finiteCoord_bound_of_projection_outside hinf hC (by rw [hproj]; exact hz)
  exact (Complex.abs_re_le_norm _).trans hh

 theorem FlattenedSourceSelection.value_bound (M : CompactScalarModel G u)
    {R d : ℝ} {H : ControlledHeight R d}
    {W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    {A L δ ε : ℝ} (S : FlattenedSourceSelection M H W A L δ ε)
    (hinf : OnePoint.infty ∈ G) {C : ℝ}
    (hC : ∀ z : ℂ, (z : Sphere) ∉ extendAtInfinity M.function '' G → ‖z‖ ≤ C) (n : ℕ) :
    ‖S.value n‖ ≤ C := by
  rw [S.value_eq]
  apply (Complex.abs_re_le_norm _).trans
  apply M.finiteCoord_bound_of_projection_outside hinf hC
  rw [S.target_projection]
  exact S.center_outside n

 theorem FlattenedSourceSelection.priority_trace_bound (M : CompactScalarModel G u)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hG : IsOpen G) (hconn : IsConnected G)
    (hinf : OnePoint.infty ∈ G) (hTD : IsTotallyDisconnected Gᶜ)
    {R d : ℝ} {H : ControlledHeight R d}
    {W : ∀ i, DeGiorgi.MemW1pWitness 2 (u i) (physicalPlaneDomain G)}
    {A L δ ε : ℝ} (S : FlattenedSourceSelection M H W A L δ ε)
    {C : ℝ} (hC : ∀ z : ℂ, (z : Sphere) ∉ extendAtInfinity M.function '' G → ‖z‖ ≤ C)
    {z : ℂ} (hz : (z : Sphere) ∉ G) :
    ‖priorityInfiniteValue (fun n => S.cutoff n z) S.value (M.horizontalSection (z : Sphere))‖ ≤ C := by
  exact priorityInfiniteValue_norm_le (fun n => S.cutoff_unit n z)
    (S.value_bound M hinf hC) (M.horizontalSection_trace_bound hsard hsch hG hconn hinf hTD hC hz)

end CompactScalarModel
end CircleDomainRigidity

end

end OAI
