import OAI.Analysis.CircleDomains.Selection.MixedSequenceRetention
import OAI.Analysis.CircleDomains.Topology.PhysicalCollarCoordinates

namespace OAI

/-! A fixed source circuit keeps exactly the same circle values on the
actual mixed models and hence supplies a fixed real lift for the Stokes
limit. -/

open Set Function Filter MeasureTheory
open scoped Topology
noncomputable section
namespace CircleDomainRigidity.FiniteTransfer

 theorem MixedModelExhaustion.eventually_circuit_values
    {S C : Type*} [LinearOrder C]
    {G : Set Sphere} {π : Sphere → Sphere} {σ : S → Sphere}
    {d : CountableRealCoordinates G π σ}
    {data : C → MaskedCoordinateData G d.source π σ} {retained : ℕ → C}
    {O : ℕ → S → Set Sphere} {ε ρ : ℕ → ℝ}
    (M : MixedModelExhaustion d data retained O ε ρ)
    (H : ℂ ≃ₜ ℂ) (γ : ℝ → ℂ) (hγ : PositiveJordanParametrization H γ)
    (hG : ((↑) : ℂ → Sphere) '' frontier (jordanInterior H) ⊆ G) (c : C) :
    ∀ᶠ n in atTop, ∀ t : ℝ,
      sphereRealFunction ((M.stages n).model.functions (M.coordinateIndex c n))
        ((M.stages n).model.inverse
          ((finiteCoord ((M.stages n).model.forward (γ t : Sphere)) : ℂ) : Sphere)) =
      (data c).physical (Complex.equivRealProdCLM (γ t)) := by
  let K := ((↑) : ℂ → Sphere) '' frontier (jordanInterior H)
  have hK : IsCompact K :=
    (isCompact_closure_jordanInterior H).of_isClosed_subset isClosed_frontier frontier_subset_closure |>.image
      OnePoint.continuous_coe
  filter_upwards [M.eventually_coordinate_values hK hG c,
    M.real.eventually_core_contains hK hG] with n hn hcore
  intro t
  have hgt : (γ t : Sphere) ∈ K := mem_image_of_mem _ (hγ.mem_frontier t)
  have hx : Complex.equivRealProdCLM (γ t) ∈ (M.stages n).core := by
    apply interior_subset ((M.stages n).core_contains ?_)
    change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈
      M.real.cores n
    simpa only [ContinuousLinearEquiv.symm_apply_apply] using hcore hgt
  have hxQ : (γ t : Sphere) ∈ openCompletedRegion (M.stages n).terminals.H := by
    apply (M.stages n).core_model
    exact (coe_mem_sphericalCore _ _).mpr hx
  have hi : OnePoint.infty ∈ openCompletedRegion (M.stages n).terminals.H :=
    (M.stages n).core_model (infty_mem_sphericalCore (M.stages n).core)
  have hfin := finite_image_of_fixes_infty (M.stages n).model.equivalence.bijOn.injOn hi
    (M.stages n).model.principal.1 hxQ
  rw [coe_finiteCoord hfin, (M.stages n).model.equivalence.left_inv _ hxQ]
  apply hn
  change ((Complex.equivRealProdCLM.symm (Complex.equivRealProdCLM (γ t)) : ℂ) : Sphere) ∈ K
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hgt

end CircleDomainRigidity.FiniteTransfer

end

end OAI
