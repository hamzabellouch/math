import OAI.Analysis.CircleDomains.Uniformization.JordanExteriorDiskChart
import OAI.Analysis.CircleDomains.Uniformization.RiemannDiskInverse
import OAI.Analysis.CircleDomains.Uniformization.FiniteLiftConformal

namespace OAI

/-! Actual circularization of one Jordan hole. The map is conformal on
its entire exterior and fixes the point at infinity. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_jordan_exterior_circle_map (H : ℂ ≃ₜ ℂ) :
    ∃ F : Sphere → Sphere, F ∞=∞ ∧ IsConformalEquivalence F
      (closedTerminalCap H)ᶜ ((((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) 1)ᶜ) := by
  obtain ⟨hD,hsc,hproper,hzero⟩ := jordan_exterior_plane_data H
  obtain ⟨f,hf,hbij,_⟩ := exists_normalized_riemann_disk_map hD hsc hproper hzero
  let N := pointToInfinity ((H 0 : ℂ) : Sphere)
  let S := (closedTerminalCap H)ᶜ
  have hno : ∞ ∉ N '' S := by
    rintro ⟨p,hp,he⟩
    have hp' : p=((H 0 : ℂ) : Sphere) := N.injective
      (he.trans (pointToInfinity_apply_self _).symm)
    apply hp
    rw [hp']
    refine ⟨H 0,?_,rfl⟩
    rw [closure_jordanInterior]
    exact ⟨0,by simp,rfl⟩
  have hset : N '' S = ((↑) : ℂ → Sphere) '' jordanExteriorPlane H := by
    symm
    apply image_preimage_eq_of_subset
    intro x hx
    cases x using OnePoint.rec with
    | infty => exact (hno hx).elim
    | coe z => exact ⟨z,rfl⟩
  have hN := isConformalEquivalence_pointToInfinity ((H 0 : ℂ) : Sphere) S
  change IsConformalEquivalence N S (N '' S) at hN
  rw [hset] at hN
  have hF := conformalEquivalence_finiteLift hD hf.holomorphic hbij
  have hI := isConformalEquivalence_of_homeomorph CannonMobius.inversion
    (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1)
    (fun p _ => isConformalAt_inversion p) (fun p _ => isConformalAt_inversion p)
  have himage : CannonMobius.inversion '' (((↑) : ℂ → Sphere) '' ball (0 : ℂ) 1) =
      (((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) 1)ᶜ := by
    rw [CannonMobius.inversion.image_eq_preimage_symm]
    exact inversion_preimage_unitDisk
  rw [himage] at hI
  refine ⟨CannonMobius.inversion ∘ extendAtInfinity f ∘ N,?_,hN.trans (hF.trans hI)⟩
  change CannonMobius.inversion (extendAtInfinity f (N ∞))=∞
  have hN0 : N ∞=((0 : ℂ) : Sphere) := CannonMobius.inv_infty
  rw [hN0,extendAtInfinity_coe,hf.at_base]
  exact CannonMobius.inv_zero

end CircleDomainRigidity

end

end OAI
