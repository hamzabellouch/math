import OAI.Analysis.CircleDomains.Uniformization.JordanExteriorDiskMap
import OAI.Analysis.CircleDomains.Modulus.PrincipalNormalization
import OAI.Analysis.CircleDomains.Topology.BoundedRoundDisks

namespace OAI

/-! Principal affine normalization of the actual one-hole circularization.
The new hole has an actual positive radius and finite Euclidean center. -/
open Set Function Metric
open scoped Topology OnePoint
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer

lemma exists_principal_jordan_circle_map (H : ℂ ≃ₜ ℂ) :
    ∃ (F : Sphere → Sphere) (c : ℂ) (r : ℝ), 0<r ∧ IsPrincipalNormalized F ∧
      IsConformalEquivalence F (closedTerminalCap H)ᶜ
        ((((↑) : ℂ → Sphere) '' closedBall c r)ᶜ) := by
  obtain ⟨f,hfix,hf⟩ := exists_jordan_exterior_circle_map H
  have hU : IsOpen (closedTerminalCap H)ᶜ :=
    (isCompact_closedTerminalCap H).isClosed.isOpen_compl
  have hi : ∞ ∈ (closedTerminalCap H)ᶜ := by
    rintro ⟨z,_hz,he⟩
    exact OnePoint.coe_ne_infty z he
  obtain ⟨a,b,ha,hnorm⟩ := principal_normalize_at_infty hU hf.1 hf.bijOn.injOn hi hfix
  let A := affineSphere a b ha
  let D := ((↑) : ℂ → Sphere) '' closedBall (0 : ℂ) 1
  have hD : IsRoundClosedDisk D := isRoundClosedDisk_coe_closedBall 0 zero_lt_one
  have hAD : IsRoundClosedDisk (A '' D) := by
    have he : (A : Sphere → Sphere) = fun p => affineMobius a b ha • p :=
      funext (affineSphere_eq_smul a b ha)
    rw [he]
    exact isRoundClosedDisk_image_mobius hD _
  have hno : ∞ ∉ A '' D := by
    rintro ⟨p,hp,he⟩
    have hpinf : p=∞ := A.injective he
    subst p
    obtain ⟨z,_hz,hz⟩ := hp
    exact OnePoint.coe_ne_infty z hz
  obtain ⟨c,r,hr,he⟩ := isRoundClosedDisk_eq_euclidean hAD hno
  have hA := isConformalEquivalence_of_homeomorph A Dᶜ
    (fun p _ => isConformalAt_affineSphere a b ha p)
    (fun p _ => isConformalAt_affineSphere_symm a b ha p)
  have htarget : A '' Dᶜ = (((↑) : ℂ → Sphere) '' closedBall c r)ᶜ := by
    rw [A.image_compl,he]
  rw [htarget] at hA
  exact ⟨A ∘ f,c,r,hr,hnorm,hf.trans hA⟩

end CircleDomainRigidity

end

end OAI
