import Mathlib

namespace OAI

/-! Circle-domain uniformization and rigidity under conformal removability. -/

noncomputable section
open Set Classical
open scoped OnePoint

namespace CircleDomainRigidity

abbrev Sphere := OnePoint ℂ
abbrev Mobius := Matrix.GeneralLinearGroup (Fin 2) ℂ

def sphereInv (p : Sphere) : Sphere :=
  p.elim (0 : ℂ) (fun z ↦ if z = 0 then ∞ else (z⁻¹ : ℂ))

def finiteCoord (p : Sphere) : ℂ := p.elim 0 id

def chart (p q : Sphere) : ℂ :=
  if p = ∞ then finiteCoord (sphereInv q) else finiteCoord q

def chartSymm (p : Sphere) (z : ℂ) : Sphere :=
  if p = ∞ then sphereInv (z : Sphere) else (z : Sphere)

def IsConformalAt (f : Sphere → Sphere) (p : Sphere) : Prop :=
  ContinuousAt f p ∧ ∃ d : ℂ, d ≠ 0 ∧
    HasDerivAt (fun z ↦ chart (f p) (f (chartSymm p z))) d (chart p p)

def IsConformalOn (f : Sphere → Sphere) (U : Set Sphere) : Prop :=
  ∀ p ∈ U, IsConformalAt f p

def IsConformalEquivalence (f : Sphere → Sphere) (U V : Set Sphere) : Prop :=
  IsConformalOn f U ∧ MapsTo f U V ∧ ∃ g : Sphere → Sphere,
    IsConformalOn g V ∧ MapsTo g V U ∧
    (∀ z ∈ U, g (f z) = z) ∧ (∀ w ∈ V, f (g w) = w)

def IsRoundClosedDisk (K : Set Sphere) : Prop :=
  ∃ M : Mobius,
    K = (fun p : Sphere ↦ M • p) ''
      (((↑) : ℂ → Sphere) '' Metric.closedBall (0 : ℂ) 1)

def IsCircleDomain (U : Set Sphere) : Prop :=
  IsOpen U ∧ IsConnected U ∧
    ∀ p ∈ Uᶜ, (∃ q : Sphere, connectedComponentIn Uᶜ p = {q}) ∨
      IsRoundClosedDisk (connectedComponentIn Uᶜ p)

def OrientationPreserving (h : Sphere ≃ₜ Sphere) : Prop :=
  ContinuousMap.Homotopic (⟨h, h.continuous⟩ : C(Sphere, Sphere)) (ContinuousMap.id Sphere)

def IsConformallyRemovable (E : Set Sphere) : Prop :=
  IsCompact E ∧ ∀ h : Sphere ≃ₜ Sphere, OrientationPreserving h →
    IsConformalOn h Eᶜ → ∃ M : Mobius, ∀ p : Sphere, h p = M • p

end CircleDomainRigidity

open CircleDomainRigidity

namespace Problem047

theorem koebe_circle_domain :
    ∀ U : Set Sphere, IsOpen U → IsConnected U →
      ∃ (V : Set Sphere) (f : Sphere → Sphere),
        IsCircleDomain V ∧ IsConformalEquivalence f U V := by
  sorry

theorem removability_implies_rigidity :
    ∀ (U V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain U → IsCircleDomain V →
      IsConformallyRemovable (frontier U) → IsConformalEquivalence f U V →
      ∃ M : Mobius, ∀ p ∈ U, f p = M • p := by
  sorry

end Problem047

end

end OAI
