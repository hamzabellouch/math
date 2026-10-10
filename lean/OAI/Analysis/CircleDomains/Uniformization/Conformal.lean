import OAI.Analysis.CircleDomains.LengthArea

namespace OAI

/-!
# Sphere conformality and circle-domain statements

The concrete Riemann-sphere charts define conformal equivalences,
round disks, and conformal removability. The two circle-domain statements
express unrestricted uniformization and rigidity under removability.
-/

noncomputable section

open Set
open scoped OnePoint

namespace CircleDomainRigidity

/-- Sphere inversion exchanges zero and infinity and is its own inverse. -/
theorem sphereInv_involutive : Function.Involutive sphereInv := by
  intro p
  cases p using OnePoint.rec with
  | infty => simp [sphereInv]
  | coe z =>
    by_cases hz : z = 0
    · subst z
      simp [sphereInv]
    · simp [sphereInv, hz, inv_ne_zero hz]

@[simp] theorem sphereInv_sphereInv (p : Sphere) : sphereInv (sphereInv p) = p :=
  sphereInv_involutive p

/-- The concrete chart and inverse chart are inverse at all finite chart values. -/
theorem chart_chartSymm (p : Sphere) (z : ℂ) :
    chart p (chartSymm p z) = z := by
  by_cases hp : p = ∞
  · simp [chart, chartSymm, hp, finiteCoord]
  · simp [chart, chartSymm, hp, finiteCoord]

/-- The identity is conformal in both finite and infinite charts. -/
theorem isConformalAt_id (p : Sphere) : IsConformalAt id p := by
  refine ⟨continuousAt_id, 1, one_ne_zero, ?_⟩
  convert hasDerivAt_id (chart p p) using 1
  funext z
  exact chart_chartSymm p z

/-- Reflexivity of the concrete conformal-equivalence predicate. -/
theorem isConformalEquivalence_id (U : Set Sphere) :
    IsConformalEquivalence id U U := by
  refine ⟨fun p _ => isConformalAt_id p, fun _ h => h, id,
    fun p _ => isConformalAt_id p, fun _ h => h, ?_, ?_⟩
  · intro z _
    rfl
  · intro z _
    rfl

/-- Paper 047-02, Introduction, `thm:main`: unrestricted Koebe uniformization. -/
def KoebeCircleDomainConjecture : Prop :=
  ∀ U : Set Sphere, IsOpen U → IsConnected U →
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f U V

/-- Paper 047-01, Introduction, `thm:main`: removability implies rigidity. -/
def CircleDomainRemovabilityRigidity : Prop :=
  ∀ (U V : Set Sphere) (f : Sphere → Sphere),
    IsCircleDomain U → IsCircleDomain V →
    IsConformallyRemovable (frontier U) → IsConformalEquivalence f U V →
    ∃ M : Mobius, ∀ p ∈ U, f p = M • p

/-- The whole-sphere case of Koebe uniformization. -/
theorem circleDomainModel_univ :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f univ V :=
  ⟨univ, id, isCircleDomain_univ, isConformalEquivalence_id univ⟩

/-- An already circular domain is its own conformal model. -/
theorem circleDomainModel_of_circleDomain {U : Set Sphere} (hU : IsCircleDomain U) :
    ∃ (V : Set Sphere) (f : Sphere → Sphere),
      IsCircleDomain V ∧ IsConformalEquivalence f U V :=
  ⟨U, id, hU, isConformalEquivalence_id U⟩

end CircleDomainRigidity

end

end OAI
