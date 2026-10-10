import OAI.Combinatorics.EuclideanRamsey.TensorSphere
import OAI.Combinatorics.EuclideanRamsey.SphereTransport
import OAI.Combinatorics.EuclideanRamsey.Main

namespace OAI

noncomputable section

namespace EuclideanRamsey

/-- Every injective finite indexed Ramsey configuration is cospherical.
This uses the existing Ramsey predicate, with arbitrary finite colorings and
copies preserving the original pairwise distances. Empty configurations and
singletons are included, and no ambient affine-span assumption is imposed. -/
theorem ramsey_cospherical {s d : ℕ} (a : Fin s → Space d)
    (ha : Function.Injective a) (hR : Ramsey a) :
    EuclideanGeometry.Cospherical (Set.range a) := by
  by_cases hs0 : s = 0
  · subst s
    refine ⟨0, 0, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact Fin.elim0 i
  · by_cases hs1 : s = 1
    · subst s
      refine ⟨a 0, 0, ?_⟩
      rintro _ ⟨i, rfl⟩
      have hi : i = 0 := Subsingleton.elim _ _
      rw [hi, dist_self]
    · have hs2 : 2 ≤ s := by omega
      obtain ⟨D, _hD, b, _hb, hab, hspan⟩ :=
        full_affine_representative a hs2 ha
      have hbR : Ramsey b := (ramsey_congruent_iff hab).mp hR
      have hbCriterion : RealCriterion b :=
        ramsey_realCriterion b (by omega) hspan hbR
      have hbSphere : EuclideanGeometry.Cospherical (Set.range b) :=
        realCriterion_cospherical b (by omega) hbCriterion
      exact cospherical_transport a b hspan hab hbSphere

end EuclideanRamsey

end

end OAI
