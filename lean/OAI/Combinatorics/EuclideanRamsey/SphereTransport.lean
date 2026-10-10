import OAI.Combinatorics.EuclideanRamsey.Congruence
import Mathlib.Geometry.Euclidean.Sphere.Basic

namespace OAI

noncomputable section

namespace EuclideanRamsey

/-- A full-affine-span representative transfers its sphere to any congruent
configuration. The translated linear isometry preserves the radius exactly;
in particular, there is no rescaling of the pairwise distances. No injectivity
or positive-dimension hypothesis is needed for this transport lemma. -/
theorem cospherical_transport {s D d : ℕ}
    (a : Fin s → Space D) (b : Fin s → Space d)
    (hspan : affineSpan ℝ (Set.range b) = ⊤)
    (hab : Congruent a b)
    (hb : EuclideanGeometry.Cospherical (Set.range b)) :
    EuclideanGeometry.Cospherical (Set.range a) := by
  by_cases hs : s = 0
  · subst s
    refine ⟨0, 0, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact Fin.elim0 i
  · have hspos : 0 < s := Nat.pos_of_ne_zero hs
    have hba : Congruent b a := fun i j => (hab i j).symm
    obtain ⟨Q, t, hQ⟩ :=
      congruent_linearIsometry b a ⟨0, hspos⟩ hspan hba
    obtain ⟨center, radius, hcenter⟩ := hb
    refine ⟨t + Q center, radius, ?_⟩
    rintro _ ⟨i, rfl⟩
    calc
      dist (a i) (t + Q center) =
          dist (t + Q (b i)) (t + Q center) := by rw [hQ i]
      _ = dist (Q (b i)) (Q center) := by
        simp only [dist_eq_norm]
        congr 1
        abel
      _ = dist (b i) center := Q.dist_map _ _
      _ = radius := hcenter (b i) (Set.mem_range_self i)

end EuclideanRamsey

end

end OAI
