import OAI.NumberTheory.DukePrimeDegree.Geometry.HorosphereCoordinates

namespace OAI

/-!
# A horospherical element with no peripheral entries is a root element
-/

noncomputable section
open Matrix

namespace DukePrimeDegree
open PrimeDegreePackets

theorem rootHorosphere_eq_transvection_of_peripheral_zero
    {n : ℕ} {i j : Fin n} (hij : i ≠ j)
    (g : G n) (hg : RootHorosphereShape i j g)
    (hrow : ∀ k, k ≠ i → k ≠ j → g.val i k = 0)
    (hcol : ∀ k, k ≠ i → k ≠ j → g.val k j = 0) :
    g = Matrix.SpecialLinearGroup.transvection hij (g.val i j) := by
  apply Subtype.ext
  ext r s
  by_cases hrs : r = s
  · subst s
    have hd := hg r r (Or.inr rfl)
    by_cases hri : r = i
    · subst r
      simpa [Matrix.SpecialLinearGroup.transvection_coe, hij.symm] using hd
    · simpa [Matrix.SpecialLinearGroup.transvection_coe, Matrix.single_apply, Ne.symm hri] using hd
  by_cases hri : r = i
  · subst r
    by_cases hsj : s = j
    · subst s
      simp [Matrix.SpecialLinearGroup.transvection_coe, hij]
    · have hz := hrow s (Ne.symm hrs) hsj
      simp [Matrix.SpecialLinearGroup.transvection_coe, hrs, Ne.symm hsj, hz]
  · by_cases hsj : s = j
    · subst s
      have hz := hcol r hri hrs
      simp [Matrix.SpecialLinearGroup.transvection_coe, hrs, Ne.symm hri, hz]
    · have hz : g.val r s = 0 := by
        simpa only [Matrix.one_apply, hrs, ite_false] using hg r s (Or.inl ⟨hri, hsj⟩)
      simp [Matrix.SpecialLinearGroup.transvection_coe, hrs, Ne.symm hri, hz]

end DukePrimeDegree

end

end OAI
