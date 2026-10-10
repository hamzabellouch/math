import OAI.Geometry.EinsteinFour.CP2NonorthogonalFixed
import OAI.Geometry.EinsteinFour.CP2OddOrthogonality

namespace OAI

/-! Every involution of CP2 preserving its Fubini--Study distance has a
fixed point. The proof uses only the three coordinate lines and the unique
central line of a nonorthogonal orbit. -/

namespace PositiveEinsteinFour

open EinsteinFour

noncomputable section

private theorem cp2_not_everywhere_orthogonal (f : ComplexProjective2 → ComplexProjective2)
    (hinv : Function.Involutive f)
    (hpres : ∀ p q, cp2Overlap (f p) (f q) = cp2Overlap p q)
    (hzero : ∀ p, cp2Overlap p (f p) = 0) : False := by
  let e (i : Fin 3) : CP2Vector := EuclideanSpace.single i 1
  have hen (i : Fin 3) : ‖e i‖ = 1 := by simp [e]
  have he0 (i : Fin 3) : e i ≠ 0 := by
    intro h
    have hn := hen i
    rw [h, norm_zero] at hn
    exact zero_ne_one hn
  let p (i : Fin 3) : ComplexProjective2 := Projectivization.mk ℂ (e i) (he0 i)
  let v (i : Fin 3) := cp2UnitRep (f (p i))
  have hvn (i : Fin 3) : ‖v i‖ = 1 := cp2UnitRep_norm _
  have hcoord (i j : Fin 3) : cp2Overlap (p i) (f (p j)) = ‖v j i‖ := by
    rw [cp2Overlap_of_unit_representatives (p i) (f (p j)) (e i) (v j)
      (he0 i) (cp2UnitRep_ne_zero _) (hen i) (hvn j) rfl (cp2UnitRep_mk _)]
    simp [e, EuclideanSpace.inner_single_left]
  have hdiag (i : Fin 3) : v i i = 0 := by
    apply norm_eq_zero.mp
    rw [← hcoord, hzero]
  have horth (i j : Fin 3) (hij : i ≠ j) : inner ℂ (v i) (v j) = 0 := by
    apply norm_eq_zero.mp
    change cp2Overlap (f (p i)) (f (p j)) = 0
    rw [hpres, cp2Overlap_of_unit_representatives (p i) (p j) (e i) (e j)
      (he0 i) (he0 j) (hen i) (hen j) rfl rfl]
    simp [e, EuclideanSpace.inner_single_left, hij]
  have hsym (i j : Fin 3) : ‖v i j‖ = ‖v j i‖ := by
    rw [← hcoord, ← hcoord]
    calc
      cp2Overlap (p j) (f (p i)) = cp2Overlap (f (p j)) (p i) := by
        simpa only [hinv (p i)] using (hpres (p j) (f (p i))).symm
      _ = cp2Overlap (p i) (f (p j)) := cp2Overlap_comm _ _
  exact cp2_odd_orthogonality_obstruction v hvn horth hdiag hsym

theorem cp2_involutive_overlap_fixed (f : ComplexProjective2 → ComplexProjective2)
    (hinv : Function.Involutive f)
    (hpres : ∀ p q, cp2Overlap (f p) (f q) = cp2Overlap p q) :
    ∃ p, f p = p := by
  by_contra hn
  apply cp2_not_everywhere_orthogonal f hinv hpres
  intro p
  apply le_antisymm _ (cp2Overlap_nonneg _ _)
  by_contra hp
  exact hn (cp2_nonorthogonal_fixed f hinv hpres p (lt_of_not_ge hp))

theorem cp2_involutive_isometry_fixed (f : ComplexProjective2 → ComplexProjective2)
    (hinv : Function.Involutive f)
    (hdist : ∀ p q, fubiniStudyDistance (f p) (f q) = fubiniStudyDistance p q) :
    ∃ p, f p = p := by
  apply cp2_involutive_overlap_fixed f hinv
  intro p q
  exact (cp2Overlap_eq_iff_distance_eq _ _ _ _).mpr (hdist p q)

end
end PositiveEinsteinFour

end OAI
