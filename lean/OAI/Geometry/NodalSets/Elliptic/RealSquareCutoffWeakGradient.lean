import OAI.Geometry.NodalSets.Elliptic.RealBallCubeContainmentLemmas
import OAI.Geometry.NodalSets.Elliptic.RealLocalWeakCutoff

namespace OAI

namespace Yau
open MeasureTheory Set
open scoped ContDiff
noncomputable section

def realSquareCutoff {n : ℕ} (eta u : Coord n → ℝ) : Coord n → ℝ :=
  fun x ↦ eta x^2*u x

def realSquareCutoffGradient {n : ℕ} (eta u : Coord n → ℝ)
    (g : Fin n → Coord n → ℝ) (j : Fin n) : Coord n → ℝ :=
  fun x ↦ eta x^2*g j x+2*eta x*coordPartial eta x j*u x

theorem real_integral_pairing_restrict {n : ℕ} {D : Set (Coord n)}
    (a b : Coord n → ℝ) (hs : tsupport b ⊆ D) :
    (∫ x, a x*b x) = ∫ x in D, a x*b x := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  rw [image_eq_zero_of_notMem_tsupport (fun ht ↦ hx (hs ht)),mul_zero]

theorem real_square_cutoff_weak_gradient {n : ℕ} {D : Set (Coord n)} (hD : IsCompact D)
    (eta u : Coord n → ℝ) (g : Fin n → Coord n → ℝ)
    (hu : MemLp u 2 (volume.restrict D)) (hg : ∀ j, MemLp (g j) 2 (volume.restrict D))
    (he : ContDiff ℝ ∞ eta) (hs : tsupport eta ⊆ D)
    (hw : ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi → tsupport psi ⊆ D →
      (∫ x in D, u x*coordPartial psi x j)=-(∫ x in D, g j x*psi x)) :
    MemLp (realSquareCutoff eta u) 2 volume ∧
    (∀ j, MemLp (realSquareCutoffGradient eta u g j) 2 volume) ∧
    (∀ x, x ∉ tsupport eta → realSquareCutoff eta u x=0) ∧
    (∀ j x, x ∉ tsupport eta → realSquareCutoffGradient eta u g j x=0) ∧
    ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, realSquareCutoff eta u x*coordPartial psi x j)=
        -(∫ x, realSquareCutoffGradient eta u g j x*psi x) := by
  have he2 : ContDiff ℝ ∞ (fun x ↦ eta x^2) := he.pow 2
  have hs2 : tsupport (fun x ↦ eta x^2) ⊆ D := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := eta) (g := eta)).trans hs
  have hd (x : Coord n) (j : Fin n) : coordPartial (fun y ↦ eta y^2) x j =
      2*eta x*coordPartial eta x j := by
    simp only [pow_two,real_coordPartial_mul eta eta he he]
    ring
  have hbase := real_compact_localL2_product hD (fun x ↦ eta x^2) u he2.continuous hs2 hu
  have hh (j : Fin n) := real_local_weak_cutoff hD u (g j) (fun x ↦ eta x^2)
    hu (hg j) he2 hs2 j (hw j)
  simp only [hd] at hh
  refine ⟨hbase,fun j ↦ (hh j).2.1,?_,?_,fun j psi hp hc ↦ ((hh j).2.2 psi hp hc).2.2⟩
  · intro x hx
    simp only [realSquareCutoff,image_eq_zero_of_notMem_tsupport hx,zero_pow (by decide : 2≠0),zero_mul]
  · intro j x hx
    simp only [realSquareCutoffGradient,image_eq_zero_of_notMem_tsupport hx,
      zero_pow (by decide : 2≠0),zero_mul,mul_zero,add_zero]

theorem real_square_cutoff_difference_weak_gradient {n : ℕ}
    (eta u : Coord n → ℝ) (g : Fin n → Coord n → ℝ)
    (hu : MemLp u 2 volume) (hg : ∀ j, MemLp (g j) 2 volume)
    (R r : ℝ) (hr : r ≤ R) (he : ContDiff ℝ ∞ eta)
    (hs : tsupport eta ⊆ realCenteredCube n r)
    (hw : ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      tsupport psi ⊆ realCenteredCube n R →
      (∫ x, u x*coordPartial psi x j)=-(∫ x, g j x*psi x))
    (i : Fin n) (h : ℝ) (hh : |h| ≤ R-r) :
    MemLp (realSquareCutoff eta (realDifferenceQuotient i h u)) 2 volume ∧
    (∀ j, MemLp (realSquareCutoffGradient eta (realDifferenceQuotient i h u)
      (fun l ↦ realDifferenceQuotient i h (g l)) j) 2 volume) ∧
    (∀ x, x ∉ tsupport eta → realSquareCutoff eta (realDifferenceQuotient i h u) x=0) ∧
    (∀ j x, x ∉ tsupport eta → realSquareCutoffGradient eta (realDifferenceQuotient i h u)
      (fun l ↦ realDifferenceQuotient i h (g l)) j x=0) ∧
    ∀ j, ∀ psi : Coord n → ℝ, ContDiff ℝ ∞ psi → HasCompactSupport psi →
      (∫ x, realSquareCutoff eta (realDifferenceQuotient i h u) x*coordPartial psi x j)=
        -(∫ x, realSquareCutoffGradient eta (realDifferenceQuotient i h u)
          (fun l ↦ realDifferenceQuotient i h (g l)) j x*psi x) := by
  apply real_square_cutoff_weak_gradient (realCenteredCube_isCompact n r) eta
    (realDifferenceQuotient i h u) (fun j ↦ realDifferenceQuotient i h (g j))
    ((realDifferenceQuotient_memLp i h u hu).restrict _)
    (fun j ↦ (realDifferenceQuotient_memLp i h (g j) (hg j)).restrict _) he hs
  intro j psi hp hc hpsi
  have ht := real_local_difference_weak_derivative u (g j) hu (hg j) R r hr j (hw j)
    i h hh psi hp hc hpsi
  rw [real_integral_pairing_restrict (realDifferenceQuotient i h u) (fun x ↦ coordPartial psi x j)
    ((tsupport_fderiv_apply_subset ℝ (Pi.single j 1)).trans hpsi),
    real_integral_pairing_restrict (realDifferenceQuotient i h (g j)) psi hpsi] at ht
  exact ht

end
end Yau

end OAI
