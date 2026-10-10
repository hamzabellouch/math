import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.WellCover

namespace OAI

/-! Cells meeting the well support have total volume O(m*S), rather than
the volume of the surrounding slab. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ContinuumCoulomb

theorem cube_meets_wellCover_subset {b z : Position} {u : PlanarPosition}
    {h r S : ℝ} (hh : 0 ≤ h) (hz : z ∈ positionCube b h)
    (hzu : z ∈ wellCoverBox u r S) :
    positionCube b h ⊆ wellCoverBox u (r+2*h) (S+2*h) := by
  intro x hx
  have hd := positionCube_diameter_bound hh hx hz
  have hi (i : Fin 3) : |x i-z i| ≤ 2*h := by
    exact (PiLp.norm_apply_le (x-z) i).trans hd
  obtain ⟨hz0,hz1,hz2⟩ := mem_wellCoverBox.mp hzu
  apply mem_wellCoverBox.mpr
  refine ⟨?_,?_,?_⟩
  · linarith [abs_sub_le (x 0) (z 0) (u 0),hi 0]
  · linarith [abs_sub_le (x 1) (z 1) (u 1),hi 1]
  · have he := abs_sub_le (x 2) (z 2) 0
    simp only [sub_zero] at he
    linarith [hi 2]

theorem exceptional_cell_volume_bound {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h S : ℝ} (hh : 0 < h) (hh1 : h ≤ 1) (hS : 1 ≤ S)
    (freq scale : ℝ) {m : ℕ} (u : Fin m → PlanarPosition)
    (hmeet : ∀ i, ∃ z ∈ positionCube (gaussCellCenter h (index i)) h,
      z ∈ tsupport (manufacturedWellField freq scale S u)) :
    (Fintype.card ι:ℝ)*h^3 ≤ 216*m*S := by
  let A : ι → Set Position := fun i => positionOpenCube (gaussCellCenter h (index i)) h
  let B : Fin m → Set Position := fun j => wellCoverBox (u j) (1+2*h) (S+2*h)
  have hsub : (⋃ i, A i) ⊆ ⋃ j, B j := by
    intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    obtain ⟨z,hz,hzs⟩ := hmeet i
    obtain ⟨j,hj⟩ := Set.mem_iUnion.mp
      (manufacturedWellField_support_cover freq scale (by linarith : 0 < S) u hzs)
    exact Set.mem_iUnion.mpr ⟨j,cube_meets_wellCover_subset hh.le hz hj
      (positionOpenCube_subset _ _ hi)⟩
  have hBfinite : volume (⋃ j, B j) ≠ ⊤ := by
    apply ne_of_lt
    apply lt_of_le_of_lt (measure_iUnion_fintype_le volume B)
    exact ENNReal.sum_lt_top.mpr (fun j _ => (wellCoverBox_measure_ne_top (u j) _ _).lt_top)
  have hA : volume.real (⋃ i, A i) = (Fintype.card ι:ℝ)*h^3 := by
    rw [measureReal_iUnion_fintype
      (fun i j hij => grid_openCubes_disjoint hh (fun he => hij (hindex he)))
      (fun i => positionOpenCube_measurable _ _)
      (fun i => by
        rw [measure_congr (positionOpenCube_ae_eq (gaussCellCenter h (index i)) h)]
        exact (positionCube_isCompact _ hh.le).measure_ne_top)]
    simp only [positionOpenCube_volume _ hh.le,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  calc
    _ = volume.real (⋃ i, A i) := hA.symm
    _ ≤ volume.real (⋃ j, B j) := measureReal_mono hsub hBfinite
    _ ≤ 8*m*(1+2*h)^2*(S+2*h) :=
      wellCover_volume_bound u (by positivity) (by linarith)
    _ ≤ 8*m*9*(3*S) := by
      gcongr
      · nlinarith
      · linarith
    _ = _ := by ring

end ContinuumCoulomb

end

end OAI
