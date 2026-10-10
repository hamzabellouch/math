import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.ExceptionalCellVolume
import OAI.MathematicalPhysics.ContinuumCoulomb.OneParticle.LocalizedDensityMoment

namespace OAI

/-! Mesh cells near one localized orbital occupy a volume bounded by its
cutoff radius, independently of the surrounding slab's horizontal area. -/

noncomputable section
open MeasureTheory
namespace ContinuumCoulomb

theorem orbital_near_cell_volume {ι : Type*} [Fintype ι]
    (index : ι → Fin 3 → ℤ) (hindex : Function.Injective index)
    {h R : ℝ} (hh : 0 < h) (hR : 0 ≤ R) (u : PlanarPosition)
    (hnear : ∀ i, ‖gaussCellCenter h (index i)-planarCenter u‖ ≤ R) :
    (Fintype.card ι:ℝ)*h^3 ≤ 8*(R+2*h)^3 := by
  let A : ι → Set Position := fun i => positionOpenCube (gaussCellCenter h (index i)) h
  have hb (i : ι) : gaussCellCenter h (index i) ∈ wellCoverBox u R R := by
    apply mem_wellCoverBox.mpr
    have hc (j : Fin 3) := (PiLp.norm_apply_le
      (gaussCellCenter h (index i)-planarCenter u) j).trans (hnear i)
    have h0 : planarCenter u 0 = u 0 := by
      simpa only [planarCenter,ContinuousLinearEquiv.apply_symm_apply] using
        (positionSplitCoordinates_fst_zero (planarCenter u)).symm
    have h1 : planarCenter u 1 = u 1 := by
      simpa only [planarCenter,ContinuousLinearEquiv.apply_symm_apply] using
        (positionSplitCoordinates_fst_one (planarCenter u)).symm
    have h2 : planarCenter u 2 = 0 := by
      simpa only [planarCenter,ContinuousLinearEquiv.apply_symm_apply] using
        (positionSplitCoordinates_snd (planarCenter u)).symm
    exact ⟨by simpa only [PiLp.sub_apply,h0,Real.norm_eq_abs] using hc 0,
      by simpa only [PiLp.sub_apply,h1,Real.norm_eq_abs] using hc 1,
      by simpa only [PiLp.sub_apply,h2,sub_zero,Real.norm_eq_abs] using hc 2⟩
  have hsub : (⋃ i, A i) ⊆ wellCoverBox u (R+2*h) (R+2*h) := by
    intro x hx
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp hx
    exact cube_meets_wellCover_subset hh.le
      (mem_positionCube.mpr (fun _ => by simp; positivity)) (hb i)
      (positionOpenCube_subset _ _ hi)
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
    _ ≤ volume.real (wellCoverBox u (R+2*h) (R+2*h)) :=
      measureReal_mono hsub (wellCoverBox_measure_ne_top _ _ _)
    _ = 8*(R+2*h)^3 := by
      rw [wellCoverBox_volume u (by positivity) (by positivity)]
      ring

end ContinuumCoulomb

end

end OAI
