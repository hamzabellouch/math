import OAI.Geometry.NodalSets.Elliptic.CoordinateTransverseDisk

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set MeasureTheory
open scoped ENNReal
noncomputable section

def transverseCylinder (r : ℝ) : Set Coord :=
  {z | z 0 ∈ Icc (-1:ℝ) 1 ∧ Fin.tail z ∈ transverseDisk r}

lemma transverseCylinder_box_subset {r : ℝ} (hr : 0 ≤ r) :
    Icc (Fin.cons (-1:ℝ) (fun _ : Fin 3 ↦ -r/2))
      (Fin.cons (1:ℝ) (fun _ : Fin 3 ↦ r/2)) ⊆ transverseCylinder r := by
  intro z hz
  refine ⟨⟨by simpa using hz.1 0,by simpa using hz.2 0⟩,?_⟩
  have hz' (k : Fin 3) : -(r/2) ≤ z k.succ ∧ z k.succ ≤ r/2 := by
    constructor
    · simpa only [Fin.cons_succ,neg_div] using hz.1 k.succ
    · simpa using hz.2 k.succ
  change Real.sqrt (∑ k : Fin 3, (z k.succ)^2) ≤ r
  apply (Real.sqrt_le_left hr).mpr
  calc
    _ ≤ ∑ _ : Fin 3, (r/2)^2 := Finset.sum_le_sum (fun k _ ↦
      sq_le_sq' (hz' k).1 (hz' k).2)
    _ ≤ r^2 := by norm_num; nlinarith [sq_nonneg r]

lemma transverseCylinder_measure_lower {r : ℝ} (hr : 0 ≤ r) :
    ENNReal.ofReal (2*r^3) ≤ Measure.hausdorffMeasure (4:ℝ) (transverseCylinder r) := by
  have he : (Measure.hausdorffMeasure (4:ℝ) : Measure Coord) = volume := by
    simpa using (hausdorffMeasure_pi_real (ι := Fin 4))
  rw [he]
  have hvol : volume (Icc (Fin.cons (-1:ℝ) (fun _ : Fin 3 ↦ -r/2))
      (Fin.cons (1:ℝ) (fun _ : Fin 3 ↦ r/2)) : Set Coord) = ENNReal.ofReal (2*r^3) := by
    rw [Real.volume_Icc_pi,Fin.prod_univ_succ]
    simp only [Fin.cons_zero,Fin.cons_succ,show (1:ℝ)-(-1) = 2 by ring,
      show r/2- -r/2 = r by ring,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),ENNReal.ofReal_pow hr]
  rw [← hvol]
  exact measure_mono (transverseCylinder_box_subset hr)

end
end Yau.Geometry

end OAI
