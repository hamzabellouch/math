import OAI.Geometry.NodalSets.Elliptic.RealCubeCellApproximation

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function
open scoped ContDiff
noncomputable section

lemma realCubeCellMean_sub (n : ℕ) (k : Fin 4 → Fin n)
    (W V : Yau.Jets.Coord → ℝ) (hW : Continuous W) (hV : Continuous V) :
    realCubeCellMean (fun x ↦ W x-V x) n k = realCubeCellMean W n k-realCubeCellMean V n k := by
  unfold realCubeCellMean
  rw [integral_sub (hW.continuousOn.integrableOn_compact (realCubeCell_isCompact n k))
    (hV.continuousOn.integrableOn_compact (realCubeCell_isCompact n k)),sub_div]

theorem realCubeCell_square_decomposition {n : ℕ} (hn : 0 < n)
    (W : Yau.Jets.Coord → ℝ) (hW : Continuous W) :
    (∫ x in realFinCube 4, W x^2) =
      (∑ k : Fin 4 → Fin n, ∫ x in realCubeCell n k, (W x-realCubeCellMean W n k)^2)+
      ∑ k : Fin 4 → Fin n, (2/(n:ℝ))^4*(realCubeCellMean W n k)^2 := by
  rw [realCubeCell_integral_sum hn (fun x ↦ W x^2) (realFinCube_integrable 4 _ (hW.pow 2)),← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  have hnR : (0:ℝ)<n := by exact_mod_cast hn
  let : IsFiniteMeasure (volume.restrict (realCubeCell n k)) :=
    isFiniteMeasure_restrict.mpr (realCubeCell_isCompact n k).measure_ne_top
  have h := real_mean_square_decomposition (volume.restrict (realCubeCell n k))
    (by rw [realCubeCell_mass hn]; positivity) W
    (hW.continuousOn.integrableOn_compact (realCubeCell_isCompact n k))
    ((hW.pow 2).continuousOn.integrableOn_compact (realCubeCell_isCompact n k)) 0
  simpa only [sub_zero,realCubeCell_mass hn,realCubeCellMean] using h

theorem realCubeCell_square_bound {n : ℕ} (hn : 0 < n)
    (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W) :
    (∫ x in realFinCube 4, W x^2) ≤
      (4/(n:ℝ)^2)*(∫ x in realFinCube 4, ∑ i, (Yau.coordPartial W x i)^2)+
      ∑ k : Fin 4 → Fin n, (2/(n:ℝ))^4*(realCubeCellMean W n k)^2 := by
  rw [realCubeCell_square_decomposition hn W hW.continuous]
  exact add_le_add (realCubeCell_total_error hn W hW) le_rfl

lemma real_cube_energy_sub (W V : Yau.Jets.Coord → ℝ)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) :
    (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial (fun y ↦ W y-V y) x i)^2) ≤
      2*((∫ x in realFinCube 4, ∑ i, (Yau.coordPartial W x i)^2)+
        (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial V x i)^2)) := by
  have hp (x : Yau.Jets.Coord) (i : Fin 4) :
      Yau.coordPartial (fun y ↦ W y-V y) x i = Yau.coordPartial W x i-Yau.coordPartial V x i := by
    simp only [Yau.coordPartial,fderiv_fun_sub (hW.differentiable (by simp) x)
      (hV.differentiable (by simp) x),_root_.sub_apply]
  have hc (F : Yau.Jets.Coord → ℝ) (hF : ContDiff ℝ ∞ F) :
      Continuous (fun x ↦ ∑ i, (Yau.coordPartial F x i)^2) :=
    continuous_finsetSum _ (fun i _ ↦ (Yau.real_coordPartial_smooth F hF i).continuous.pow 2)
  have hpt (x : Yau.Jets.Coord) : (∑ i, (Yau.coordPartial (fun y ↦ W y-V y) x i)^2) ≤
      2*((∑ i, (Yau.coordPartial W x i)^2)+(∑ i, (Yau.coordPartial V x i)^2)) := by
    simp_rw [hp]
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    nlinarith [sq_nonneg (Yau.coordPartial W x i+Yau.coordPartial V x i)]
  have h := setIntegral_mono_on (μ := volume)
    (realFinCube_integrable 4 _ (hc _ (hW.sub hV)))
    (realFinCube_integrable 4 _ (((hc W hW).add (hc V hV)).const_mul 2))
    (realFinCube_isCompact 4).measurableSet (fun x _ ↦ hpt x)
  simp only [Pi.add_apply] at h
  rw [integral_const_mul,integral_add (realFinCube_integrable 4 _ (hc W hW))
    (realFinCube_integrable 4 _ (hc V hV))] at h
  exact h

theorem realCubeCell_distance_bound {n : ℕ} (hn : 0 < n)
    (W V : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V) :
    (∫ x in realFinCube 4, (W x-V x)^2) ≤
      (8/(n:ℝ)^2)*((∫ x in realFinCube 4, ∑ i, (Yau.coordPartial W x i)^2)+
        (∫ x in realFinCube 4, ∑ i, (Yau.coordPartial V x i)^2))+
      ∑ k : Fin 4 → Fin n, (2/(n:ℝ))^4*(realCubeCellMean W n k-realCubeCellMean V n k)^2 := by
  have h := realCubeCell_square_bound hn (fun x ↦ W x-V x) (hW.sub hV)
  simp_rw [realCubeCellMean_sub n _ W V hW.continuous hV.continuous] at h
  have he := mul_le_mul_of_nonneg_left (real_cube_energy_sub W V hW hV)
    (show 0 ≤ 4/(n:ℝ)^2 by positivity)
  have ht := h.trans (add_le_add he le_rfl)
  rw [← mul_assoc (4/(n:ℝ)^2) 2,show (4/(n:ℝ)^2)*2=8/(n:ℝ)^2 by ring] at ht
  exact ht

end
end Yau.Geometry

end OAI
