import OAI.Geometry.NodalSets.Elliptic.RealCubeVarianceTensorization
import OAI.Geometry.NodalSets.Elliptic.RealFinCubeSlices
import OAI.Geometry.NodalSets.Elliptic.RealIntervalPoincare

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function
open scoped ContDiff
noncomputable section

theorem real_finCube_poincare (n : ℕ) (W : (Fin n → ℝ) → ℝ)
    (hW : ContDiff ℝ ∞ W) :
    (∫ x in realFinCube n, (W x-(∫ y in realFinCube n, W y)/2^n)^2) ≤
      4*(∫ x in realFinCube n, ∑ i, (Yau.coordPartial W x i)^2) := by
  induction n with
  | zero => simp [realFinCube_integral_zero]
  | succ n ih =>
    let F : ℝ × (Fin n → ℝ) → ℝ := fun p ↦ W (Fin.cons p.1 p.2)
    have hF : Continuous F := hW.continuous.comp (real_finCons_smooth n).continuous
    let R : ℝ → ℝ := fun t ↦ (∫ z in realFinCube n, F (t,z))/2^n
    let C : (Fin n → ℝ) → ℝ := fun z ↦ (∫ t in Icc (-1:ℝ) 1, F (t,z))/2
    have hR : Continuous R := (real_interval_cube_integral_continuous n F hF).div_const _
    have hC : Continuous C := (real_cube_interval_integral_continuous n F hF).div_const _
    have hVR : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-R p.1)^2) :=
      (hF.sub (hR.comp continuous_fst)).pow 2
    have hVC : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-C p.2)^2) :=
      (hF.sub (hC.comp continuous_snd)).pow 2
    let E0 : ℝ × (Fin n → ℝ) → ℝ := fun p ↦ (Yau.coordPartial W (Fin.cons p.1 p.2) 0)^2
    let ET : ℝ × (Fin n → ℝ) → ℝ := fun p ↦ ∑ i : Fin n,
      (Yau.coordPartial W (Fin.cons p.1 p.2) i.succ)^2
    have hE0 : Continuous E0 :=
      ((Yau.real_coordPartial_smooth W hW 0).continuous.comp (real_finCons_smooth n).continuous).pow 2
    have hET : Continuous ET := continuous_finsetSum _ (fun i _ ↦
      ((Yau.real_coordPartial_smooth W hW i.succ).continuous.comp (real_finCons_smooth n).continuous).pow 2)
    have htail (t : ℝ) : (∫ z in realFinCube n, (F (t,z)-R t)^2) ≤
        4*(∫ z in realFinCube n, ET (t,z)) := by
      have h := ih (fun z ↦ W (Fin.cons t z)) (real_finCube_slice_smooth n W hW t)
      simpa only [real_finCube_slice_partial n W hW] using h
    have hhead (z : Fin n → ℝ) : (∫ t in Icc (-1:ℝ) 1, (F (t,z)-C z)^2) ≤
        4*(∫ t in Icc (-1:ℝ) 1, E0 (t,z)) := by
      have h := real_interval_poincare (fun t ↦ W (Fin.cons t z))
        (real_finCube_line_smooth n W hW z) (by norm_num : (-1:ℝ)<1)
      simp only [real_finCube_line_deriv n W hW] at h
      norm_num at h
      exact h
    have ht := setIntegral_mono_on (μ := volume) (s := Icc (-1:ℝ) 1)
      ((real_interval_cube_integral_continuous n _ hVR).continuousOn.integrableOn_Icc)
      (((real_interval_cube_integral_continuous n ET hET).const_mul 4).continuousOn.integrableOn_Icc)
      measurableSet_Icc (fun t _ ↦ htail t)
    have hh := setIntegral_mono_on (μ := volume)
      (realFinCube_integrable n _ (real_cube_interval_integral_continuous n _ hVC))
      (realFinCube_integrable n _ ((real_cube_interval_integral_continuous n E0 hE0).const_mul 4))
      (realFinCube_isCompact n).measurableSet (fun z _ ↦ hhead z)
    rw [integral_const_mul] at ht hh
    have hvar := (real_interval_cube_variance_le n F hF).trans (add_le_add ht hh)
    rw [← real_interval_cube_integral_swap n E0 hE0] at hvar
    have he (t : ℝ) : (∫ z in realFinCube n, ∑ i : Fin (n+1),
        (Yau.coordPartial W (Fin.cons t z) i)^2) =
        (∫ z in realFinCube n, E0 (t,z))+(∫ z in realFinCube n, ET (t,z)) := by
      simp_rw [Fin.sum_univ_succ]
      exact integral_add
        (realFinCube_integrable n _ (hE0.comp (continuous_const.prodMk continuous_id)))
        (realFinCube_integrable n _ (hET.comp (continuous_const.prodMk continuous_id)))
    have hWC : Continuous (fun x ↦ (W x-(∫ y in realFinCube (n+1), W y)/2^(n+1))^2) :=
      (hW.continuous.sub continuous_const).pow 2
    have hWE : Continuous (fun x ↦ ∑ i, (Yau.coordPartial W x i)^2) :=
      continuous_finsetSum _ (fun i _ ↦ (Yau.real_coordPartial_smooth W hW i).continuous.pow 2)
    rw [realFinCube_integral_succ n _ hWC,
      realFinCube_integral_succ n W hW.continuous,
      realFinCube_integral_succ n _ hWE]
    simp_rw [he]
    rw [integral_add
      ((real_interval_cube_integral_continuous n E0 hE0).continuousOn.integrableOn_Icc)
      ((real_interval_cube_integral_continuous n ET hET).continuousOn.integrableOn_Icc)]
    rw [show (2:ℝ)^(n+1)=2*2^n by rw [pow_succ]; ring]
    calc
      _ ≤ 4*(∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, ET (t,z))+
          4*(∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, E0 (t,z)) := hvar
      _ = _ := by ring

theorem real_cube_poincare (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W) :
    (∫ x in realFinCube 4, (W x-(∫ y in realFinCube 4, W y)/16)^2) ≤
      16*(∫ x in realFinCube 4, ∑ i, (Yau.coordPartial W x i)^2) := by
  have h := real_finCube_poincare 4 W hW
  norm_num at h
  exact h.trans (mul_le_mul_of_nonneg_right (by norm_num)
    (integral_nonneg (fun x ↦ Finset.sum_nonneg (fun i _ ↦ sq_nonneg _))))

end
end Yau.Geometry

end OAI
