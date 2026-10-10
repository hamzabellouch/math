import OAI.Geometry.NodalSets.Elliptic.RealCubeL2EmbeddingLemmas
import OAI.Geometry.NodalSets.Elliptic.RealMeanSquareDecomposition

namespace OAI

namespace Yau.Geometry
open MeasureTheory Set Function
noncomputable section

theorem real_interval_cube_variance_le (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n,
      (F (t,z)-(∫ s in Icc (-1:ℝ) 1, ∫ y in realFinCube n, F (s,y))/(2*2^n))^2) ≤
    (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n,
      (F (t,z)-(∫ y in realFinCube n, F (t,y))/2^n)^2) +
    (∫ z in realFinCube n, ∫ t in Icc (-1:ℝ) 1,
      (F (t,z)-(∫ s in Icc (-1:ℝ) 1, F (s,z))/2)^2) := by
  let m : ℝ := 2^n
  have hm : 0 < m := pow_pos (by norm_num) n
  let : IsFiniteMeasure (volume.restrict (realFinCube n)) :=
    isFiniteMeasure_restrict.mpr (realFinCube_isCompact n).measure_ne_top
  let R : ℝ → ℝ := fun t ↦ (∫ z in realFinCube n, F (t,z))/m
  let C : (Fin n → ℝ) → ℝ := fun z ↦ (∫ t in Icc (-1:ℝ) 1, F (t,z))/2
  let M : ℝ := (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, F (t,z))/(2*m)
  have hR : Continuous R := (real_interval_cube_integral_continuous n F hF).div_const m
  have hC : Continuous C := (real_cube_interval_integral_continuous n F hF).div_const 2
  have hmean : (∫ z in realFinCube n, C z)/m = M := by
    dsimp [C,M]
    rw [integral_div,← real_interval_cube_integral_swap n F hF]
    ring
  have hFC : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-C p.2)^2) :=
    (hF.sub (hC.comp continuous_snd)).pow 2
  have hFR : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-R p.1)^2) :=
    (hF.sub (hR.comp continuous_fst)).pow 2
  have hFM : Continuous (fun p : ℝ × (Fin n → ℝ) ↦ (F p-M)^2) :=
    (hF.sub continuous_const).pow 2
  have hpt (t : ℝ) : m*(R t-M)^2 ≤ ∫ z in realFinCube n, (F (t,z)-C z)^2 := by
    have hc : Continuous (fun z ↦ F (t,z)-C z) :=
      (hF.comp (continuous_const.prodMk continuous_id)).sub hC
    have h := real_mean_square_contraction (volume.restrict (realFinCube n))
      (by rw [realFinCube_mass]; exact hm) _
      (realFinCube_integrable n _ hc) (realFinCube_integrable n _ (hc.pow 2))
    have hi : IntegrableOn (fun z ↦ F (t,z)) (realFinCube n) :=
      realFinCube_integrable n _ (hF.comp (continuous_const.prodMk continuous_id))
    rw [realFinCube_mass,integral_sub hi
      (realFinCube_integrable n _ hC),sub_div,hmean] at h
    exact h
  have hbound := setIntegral_mono_on (μ := volume) (s := Icc (-1:ℝ) 1)
    (((continuous_const : Continuous (fun _ : ℝ ↦ m)).mul
      ((hR.sub (continuous_const : Continuous (fun _ : ℝ ↦ M))).pow 2)).continuousOn.integrableOn_Icc)
    ((real_interval_cube_integral_continuous n _ hFC).continuousOn.integrableOn_Icc)
    measurableSet_Icc (fun t _ ↦ hpt t)
  have hdecomp (t : ℝ) : (∫ z in realFinCube n, (F (t,z)-M)^2) =
      (∫ z in realFinCube n, (F (t,z)-R t)^2)+m*(R t-M)^2 := by
    have hc : Continuous (fun z : Fin n → ℝ ↦ F (t,z)) :=
      hF.comp (continuous_const.prodMk continuous_id)
    have h := real_mean_square_decomposition (volume.restrict (realFinCube n))
      (by rw [realFinCube_mass]; exact hm) _
      (realFinCube_integrable n _ hc) (realFinCube_integrable n _ (hc.pow 2)) M
    simpa only [realFinCube_mass] using h
  change (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, (F (t,z)-M)^2) ≤
    (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, (F (t,z)-R t)^2)+
      (∫ z in realFinCube n, ∫ t in Icc (-1:ℝ) 1, (F (t,z)-C z)^2)
  simp_rw [hdecomp]
  have hiR : IntegrableOn (fun t ↦ ∫ z in realFinCube n, (F (t,z)-R t)^2)
      (Icc (-1:ℝ) 1) :=
    (real_interval_cube_integral_continuous n _ hFR).continuousOn.integrableOn_Icc
  have hiM : IntegrableOn (fun t ↦ m*(R t-M)^2) (Icc (-1:ℝ) 1) :=
    (continuous_const.mul ((hR.sub continuous_const).pow 2)).continuousOn.integrableOn_Icc
  rw [integral_add hiR hiM]
  exact add_le_add le_rfl (hbound.trans_eq (real_interval_cube_integral_swap n _ hFC))

end
end Yau.Geometry

end OAI
