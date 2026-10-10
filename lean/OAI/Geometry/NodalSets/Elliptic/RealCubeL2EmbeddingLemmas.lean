import OAI.Geometry.NodalSets.Elliptic.RealFinCubeFubini

namespace OAI

noncomputable section

namespace Yau.Geometry

open Yau.Analysis MeasureTheory Set Function Metric
open scoped ContDiff

lemma realFinCube_four_eq_closedBall : realFinCube 4 = closedBall (0 : Yau.Jets.Coord) 1 := by
  rw [closedBall_pi _ (by norm_num : (0:ℝ) ≤ 1)]
  simp [realFinCube,Real.closedBall_eq_Icc]

theorem realFinCube_integral_four (F : Yau.Jets.Coord → ℝ) (hF : Continuous F) :
    (∫ z in realFinCube 4, F z) =
      ∫ a in Icc (-1:ℝ) 1, ∫ b in Icc (-1:ℝ) 1,
        ∫ c in Icc (-1:ℝ) 1, ∫ d in Icc (-1:ℝ) 1, F ![a,b,c,d] := by
  rw [realFinCube_integral_succ 3 F hF]
  apply integral_congr_ae
  filter_upwards [] with a
  have ha : Continuous (fun z : Fin 3 → ℝ ↦ F (Fin.cons a z)) :=
    hF.comp (continuous_const.finCons continuous_id)
  rw [realFinCube_integral_succ 2 _ ha]
  apply integral_congr_ae
  filter_upwards [] with b
  have hb : Continuous (fun z : Fin 2 → ℝ ↦ F (Fin.cons a (Fin.cons b z))) :=
    ha.comp (continuous_const.finCons continuous_id)
  rw [realFinCube_integral_succ 1 _ hb]
  apply integral_congr_ae
  filter_upwards [] with c
  have hc : Continuous (fun z : Fin 1 → ℝ ↦ F (Fin.cons a (Fin.cons b (Fin.cons c z)))) :=
    hb.comp (continuous_const.finCons continuous_id)
  rw [realFinCube_integral_succ 0 _ hc]
  apply integral_congr_ae
  filter_upwards [] with d
  rw [realFinCube_integral_zero]
  rfl

theorem realCubeAverage_all (F : Yau.Jets.Coord → ℝ) (hF : Continuous F)
    (x : Yau.Jets.Coord) :
    realCubeAverage F [0,1,2,3] x = ∫ z in closedBall (0 : Yau.Jets.Coord) 1, F z := by
  rw [← realFinCube_four_eq_closedBall,realFinCube_integral_four F hF]
  simp only [realCubeAverage]
  apply integral_congr_ae
  filter_upwards [] with a
  apply integral_congr_ae
  filter_upwards [] with b
  apply integral_congr_ae
  filter_upwards [] with c
  apply integral_congr_ae
  filter_upwards [] with d
  congr 1
  ext i
  fin_cases i <;> simp

theorem real_cube_l2_embedding (W : Yau.Jets.Coord → ℝ) (hW : ContDiff ℝ ∞ W)
    (ds : List (Fin 4)) (x : Yau.Jets.Coord) (hx : InUnitCube x) :
    (partialJet W ds x)^2 ≤ 256 * (∫ z in closedBall (0 : Yau.Jets.Coord) 1,
      realFiniteJetSquare W (ds.length+4) z) := by
  have h := (partialJet_sq_le_realCubeL2Control W hW [0,1,2,3] ds x hx).trans
    (realCubeL2Control_le_average W hW (ds.length+4) [0,1,2,3] ds (by simp) x)
  rw [realCubeAverage_all _ (realFiniteJetSquare_smooth W hW _).continuous] at h
  norm_num at h ⊢
  exact h

open MeasureTheory Set Function

lemma realFinCube_isCompact (n : ℕ) : IsCompact (realFinCube n) :=
  isCompact_univ_pi (fun _ ↦ isCompact_Icc)

lemma realFinCube_mass (n : ℕ) :
    (volume.restrict (realFinCube n)).real univ = (2:ℝ)^n := by
  rw [realFinCube_volume,Measure.real,Measure.pi_univ]
  norm_num

lemma real_interval_cube_integral_continuous (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    Continuous (fun t ↦ ∫ z in realFinCube n, F (t,z)) := by
  apply continuous_parametric_integral_of_continuous _ (realFinCube_isCompact n)
  exact hF

lemma real_cube_interval_integral_continuous (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    Continuous (fun z ↦ ∫ t in Icc (-1:ℝ) 1, F (t,z)) := by
  apply continuous_parametric_integral_of_continuous _ isCompact_Icc
  exact hF.comp continuous_swap

lemma real_interval_cube_integral_swap (n : ℕ)
    (F : ℝ × (Fin n → ℝ) → ℝ) (hF : Continuous F) :
    (∫ t in Icc (-1:ℝ) 1, ∫ z in realFinCube n, F (t,z)) =
      ∫ z in realFinCube n, ∫ t in Icc (-1:ℝ) 1, F (t,z) := by
  apply integral_integral_swap
  rw [Measure.prod_restrict]
  exact hF.continuousOn.integrableOn_compact (isCompact_Icc.prod (realFinCube_isCompact n))

end Yau.Geometry

end

end OAI
